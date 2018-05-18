(*  Zadanie 6: Przelewanka      *)
(*  autor: Kamil Dubil, 370826  *)
(*  reviewer: Mateusz Masiak    *)

exception Found_answer of int

(* glasses - tablica par (xi, yi), gdzie xi - pojemność i-tej szklanki, *)
(* yi - docelowa ilość wody w i-tej szklance                            *)
(* wynik - minimalna liczba czynności potrzebnych do uzyskania          *)
(* stanu docelowego albo -1, jeśli stan ten nie jest osiągalny          *)
let przelewanka glasses =
    let n = Array.length glasses in
    (* początkowy stan - wszystkie szklanki puste *)
    let state = Array.make n 0 in
    (* stan docelowy *)
    let goal = Array.init n (fun i -> snd glasses.(i)) in
    (* największy wspólny dzielnik *)
    let nwd a b =
        let rec f a b =
            if b = 0 then a else f b (a mod b)
        in
        if a > b then f a b else f b a in
    (* sprawdzenie czy obecny stan jest docelowym *)
    let check t =
        try
        for i = 0 to n - 1 do
            if goal.(i) <> t.(i) then
                failwith "Nope"
        done;
        true
        with Failure _ -> false in
    (* w szczególności jeśli glasses jest pustą tablicą, *)
    (* to check state zwraca true                        *)
    if check state then 0 else
(* świadomie pomijam wcięcie, żeby kod nie był zbyt szeroki *)
    (* jeśli docelowa ilość wody w którejś ze szklanek nie jest podzielna *)
    (* przez nwd pojemności szklanek, to docelowy stan nie jest odiągalny *)
    let check_nwd =
        let nwdd =
            Array.fold_left
                (fun a (x, _) -> nwd a x)
                (fst glasses.(0))
                glasses in
        match nwdd with
        | 0 | 1 -> true
        | _ ->
            try
            Array.iter
                (fun (_, y) -> if y mod nwdd <> 0 then failwith "Nope")
                glasses;
            true
            with Failure _ -> false in
    (* jeśli nie ma takiego i, że xi = yi lub yi = 0, *)
    (* to docelowy stan nie jest osiągalny            *)
    let check_beg =
        try
        Array.iter
            (fun (x, y) -> if x = y || y = 0 then failwith "Yep")
            glasses;
        false
        with Failure _ -> true in
    if not (check_beg && check_nwd) then -1 else (
(* świadomie pomijam wcięcie, żeby kod nie był zbyt szeroki *)
    (* napełnij k-tą szklankę *)
    let fill k t =
        let copy = Array.copy t in
        copy.(k) <- fst glasses.(k);
        copy in
    (* opróżnij k-tą szklankę *)
    let empty k t =
        let copy = Array.copy t in
        copy.(k) <- 0;
        copy in
    (* przelej wodę z k-tej szklanki do l-tej *)
    let pour k l t =
        let copy = Array.copy t in
        let available_volume = fst glasses.(l) - t.(l) in
        if t.(k) <= available_volume then begin
            copy.(k) <- 0;
            copy.(l) <- t.(l) + t.(k);
        end
        else begin
            copy.(l) <- fst glasses.(l);
            copy.(k) <- t.(k) - available_volume
        end;
        copy in
    (* generuje listę stanów po przelaniu wody *)
    (* z k-tej szklanki do każdej innej        *)
    let pour_to_others k t =
        let w = ref [] in
        for i = 0 to n - 1 do
            if i <> k then
                w := (pour k i t)::!w
        done;
        !w in
    (* dodaje do tablicy haszy nowy stan s, kluczem jest stan,         *)
    (* wartością liczba czynności d; jeżeli w tablicy już jest stan s, *)
    (* to zwraca false, jeżeli nie ma - dodaje i zwraca true           *)
    let add_without_replacement tbl s d =
        if Hashtbl.mem tbl s then false
        else begin
            Hashtbl.add tbl s d;
            true;
        end in
    (* ht - tablica z haszowaniem pamiętająca odwiedzone stany *)
    let ht = Hashtbl.create n in
    (* kolejka do algorytmu BFS *)
    let q = Queue.create () in
    Queue.push state q;
    Hashtbl.add ht state 0;
    try
    while not (Queue.is_empty q) do
        let s = Queue.pop q in
        let d = Hashtbl.find ht s in
        let d = d + 1 in
        for i = 0 to n - 1 do
            (* wszystkie stany po napełnieniu jednej szklanki *)
            let s1 = fill i s in
            if check s1 then raise (Found_answer d) else
            if add_without_replacement ht s1 d then
                Queue.push s1 q;
            (* wszystkie stany po opróżnieniu jednej szklanki *)
            let s1 = empty i s in
            if check s1 then raise (Found_answer d) else
            if add_without_replacement ht s1 d then
                Queue.push s1 q;
            (* wszystkie stany po przelaniu wody z jednej szklanki do innych *)
            let s_list = pour_to_others i s in
            List.iter
                (fun x ->
                    if check x then raise (Found_answer d) else
                    if add_without_replacement ht x d then
                        Queue.push x q)
                s_list;
        done;
    done;
    -1;
    with Found_answer d -> d;
    )


(*****************************************************************************)

(* testy *)

(*

assert ( przelewanka [| (4,0); (1,0); (1,1); (1,0); (0,0); (5,4) |] =(2));;
assert ( przelewanka [| (3,1); (2,2); (2,2); (2,0) |] =(3));;
assert ( przelewanka [| (12,2); (6,6); (1,1) |] =(6));;
assert ( przelewanka [| (4,0); (8,6); (4,3) |] =(-1));;
assert ( przelewanka [| (3,1); (2,0); (0,0); (3,3); (1,0); (1,0) |] =(3));;
assert ( przelewanka [| (4,2); (5,4); (2,1) |] =(-1));;
assert ( przelewanka [| (5,3); (8,7); (4,3) |] =(-1));;
assert ( przelewanka [| (1,0); (1,1); (1,1); (2,0); (0,0); (0,0); (0,0); (1,1); (0,0); (1,1) |] =(4));;
assert ( przelewanka [| (10,5); (5,1) |] =(-1));;
assert ( przelewanka [| (2,2); (2,2); (0,0); (2,0); (2,0); (0,0); (2,2) |] =(3));;
assert ( przelewanka [| (4,3); (1,1); (8,8); (1,1) |] =(4));;
assert ( przelewanka [| (7,4); (6,4) |] =(-1));;
assert ( przelewanka [| (10,2); (9,5) |] =(-1));;
assert ( przelewanka [| (11,2); (7,1) |] =(-1));;
assert ( przelewanka [| (1,0); (5,0); (3,0); (3,0) |] =(0));;
assert ( przelewanka [| (10,0); (3,0) |] =(0));;
assert ( przelewanka [| (10,9); (2,0); (4,4) |] =(-1));;
assert ( przelewanka [| (0,0); (0,0); (8,8); (6,6) |] =(2));;
assert ( przelewanka [| (30,27); (15,13) |] =(-1));;
assert ( przelewanka [| (7,0); (14,2); (15,10); (0,0) |] =(19));;
assert ( przelewanka [| (20,9); (26,22) |] =(-1));;
assert ( przelewanka [| (0,0); (4,4); (1,1); (6,4); (6,0); (1,1) |] =(4));;
assert ( przelewanka [| (38,20); (27,13) |] =(-1));;
assert ( przelewanka [| (2,0); (5,3); (4,3); (8,4) |]= (7));;
assert ( przelewanka [| (44,14); (43,30) |]= (-1));;
assert ( przelewanka [| (12,4); (13,13); (1,0); (6,3) |] =(9));;
assert ( przelewanka [| (46,44); (46,43) |] =(-1));;
assert ( przelewanka [| (2,1); (4,2); (0,0); (3,2); (3,1); (4,1); (1,0); (0,0); (0,0) |] =(7));;
assert ( przelewanka [| (32,7); (39,24) |] =(-1));;
assert ( przelewanka [| (5,5); (11,7); (9,2) |] =(8));;
assert ( przelewanka [| (6,4); (8,4); (8,4) |]= (-1));;
assert ( przelewanka [| (39,9); (29,4) |] =(-1));;
assert ( przelewanka [| (13,2); (23,3) |] =(-1));;
assert ( przelewanka [| (71,37) |] =(-1));;
assert ( przelewanka [| (17,2); (3,2); (23,9) |] =(-1));;
assert ( przelewanka [| (9,4); (9,2); (8,7); (0,0) |] = (-1));;
assert ( przelewanka [| (0,0); (5,1); (6,4); (5,1); (0,0); (6,6) |] = (11));;
assert ( przelewanka [| (14,14); (85,61) |] = (60));;
assert ( przelewanka [| (12,7); (4,3); (7,5); (1,1) |] = (7));;
assert ( przelewanka [| (20,1); (30,27) |] = (-1));;
assert ( przelewanka [| (47,45); (37,30) |] = (-1));;
assert ( przelewanka [| (23,14); (16,16) |] = (6));;
assert ( przelewanka [| (62,48); (16,12) |] = (-1));;
assert ( przelewanka [| (5,3); (55,39); (3,1) |] = (-1));;
assert ( przelewanka [| (17,13); (14,1) |] = (-1));;
assert ( przelewanka [| (18,13); (14,3) |] = (-1));;
assert ( przelewanka [| (82,61); (42,19) |] = (-1));;
assert ( przelewanka [| (0,0); (4,0); (6,5); (6,0); (0,0); (4,1) |] = (-1));;
assert ( przelewanka [| (87,70); (33,25) |] = (-1));;
assert ( przelewanka [| (1,0); (0,0); (3,1); (2,0); (3,2); (3,1); (0,0); (5,5); (0,0) |] = (6));;
assert ( przelewanka [| (1,0); (4,2); (4,4); (2,0); (0,0); (2,1); (3,3) |] = (6));;
assert ( przelewanka [| (5,4); (36,10); (29,1) |] = (-1));;
assert ( przelewanka [| (17,14); (66,26) |] = (-1));;
assert ( przelewanka [| (33,17); (94,9); (9,8) |] = (-1));;
assert ( przelewanka [| (335,126); (170,82) |] = (-1));;
assert ( przelewanka [| (11,0); (8,0); (8,7); (15,6); (5,5) |] = (7));;
assert ( przelewanka [| (27,1); (2,0); (22,11); (23,16) |] = (15));;
assert ( przelewanka [| (3,3); (9,4); (0,0); (19,15); (15,5); (1,1) |] = (9));;
assert ( przelewanka [| (152,118); (154,68) |] = (-1));;
assert ( przelewanka [| (310,76); (139,91) |] = (-1));;
assert ( przelewanka [| (48,9); (12,0); (1,1); (65,64) |] = (10));;
assert ( przelewanka [| (7,5); (3,3); (9,4); (10,4); (6,3); (5,3) |] = (8));;
assert ( przelewanka [| (100000,50000); (1,1) |] = (100000));;
assert ( przelewanka [| (0,0); (0,0); (0,0); (300000,151515); (1,0); (0,0) |] = (296971));;
assert ( przelewanka [| (100,0); (100,100); (100,0); (100,100); (100,0); (100,100); (100,0); (100,100); (100,0); (100,0) |] = (4));;
assert ( przelewanka [| (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8); (8,8) |] = (14));;
assert ( przelewanka [| (389,389); (276,214) |] = (626));;
assert ( przelewanka [| (100,0); (100,50); (100,100); (100,50); (100,0); (100,50); (100,100); (50,0) |] = (7));;
assert ( przelewanka [| (500,0); (499,492); (498,0); (497,0); (496,0); (495,0); (494,0); (493,0); (492,0); (491,0); (490,0) |] = (2));;
assert ( przelewanka [| (500,0); (499,3); (498,0); (497,0); (496,0); (495,0); (494,494); (493,0); (492,0); (491,0); (490,0) |] = (3));;
assert ( przelewanka [| (100,0); (100,50); (100,100); (100,50); (100,0); (100,50); (100,100); (100,50) |] = (-1));;
assert ( przelewanka (Array.init 35 (fun i -> (i * i * i * i * i, if i = 25 then 20 * 20 * 20 * 20 * 20 else 0))) = 2);;

*)
