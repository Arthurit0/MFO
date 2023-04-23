(* Nenhum outro arquivo deve ser importado.

Nome: Arthur José Budal da Silva*)

Require Import Coq.Arith.PeanoNat.

(* Podemos definir uma representação binária dos números naturais por meio de dois 
construtores que representam 0s e 1s (B0 e B1), e um marcador de final da sequência Z. 

Por exemplo:


        decimal               Binary                          unary
           0                    B0 Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

Note que o bit menos significativo fica a esquerda da sequência.

*)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

(* Complete as definições abaixo, sendo incr uma função que incrementa um número
binário e bin_to_nat a função que converte um binário em natural: *)

Fixpoint incr (n:bin) : bin :=
  match n with
  | Z => B1 Z
  | B0 n' => B1 n'
  | B1 n' => B0 (incr n')
  end.


Fixpoint bin_to_nat (n:bin) : nat :=
  match n with
  | Z => O
  | B0 n' => 2 * (bin_to_nat n')
  | B1 n' => 1 + 2 * (bin_to_nat n')
  end.

(* Declare uma função que converta natural para binário: *)

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.
(* Prove que as tranformações definididas no diagrama abaixo são válidas: 

                           incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

*)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [ | n' IHn'].
  simpl. rewrite <- plus_n_O. reflexivity.
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_1 : forall (n : nat),
  n + 1 = S (n).
Proof.
    intros n. induction n as [| w W].
    simpl. reflexivity.
    simpl. rewrite W. reflexivity.   
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity.  
Qed.

Lemma plus_1_r : forall n : nat,
  S n = n + 1.
Proof.
  intros n. rewrite -> plus_comm. rewrite <- plus_1_l. reflexivity.
  Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n].
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity.
Qed.


Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b. induction b as [|b1 | b2]. 
  simpl. reflexivity.
  simpl. rewrite <- plus_1. rewrite <- plus_n_O. rewrite <- plus_1_r.  reflexivity.
  rewrite <- plus_1. simpl. rewrite <- plus_n_O. rewrite <- plus_n_O.  rewrite -> IHb2.
  simpl. replace (S (bin_to_nat b2)) with (bin_to_nat b2 + 1).
  rewrite -> plus_assoc. reflexivity. rewrite <- plus_1_r. reflexivity.
  Qed.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [ | n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn'. reflexivity.
Qed.

