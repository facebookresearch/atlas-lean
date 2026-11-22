/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.HashTableIdempotent

/-!
# Sequential idempotent requests over `HashTable`

Concrete fixtures and checks for one memo step `serve`: a lookup hit returns
the stored response with the table unchanged; a miss runs the handler and
inserts its response. The `serve` operation and its laws live in the public
module `CSLibExt.Algorithms.Lean.DataStructures.HashTableIdempotent`.
D1: only HashTable facts are proved; no other map type appears.
D2: keys use propositional = under DecidableEq, not BEq; hash needs no law.
D3: specifications are plain equations, not program-logic triples.
D4: unchanged means literal table equality; agreement means lookup equality.
No concurrency, crash-recovery, or external-effect behavior is claimed.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.HashTableIdempotentRequestTests

universe u v

open HashTable

private def t1Handler : Nat → String :=
  fun n => if n = 7 then "seven" else "other"

#print axioms t1Handler

private def t1Table : HashTable Nat String id :=
  HashTable.empty id 2 (by decide)

#print axioms t1Table

private theorem t1_miss_lookup :
    HashTable.lookup 7 t1Table = none := by decide

#print axioms t1_miss_lookup

private theorem t1_first_serve :
    (serve t1Handler 7 t1Table).1 = t1Handler 7 := by decide

#print axioms t1_first_serve

private theorem t1_second_serve :
    (serve t1Handler 7 (serve t1Handler 7 t1Table).2).1 =
      t1Handler 7 := by decide

#print axioms t1_second_serve

private theorem t1_stable :
    (serve t1Handler 7 (serve t1Handler 7 t1Table).2).2 =
      (serve t1Handler 7 t1Table).2 :=
  congrArg Prod.snd (serve_serve t1Handler 7 t1Table)

#print axioms t1_stable

private def t2Handler : Nat → String := fun n =>
  if n = 1 then "one"
  else if n = 3 then "three"
  else if n = 5 then "five"
  else if n = 9 then "nine"
  else "other"

#print axioms t2Handler

private def t2Table : HashTable Nat String id :=
  HashTable.empty id 2 (by decide)

#print axioms t2Table

private def t2After1 : String × HashTable Nat String id :=
  serve t2Handler 1 t2Table

#print axioms t2After1

private theorem t2_collision_miss :
    HashTable.lookup 3 t2After1.2 = none := by decide

#print axioms t2_collision_miss

private def t2After13 : String × HashTable Nat String id :=
  serve t2Handler 3 t2After1.2

#print axioms t2After13

private theorem t2_serve3_answers :
    t2After13.1 = t2Handler 3 := by decide

#print axioms t2_serve3_answers

private theorem t2_serve1_hits :
    (serve t2Handler 1 t2After13.2).1 = t2Handler 1 := by decide

#print axioms t2_serve1_hits

private def t2Table1 : HashTable Nat String id :=
  HashTable.empty id 1 (by decide)

#print axioms t2Table1

private def t2One5 : String × HashTable Nat String id :=
  serve t2Handler 5 t2Table1

#print axioms t2One5

private theorem t2_onebucket_miss :
    HashTable.lookup 9 t2One5.2 = none := by decide

#print axioms t2_onebucket_miss

private def t2One59 : String × HashTable Nat String id :=
  serve t2Handler 9 t2One5.2

#print axioms t2One59

private theorem t2_onebucket_hit :
    (serve t2Handler 5 t2One59.2).1 = t2Handler 5 := by decide

#print axioms t2_onebucket_hit

private def t3Table : HashTable Nat String id :=
  HashTable.empty id 2 (by decide)

#print axioms t3Table

private def t3HandlerA : Nat → String := fun _ => "a"

#print axioms t3HandlerA

private def t3HandlerB : Nat → String := fun _ => "b"

#print axioms t3HandlerB

private def t3AfterA : String × HashTable Nat String id :=
  serve t3HandlerA 1 t3Table

#print axioms t3AfterA

private theorem t3_first_answers_a : t3AfterA.1 = "a" := by decide

#print axioms t3_first_answers_a

private theorem t3_second_stale :
    (serve t3HandlerB 1 t3AfterA.2).1 = "a" := by decide

#print axioms t3_second_stale

private def t3PairHash : Nat × String → Nat := fun k => k.1

#print axioms t3PairHash

private def t3PairHandler : Nat × String → String := fun k => k.2 ++ "!"

#print axioms t3PairHandler

private def t3PairTable : HashTable (Nat × String) String t3PairHash :=
  HashTable.empty t3PairHash 2 (by decide)

#print axioms t3PairTable

private def t3PairA : Nat × String := (1, "a")

#print axioms t3PairA

private def t3PairB : Nat × String := (1, "b")

#print axioms t3PairB

private theorem t3Pair_collide :
    t3PairHash t3PairA = t3PairHash t3PairB := by decide

#print axioms t3Pair_collide

private theorem t3Pair_distinct : t3PairA ≠ t3PairB := by decide

#print axioms t3Pair_distinct

private def t3PairAfterA :
    String × HashTable (Nat × String) String t3PairHash :=
  serve t3PairHandler t3PairA t3PairTable

#print axioms t3PairAfterA

private theorem t3Pair_miss :
    HashTable.lookup t3PairB t3PairAfterA.2 = none := by decide

#print axioms t3Pair_miss

private theorem t3Pair_own :
    (serve t3PairHandler t3PairB t3PairAfterA.2).1 =
      t3PairHandler t3PairB := by decide

#print axioms t3Pair_own

#print axioms Cslib.Algorithms.Lean.HashTable.serve
#print axioms Cslib.Algorithms.Lean.HashTable.serve_of_lookup_eq_some
#print axioms Cslib.Algorithms.Lean.HashTable.serve_of_lookup_eq_none
#print axioms Cslib.Algorithms.Lean.HashTable.lookup_serve_self
#print axioms Cslib.Algorithms.Lean.HashTable.lookup_serve_of_ne
#print axioms Cslib.Algorithms.Lean.HashTable.serve_serve
#print axioms Cslib.Algorithms.Lean.HashTable.valid_serve
#print axioms Cslib.Algorithms.Lean.HashTable.fst_serve_of_agree
#print axioms Cslib.Algorithms.Lean.HashTable.agree_serve
#print axioms Cslib.Algorithms.Lean.HashTable.stale_serves_run_handler
#print axioms Cslib.Algorithms.Lean.HashTable.chained_serve_hits

end Cslib.Algorithms.Lean.HashTableIdempotentRequestTests
