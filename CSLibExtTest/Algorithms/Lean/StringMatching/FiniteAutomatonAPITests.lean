/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.FiniteAutomaton

public section

set_option autoImplicit false

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.TimeM

example {A : Nat} (pattern : List (Fin A)) :
    TimeM Nat (Vector (Fin (pattern.length + 1)) ((pattern.length + 1) * A)) :=
  computeTransition pattern

example {A : Nat} (pattern : List (Fin A)) (q : Fin (pattern.length + 1)) (a : Fin A) :
    IsGreatest {k : Nat | k ≤ pattern.length ∧ pattern.take k <:+ pattern.take q.val ++ [a]}
      ((computeTransition pattern).ret.get ⟨q.val * A + a.val, by
        calc
          q.val * A + a.val < q.val * A + A := Nat.add_lt_add_left a.isLt _
          _ = (q.val + 1) * A := (Nat.succ_mul q.val A).symm
          _ ≤ (pattern.length + 1) * A :=
            Nat.mul_le_mul_right A (Nat.succ_le_of_lt q.isLt)⟩).val :=
  computeTransition_spec pattern q a

example {A : Nat} (pattern : List (Fin A)) :
    Cslib.Automata.DA.FinAcc (Fin (pattern.length + 1)) (Fin A) := patternAutomaton pattern

example {A : Nat} (pattern word : List (Fin A)) :
    IsGreatest {k : Nat | k ≤ pattern.length ∧ pattern.take k <:+ word}
      ((patternAutomaton pattern).mtr (patternAutomaton pattern).start word).val :=
  patternAutomaton_state pattern word

example {A : Nat} (pattern text : List (Fin A)) : TimeM Nat (List Nat) :=
  finiteAutomatonMatches pattern text

example {A : Nat} (pattern text : List (Fin A)) :
    (finiteAutomatonMatches pattern text).ret = (naiveMatches pattern text).ret :=
  finiteAutomatonMatches_ret pattern text

example {A : Nat} (pattern text : List (Fin A)) :
    (finiteAutomatonMatches pattern text).time = (computeTransition pattern).time +
      2 * text.length + (finiteAutomatonMatches pattern text).ret.length :=
  finiteAutomatonMatches_time pattern text

example {A : Nat} (pattern : List (Fin A)) :
    (computeTransition pattern).time ≤ 2 * A * (pattern.length + 1) ^ 3 :=
  computeTransition_time_le pattern

example {A : Nat} (pattern text : List (Fin A)) (offset : Nat) :
    offset ∈ (finiteAutomatonMatches pattern text).ret ↔ MatchAt pattern text offset := by
  rw [finiteAutomatonMatches_ret]
  exact mem_naiveMatches_iff pattern text offset

example : (finiteAutomatonMatches ([0, 0] : List (Fin 1)) [0, 0, 0]).ret = [0, 1] := by
  rw [finiteAutomatonMatches_ret, naiveMatches_ret]
  decide

example : (finiteAutomatonMatches ([] : List (Fin 0)) []).ret = [0] := by
  rw [finiteAutomatonMatches_ret, naiveMatches_ret]
  decide

end
