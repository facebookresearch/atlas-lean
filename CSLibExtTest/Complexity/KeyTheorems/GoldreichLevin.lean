/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.KeyTheorems.GoldreichLevin

namespace MetaMathlibExt.Complexity.KeyTheorems.GoldreichLevinTest

open GoldreichLevin

-- Input order and output order both matter when recovering coordinate bits.
example : List.ofFn (glPair (fun i : Fin 2 => i == 1) (fun i => i == 0)) =
    [false, true, true, false] := by decide

example : glCircuitOutputs [(1, [0]), (0, [1]), (0, [0])] [true, false] 2 =
    [false, true] := by decide

private theorem count_set {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    Set.ncard {x | P x} = (Finset.univ.filter P).card := by
  have e : {x | P x} = (↑(Finset.univ.filter P) : Set α) := by ext; simp
  rw [e, Set.ncard_coe_finset]

-- On one bit the constant-false predictor wins three of the four input pairs.
example : predictSucc (n := 1) [(1, [0])] id = 3 / 4 := by
  rw [predictSucc, count_set]
  conv_lhs => enter [1, 1]; equals 3 => decide
  norm_num

-- The empty circuit makes no prediction, even when the correct inner product is false.
example : predictSucc (n := 1) [] id = 0 := by
  simp [predictSucc, glCircuitEval, Cslib.Complexity.Classes.circuitEval]

example : invertSucc (n := 1) [(0, [0])] id = 1 := by
  rw [invertSucc, count_set]
  conv_lhs => enter [1, 1]; equals 2 => decide
  norm_num

-- Specialize the security theorem to any predictor consisting of a single gate.
example (π : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool))
    (hbij : ∀ n, Function.Bijective (π n))
    (hfwd : ∃ q : Polynomial ℕ, ∀ n, ∃ D : List GLGate, D.length ≤ q.eval n ∧
      ∀ x, glCircuitOutputs D (List.ofFn x) n = List.ofFn (π n x))
    (how : ∀ (C : ℕ → List GLGate) (p : Polynomial ℕ),
      (∀ n, (C n).length ≤ p.eval n) →
        Cslib.Complexity.Classes.Negligible (fun n => invertSucc (C n) (π n)))
    (g : ℕ → GLGate) :
    Cslib.Complexity.Classes.Negligible (fun n => max 0 (predictSucc [g n] (π n) - 1 / 2)) :=
  goldreich_levin π hbij hfwd how (fun n => [g n]) 1 (by simp)

end MetaMathlibExt.Complexity.KeyTheorems.GoldreichLevinTest
