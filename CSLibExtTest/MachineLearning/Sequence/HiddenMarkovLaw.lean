/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkovLaw
public meta import CSLibExt.MachineLearning.Sequence.HiddenMarkovLaw
public import Mathlib.Algebra.BigOperators.Fin
public meta import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.NormNum

/-!
# Observation-likelihood normalization tests

Boundary fixture: `hZero`, a two-state HMM whose initial weight on state
`0` is zero. It satisfies `Normalized` (zeros allowed) and hence its
observation likelihood sums to one (`boundary_zeroInit_mass`).

Violated assumption: `hBad`, with every weight equal to `2`, is not
normalized and its total mass is `16`, not one (`violated_allTwo_mass`).
-/

@[expose] public section

namespace Cslib.MachineLearning.Sequence.HiddenMarkovLaw

open Cslib.MachineLearning.Sequence.HiddenMarkov

/-- Two-state HMM with a zero initial weight: state `0` never starts. -/
noncomputable def hZero : HMM (Fin 2) (Fin 2) ℝ where
  init := fun i => (i.val : ℝ)
  trans := fun _ _ => 1 / 2
  emit := fun _ _ => 1 / 2

/-- The zero-initial-weight example is normalized: zeros are allowed. -/
theorem hZero_normalized : Normalized hZero where
  init_nonneg := fun i => Nat.cast_nonneg _
  init_sum := by
    rw [Fin.sum_univ_two]
    have h0 : hZero.init 0 = ((0 : Fin 2).val : ℝ) := rfl
    have h1 : hZero.init 1 = ((1 : Fin 2).val : ℝ) := rfl
    rw [h0, h1]
    simp
  trans_nonneg := fun s s' => by
    have h : hZero.trans s s' = 1 / 2 := rfl
    rw [h]
    norm_num
  trans_sum := by
    intro s
    rw [Fin.sum_univ_two]
    have h : ∀ s' : Fin 2, hZero.trans s s' = 1 / 2 := fun _ => rfl
    simp only [h]
    norm_num
  emit_nonneg := fun s o => by
    have h : hZero.emit s o = 1 / 2 := rfl
    rw [h]
    norm_num
  emit_sum := by
    intro s
    rw [Fin.sum_univ_two]
    have h : ∀ o : Fin 2, hZero.emit s o = 1 / 2 := fun _ => rfl
    simp only [h]
    norm_num

/-- A zero initial weight is compatible with normalization. -/
theorem boundary_zeroInit_mass (t : ℕ) :
    ∑ x : Fin (t + 1) → Fin 2, likelihood hZero (extend t x) t = 1 :=
  sum_likelihood_eq_one _ _ _ hZero_normalized t

/-- Every weight equal to `2`: unnormalized semiring weights. -/
def hBad : HMM (Fin 2) (Fin 2) ℝ where
  init := fun _ => 2
  trans := fun _ _ => 2
  emit := fun _ _ => 2

/-- Unnormalized weights give total mass `16`, not one. -/
theorem violated_allTwo_mass :
    ∑ x : Fin 1 → Fin 2, likelihood hBad (extend 0 x) 0 ≠ 1 := by
  have e1 : ∀ x : Fin 1 → Fin 2,
      likelihood hBad (extend 0 x) 0 = 8 := by
    intro x
    simp only [likelihood]
    rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
    have e2 : ∀ s : Fin 2, pathProb hBad (extend 0 x) 0
        ((Equiv.funUnique (Fin 1) (Fin 2)).symm s) = 4 := by
      intro s
      have hs : (Equiv.funUnique (Fin 1) (Fin 2)).symm s = fun _ => s :=
        rfl
      have h1 : hBad.init ((fun _ => s) 0) = 2 := rfl
      have h2 : hBad.emit ((fun _ => s) 0) (extend 0 x 0) = 2 := rfl
      simp only [pathProb, hs, h1, h2]
      norm_num
    simp only [e2]
    rw [Fin.sum_univ_two]
    norm_num
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  simp only [e1]
  rw [Fin.sum_univ_two]
  norm_num

end Cslib.MachineLearning.Sequence.HiddenMarkovLaw
