/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.LongOnlyAttainment

/-!
# Tests for long-only target-slice attainment

Singular and zero matrices, feasible non-singleton slices, infeasible
targets (empty slice), and an independent numeric pin.
-/

open Matrix

namespace MathlibExt.Probability.Finance.LongOnlyAttainment

private theorem mem_halves :
    (![1 / 2, 1 / 2] : Fin 2 → ℝ) ∈ targetSlice (![0, 1] : Fin 2 → ℝ) (1 / 2 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · norm_num [dotProduct, Fin.sum_univ_two]

private theorem mem_constMean :
    (![1, 0] : Fin 2 → ℝ) ∈ targetSlice (fun _ => (3 : ℝ)) (3 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · norm_num [dotProduct, Fin.sum_univ_two]

private theorem mem_three_a :
    (![1 / 2, 0, 1 / 2] : Fin 3 → ℝ)
      ∈ targetSlice (![0, 0, 1] : Fin 3 → ℝ) (1 / 2 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · norm_num [dotProduct, Fin.sum_univ_three]

private theorem mem_three_b :
    (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ)
      ∈ targetSlice (![0, 0, 1] : Fin 3 → ℝ) (1 / 2 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · norm_num [dotProduct, Fin.sum_univ_three]

-- Zero (singular) covariance: attainment holds.
example : ∃ w ∈ targetSlice (![0, 1] : Fin 2 → ℝ) (1 / 2 : ℝ),
    IsMinOn (fun w => w ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w))
      (targetSlice (![0, 1] : Fin 2 → ℝ) (1 / 2 : ℝ)) w :=
  exists_isMinOn_targetSlice _ _ _ ⟨_, mem_halves⟩

-- Zero covariance: the objective value at halves is 0.
example : (fun w : Fin 2 → ℝ => w ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w))
    ![1 / 2, 1 / 2] = 0 := by
  norm_num [Matrix.zero_mulVec, dotProduct_zero]

-- Constant means: attainment holds on the feasible slice.
example : ∃ w ∈ targetSlice (fun _ => (3 : ℝ)) (3 : ℝ),
    IsMinOn (fun w => w ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w))
      (targetSlice (fun _ => (3 : ℝ)) (3 : ℝ)) w :=
  exists_isMinOn_targetSlice _ _ _ ⟨_, mem_constMean⟩

-- A 3-asset slice need not be a singleton.
example : ∃ w₁ ∈ targetSlice (![0, 0, 1] : Fin 3 → ℝ) (1 / 2 : ℝ),
    ∃ w₂ ∈ targetSlice (![0, 0, 1] : Fin 3 → ℝ) (1 / 2 : ℝ), w₁ ≠ w₂ :=
  ⟨_, mem_three_a, _, mem_three_b, by
    intro h
    have h0 := congrFun h 0
    norm_num at h0⟩

-- Infeasible target: the slice is empty (so no theorem instance applies).
example : (targetSlice (![0, 1] : Fin 2 → ℝ) (2 : ℝ) : Set (Fin 2 → ℝ)) = ∅ := by
  ext w
  simp only [targetSlice, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hw
  obtain ⟨hge, hsum, hdot⟩ := hw
  have h1 : w 1 ≤ 1 :=
    calc w 1 ≤ ∑ j, w j :=
            Finset.single_le_sum (fun j _ => hge j) (Finset.mem_univ 1)
        _ = 1 := hsum
  have hdot' : (![0, 1] : Fin 2 → ℝ) ⬝ᵥ w = w 1 := by
    norm_num [dotProduct, Fin.sum_univ_two]
  rw [hdot'] at hdot
  rw [hdot] at h1
  norm_num at h1

-- Numeric pin: objective value at the minimizer, computed directly.
example : (fun w : Fin 2 → ℝ => w ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w))
    ![1 / 2, 1 / 2] = 1 / 2 := by
  norm_num [Matrix.one_mulVec, dotProduct, Fin.sum_univ_two]

-- Numeric pin: `![1/2, 1/2]` minimizes the identity quadratic on its slice.
example : IsMinOn (fun w : Fin 2 → ℝ => w ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w))
    (targetSlice (![0, 1] : Fin 2 → ℝ) (1 / 2 : ℝ)) ![1 / 2, 1 / 2] := by
  have hsing : ∀ w ∈ targetSlice (![0, 1] : Fin 2 → ℝ) (1 / 2 : ℝ),
      w = ![1 / 2, 1 / 2] := by
    intro w hw
    obtain ⟨-, hsum, hdot⟩ :
        (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (![0, 1] : Fin 2 → ℝ) ⬝ᵥ w = 1 / 2 := hw
    have hdot' : (![0, 1] : Fin 2 → ℝ) ⬝ᵥ w = w 1 := by
      norm_num [dotProduct, Fin.sum_univ_two]
    rw [hdot'] at hdot
    have h0 : w 0 = 1 / 2 := by
      rw [Fin.sum_univ_two, hdot] at hsum
      have h' : w 0 = (w 0 + 1 / 2) - 1 / 2 := by ring
      rw [h', hsum]
      norm_num
    have h1 : w 1 = 1 / 2 := hdot
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  intro w hw
  have hw' : w = ![1 / 2, 1 / 2] := hsing w hw
  subst hw'
  simp

end MathlibExt.Probability.Finance.LongOnlyAttainment
