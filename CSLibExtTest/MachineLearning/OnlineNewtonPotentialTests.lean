/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.OnlineNewtonPotential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Regressions for the Online Newton Step log-determinant potential -/

open scoped Matrix
open Cslib.MachineLearning.LinearBandit Cslib.MachineLearning.OnlineNewtonStep

namespace CSLibExtTest.MachineLearning

private noncomputable def A : ℕ → Matrix (Fin 1) (Fin 1) ℝ :=
  ellipticalGram ((2 : ℝ) • 1) (fun _ _ => 1)

-- With regularization 2 and the first gradient equal to 1, the post-update inverse
-- gives 1/3, not the pre-update value 1/2. The ratio uses the initial determinant 2.
example : ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((A 1)⁻¹ *ᵥ fun _ => 1)) = 1 / 3 ∧
    (A 1).det / (A 0).det = 3 / 2 ∧ (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
  have h0 : A 0 = (2 : ℝ) • 1 := ellipticalGram_zero _ _
  have h1 : A 1 = (3 : ℝ) • 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [A, ellipticalGram, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
  have hinv : ((3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = (3⁻¹ : ℝ) • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_assoc, one_mul, ← smul_assoc, smul_eq_mul,
      mul_inv_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul]
  have hquad : ((fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((A 1)⁻¹ *ᵥ fun _ => 1)) = 1 / 3 := by
    rw [h1, hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    norm_num [dotProduct, smul_eq_mul]
  have hratio : (A 1).det / (A 0).det = 3 / 2 := by
    rw [h1, h0, Matrix.det_smul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    norm_num
  have h := (logDetPotential (ι := Fin 1) 2 (by norm_num) (fun _ _ => 1) 1 1 (by
    intro t _
    norm_num [dotProduct, Real.sqrt_one])).1
  change (∑ t ∈ Finset.range 1,
    (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((A (t + 1))⁻¹ *ᵥ fun _ => 1)) ≤
      Real.log ((A 1).det / (A 0).det) at h
  rw [Finset.sum_range_one, hquad, hratio] at h
  exact ⟨hquad, hratio, h⟩

-- The bound also applies at zero dimension, with no nonemptiness assumption.
example (g : ℕ → Fin 0 → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.range T, g t ⬝ᵥ ((ellipticalGram (1 : Matrix (Fin 0) (Fin 0) ℝ)
      g (t + 1))⁻¹ *ᵥ g t)) ≤ 0 := by
  have h := (logDetPotential (ι := Fin 0) 1 (by norm_num) g T 0 (by
    intro t _
    simp [dotProduct])).1
  simp only [one_smul, Matrix.det_isEmpty, div_one, Real.log_one] at h
  exact h

-- Pin the second inequality in dimension two with nonunit regularization and two
-- nonzero updates. The final diagonal is (4, 2), while the initial diagonal is (2, 2).
example : Real.log (2 : ℝ) ≤ 2 * Real.log 2 := by
  let g : ℕ → Fin 2 → ℝ := fun _ i => if i = 0 then 1 else 0
  let B := ellipticalGram ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) g
  have hnorm : ∀ t < 2, Real.sqrt (g t ⬝ᵥ g t) ≤ 1 := by
    intro t _
    norm_num [g, dotProduct, Fin.sum_univ_two]
  have h0 : B 0 = (2 : ℝ) • 1 := ellipticalGram_zero _ _
  have h2 : B 2 = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (4 : ℝ) else 2) := by
    change ellipticalGram ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) g (0 + 1 + 1) = _
    rw [ellipticalGram_succ, ellipticalGram_succ, ellipticalGram_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [g, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
  have hratio : (B 2).det / (B 0).det = 2 := by
    rw [h2, h0, Matrix.det_diagonal, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    norm_num [Fin.prod_univ_two]
  have h := (logDetPotential (ι := Fin 2) 2 (by norm_num) g 2 1 hnorm).2
  change Real.log ((B 2).det / (B 0).det) ≤
    (Fintype.card (Fin 2) : ℝ) * Real.log (1 + (2 : ℝ) * 1 ^ 2 / 2) at h
  rw [hratio, Fintype.card_fin] at h
  norm_num at h
  exact h

-- An empty horizon imposes no gradient bound, even when `G` is negative.
example :
    (∑ t ∈ Finset.range 0, (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ((A (t + 1))⁻¹ *ᵥ fun _ => 1)) ≤
      Real.log ((A 0).det / (A 0).det) :=
  (logDetPotential (ι := Fin 1) 2 (by norm_num) (fun _ _ => 1) 0 (-1) (by
    intro t ht
    omega)).1

end CSLibExtTest.MachineLearning
