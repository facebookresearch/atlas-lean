/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.ShiftedResolvent
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Star.Real

/-!
# Tests for shifted resolvents and row-sum bounds

Edge cases and guard failures for `fixedPoint_iff_shiftedResolvent`,
`spectralRadius_le_one_of_rowSum_le_one` and `eigenvalues_mem_Icc_zero_one_of_rowSum_le_one`,
and the finite-`λ` gain `λ μ / (1 + λ μ)`.
-/

open Matrix MathlibExt.LinearAlgebra.Matrix.ShiftedResolvent

namespace MathlibExtTest.LinearAlgebra.Matrix.ShiftedResolvent

/-! ### Zero matrix -/

-- `K = 0`: the fixed point is `z = 0`, and the resolvent formula gives `0`.
example {lam : ℝ} (hlam : 0 < lam) (Y z : Fin 3 → ℝ) :
    z = lam • ((0 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (Y - z)) ↔ z = 0 := by
  rw [(fixedPoint_iff_shiftedResolvent PosSemidef.zero hlam Y z).2.1]
  simp

/-! ### Identity and scalar matrices -/

-- `I` satisfies the row-sum bound (each row sums to exactly `1`) and has nonnegative entries.
example : (∀ i j, 0 ≤ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) ∧
    ∀ i, ∑ j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ 1 := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · by_cases h : i = j <;> simp [one_apply, h]
  · simp [one_apply]

-- So the spectral radius of `I` is at most `1` and its eigenvalues lie in `[0, 1]`.
example : spectralRadius ℂ ((1 : Matrix (Fin 3) (Fin 3) ℝ).map (algebraMap ℝ ℂ)) ≤ 1 :=
  spectralRadius_le_one_of_rowSum_le_one
    (fun i j => by by_cases h : i = j <;> simp [one_apply, h]) (fun i => by simp [one_apply])

example (i : Fin 3) : (PosDef.one.posSemidef : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef).1.eigenvalues i
    ∈ Set.Icc (0 : ℝ) 1 :=
  eigenvalues_mem_Icc_zero_one_of_rowSum_le_one PosDef.one.posSemidef
    (fun i j => by by_cases h : i = j <;> simp [one_apply, h]) (fun i => by simp [one_apply]) i

-- `2 I` violates the row-sum bound.
example : ¬ ∀ i, ∑ j, ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j ≤ 1 := by
  intro h
  have := h 0
  simp [one_apply] at this

-- Scalar `a I` with `a ∈ [0, 1]`: the row-sum bound holds, and the fixed point is
-- `z = (λ a / (1 + λ a)) Y`.
example {a : ℝ} (ha1 : a ≤ 1) :
    ∀ i, ∑ j, (a • (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j ≤ 1 := by
  intro i
  simpa [one_apply] using ha1

example {a lam : ℝ} (ha0 : 0 ≤ a) (hlam : 0 < lam) (Y : Fin 3 → ℝ) :
    (lam * a / (1 + lam * a)) • Y =
      lam • ((a • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ (Y - (lam * a / (1 + lam * a)) • Y)) := by
  have hp : 0 < 1 + lam * a := by positivity
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, smul_mulVec, one_mulVec, Pi.sub_apply]
  field_simp
  ring

/-! ### The hypotheses `0 < λ` and positive semidefiniteness are load-bearing -/

-- `λ = 0`, `K = I`: the fixed point forces `z = 0`, while the resolvent formula (with the total
-- inverse `0⁻¹ = 0`) gives `z = Y`; the equivalence fails for `Y ≠ 0`.
example : ¬ ∀ Y z : Fin 1 → ℝ,
    (z = (0 : ℝ) • ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (Y - z)) ↔
      z = (((0 : ℝ)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) + 1)⁻¹ * 1) *ᵥ Y) := by
  intro h
  have := (h 1 1).2 (by simp)
  have h0 := congrFun this 0
  simp at h0

-- `λ = -1`, `K = I`: `1 + λ K = 0` is singular. For `Y ≠ 0` the fixed point has no solution,
-- but the total-inverse resolvent formula gives `z = 0`.
example : ¬ ∀ Y z : Fin 1 → ℝ,
    (z = (-1 : ℝ) • ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (Y - z)) ↔
      z = (((-1 : ℝ)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) + 1)⁻¹ * 1) *ᵥ Y) := by
  intro h
  have hz : ((((-1 : ℝ)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) + 1)⁻¹ * 1) *ᵥ (1 : Fin 1 → ℝ)) = 0 := by
    have : (-1 : ℝ)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) + 1 = 0 := by
      ext i j; fin_cases i; fin_cases j; norm_num
    rw [this, Matrix.inv_zero, Matrix.zero_mul, zero_mulVec]
  have := (h 1 0).2 hz.symm
  have h0 := congrFun this 0
  simp at h0

/-! ### Nonsymmetric, nonreal and negative-entry examples -/

/-- The nonsymmetric matrix `[[1, 0], [1/2, 1/2]]`. -/
noncomputable abbrev N : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1 / 2, 1 / 2]

-- It has nonnegative entries and row sums `≤ 1`, so its spectral radius is at most `1`.
example : spectralRadius ℂ (N.map (algebraMap ℝ ℂ)) ≤ 1 :=
  spectralRadius_le_one_of_rowSum_le_one
    (fun i j => by fin_cases i <;> fin_cases j <;> norm_num [N])
    (fun i => by fin_cases i <;> norm_num [N, Fin.sum_univ_two])

-- Its eigenvalues `1` and `1/2` are real, but it is not symmetric, so the eigenvalue theorem for
-- positive semidefinite matrices does not apply to it.
example : (N - 1).det = 0 ∧ (N - (1 / 2 : ℝ) • 1).det = 0 := by
  constructor <;> simp [N, det_fin_two, one_apply]

example : ¬ N.IsHermitian := by
  intro h
  have := congrFun (congrFun h 0) 1
  norm_num [N, conjTranspose_apply] at this

/-- The cyclic permutation matrix of order `3`. -/
abbrev C : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

-- Its row sums are `1`, so its (complex) spectral radius is at most `1`.
example : spectralRadius ℂ (C.map (algebraMap ℝ ℂ)) ≤ 1 :=
  spectralRadius_le_one_of_rowSum_le_one
    (fun i j => by fin_cases i <;> fin_cases j <;> norm_num [C])
    (fun i => by fin_cases i <;> simp [C, Fin.sum_univ_three])

-- Its characteristic determinant is `1 - μ³`, so its only real eigenvalue is `1`; the other two
-- roots of `1 + μ + μ²` are nonreal. A generic matrix example, not a statement about any
-- particular application.
example (μ : ℝ) : (C - μ • 1).det = 1 - μ ^ 3 := by
  simp [C, det_fin_three, one_apply]
  ring

example (μ : ℝ) : 1 + μ + μ ^ 2 ≠ 0 := by nlinarith [sq_nonneg (2 * μ + 1)]

-- Negative entries break the bound: the `1 × 1` matrix `(-2)` has row sum `-2 ≤ 1` but the
-- eigenvalue `-2` (eigenvector `1`), outside `[-1, 1]`; the nonnegativity hypothesis is needed.
example : (∀ i, ∑ j, (!![-2] : Matrix (Fin 1) (Fin 1) ℝ) i j ≤ 1) ∧
    (!![-2] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ![1] = (-2 : ℝ) • ![1] ∧
    ¬ ∀ i j, 0 ≤ (!![-2] : Matrix (Fin 1) (Fin 1) ℝ) i j := by
  refine ⟨fun i => by fin_cases i; norm_num, by ext i; fin_cases i; simp, fun h => ?_⟩
  have := h 0 0
  norm_num at this

/-! ### Gain `λ μ / (1 + λ μ)` for finite `λ > 0` -/

-- For `μ ∈ [0, 1]` the gain lies in `[0, λ / (1 + λ)]`.
example {lam μ : ℝ} (hlam : 0 < lam) (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    0 ≤ lam * μ / (1 + lam * μ) ∧ lam * μ / (1 + lam * μ) ≤ lam / (1 + lam) := by
  have hp : 0 < 1 + lam * μ := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hp (by positivity)]
  nlinarith

-- It is monotone in `μ` on `[0, 1]`.
example {lam : ℝ} (hlam : 0 < lam) :
    MonotoneOn (fun μ : ℝ => lam * μ / (1 + lam * μ)) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have hpa : 0 < 1 + lam * a := by nlinarith [ha.1]
  have hpb : 0 < 1 + lam * b := by nlinarith [hb.1]
  simp only
  rw [div_le_div_iff₀ hpa hpb]
  nlinarith

-- `μ = 0` gives gain `0` for every `λ`; `μ = 1` gives `λ / (1 + λ)`.
example (lam : ℝ) : lam * 0 / (1 + lam * 0) = 0 := by simp
example (lam : ℝ) : lam * 1 / (1 + lam * 1) = lam / (1 + lam) := by simp

end MathlibExtTest.LinearAlgebra.Matrix.ShiftedResolvent
