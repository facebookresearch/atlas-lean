/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Diagonal operators on a Hilbert basis

For a Hilbert basis `b` of an inner product space `H` and coefficients
`a : ι → 𝕜`, a uniform bound `∀ i, ‖a i‖ ≤ C` defines a continuous linear
map on `H`. The map transports bounded coordinate multiplication on `ℓ²`
through `b.repr`. Its convergent series formula is
`D x = ∑' i, (a i * ⟪b i, x⟫) • b i`. Squaring the map squares its
coefficients. The constructor requires the bound and does not define an
unbounded operator by a totalized infinite sum.

This is the general mechanism behind the square of the Green's operator's
square root in `MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared`: there
the coefficient function is `k ↦ 1 / (kπ)`, and squaring it gives the
Green's eigenvalues `k ↦ 1 / (k²π²)`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.greensOperatorSqrt` (Definition, May 13, 2021 section),
which defines `A^{1/2}` by its action on the sine eigenbasis. The diagonal
operator here is the general form of that definition; the Green's case is
its corollary in `GreensOperatorSqrtSquared`.
-/

@[expose] public section

open Filter Topology InnerProductSpace
open scoped ComplexConjugate ENNReal lp

namespace MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*}

/-- The bounded diagonal continuous linear map with coefficients `a` in the
Hilbert basis `b`. Its uniform coefficient bound is part of the constructor. -/
noncomputable def diagonalOperator (b : HilbertBasis ι 𝕜 H) (a : ι → 𝕜) {C : ℝ}
    (hC : ∀ i, ‖a i‖ ≤ C) : H →L[𝕜] H :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun i => a i • ContinuousLinearMap.id 𝕜 𝕜) (abs_nonneg C) (fun i => by
        simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
          (hC i).trans (le_abs_self C))).comp
      b.repr.toLinearIsometry.toContinuousLinearMap)

/-- If `a` is bounded, the coefficient sequence of the diagonal operator is in `ℓ²`. -/
private theorem memℓp_diagonal_coeff {b : HilbertBasis ι 𝕜 H} {a : ι → 𝕜} {C : ℝ}
    (hC : ∀ i, ‖a i‖ ≤ C) (x : H) :
    Memℓp (fun i => a i * ⟪b i, x⟫_𝕜) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h2]
  simp only [Real.rpow_two]
  have hle : ∀ i, ‖a i * ⟪b i, x⟫_𝕜‖ ^ 2 ≤ C ^ 2 * ‖⟪b i, x⟫_𝕜‖ ^ 2 := by
    intro i
    simp only [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC i) 2)
      (sq_nonneg _)
  exact Summable.of_nonneg_of_le (fun i => sq_nonneg _) hle
    (Summable.mul_left _ (b.orthonormal.inner_products_summable x))

/-- The diagonal operator is the inverse image under `repr` of its coefficient sequence. -/
private theorem diagonalOperator_eq_repr_symm {b : HilbertBasis ι 𝕜 H} {a : ι → 𝕜}
    {C : ℝ} (hC : ∀ i, ‖a i‖ ≤ C) (x : H) :
    diagonalOperator b a hC x =
      b.repr.symm ⟨fun i => a i * ⟪b i, x⟫_𝕜, memℓp_diagonal_coeff hC x⟩ := by
  apply b.repr.injective
  ext i
  simp [diagonalOperator, lp.mapCLM_apply_coe, HilbertBasis.repr_apply_apply]

/-- The `repr` coordinates of the diagonal operator. -/
theorem repr_diagonalOperator_apply {b : HilbertBasis ι 𝕜 H} {a : ι → 𝕜} {C : ℝ}
    (hC : ∀ i, ‖a i‖ ≤ C) (x : H) (i : ι) :
    b.repr (diagonalOperator b a hC x) i = a i * ⟪b i, x⟫_𝕜 := by
  rw [diagonalOperator_eq_repr_symm hC x]
  simp [LinearIsometryEquiv.apply_symm_apply]

/-- The series formula for a bounded diagonal map is a genuine convergent
Hilbert-basis expansion. -/
theorem diagonalOperator_eq_tsum {b : HilbertBasis ι 𝕜 H} {a : ι → 𝕜} {C : ℝ}
    (hC : ∀ i, ‖a i‖ ≤ C) (x : H) :
    diagonalOperator b a hC x = ∑' i, (a i * ⟪b i, x⟫_𝕜) • b i := by
  rw [diagonalOperator_eq_repr_symm hC x]
  exact (b.hasSum_repr_symm
    ⟨fun i => a i * ⟪b i, x⟫_𝕜, memℓp_diagonal_coeff hC x⟩).tsum_eq.symm

/-- A diagonal operator acts on basis vectors by scalar multiplication. -/
theorem diagonalOperator_apply_basis {b : HilbertBasis ι 𝕜 H} {a : ι → 𝕜} {C : ℝ}
    (hC : ∀ i, ‖a i‖ ≤ C) (j : ι) :
    diagonalOperator b a hC (b j) = a j • b j := by
  classical
  rw [diagonalOperator_eq_tsum hC, tsum_eq_single j]
  · have hj : ⟪b j, b j⟫_𝕜 = 1 := by
      simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one j]
    rw [hj, mul_one]
  · intro i hi
    rw [b.orthonormal.inner_eq_zero hi, mul_zero, zero_smul]

/-- A bounded diagonal operator squared is the diagonal operator with squared coefficients. -/
theorem diagonalOperator_sq {b : HilbertBasis ι 𝕜 H} {a : ι → 𝕜} {C : ℝ}
    (hC : ∀ i, ‖a i‖ ≤ C) (x : H) :
    diagonalOperator b a hC (diagonalOperator b a hC x) =
      diagonalOperator b (fun i => (a i) ^ 2) (C := C ^ 2) (fun i => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC i) 2) x := by
  have hC2 : ∀ i, ‖(a i) ^ 2‖ ≤ C ^ 2 := by
    intro i
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC i) 2
  apply b.repr.injective
  ext i
  rw [repr_diagonalOperator_apply hC (diagonalOperator b a hC x) i,
    repr_diagonalOperator_apply hC2 x i]
  rw [← b.repr_apply_apply (diagonalOperator b a hC x) i,
    repr_diagonalOperator_apply hC x i]
  ring

end MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
