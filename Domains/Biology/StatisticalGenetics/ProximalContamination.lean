/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.Star.Real

/-!
# Proximal contamination in mixed-model association

A mixed-model association test of a candidate marker with standardized genotype vector `x`
against a phenotype vector `y` uses the generalized-least-squares score statistic

  `χ²(V) = (xᵀ V⁻¹ y)² / (xᵀ V⁻¹ x)`,

where `V` is the phenotypic covariance matrix, built from a genetic relationship matrix that
averages `x_k x_kᵀ` over the markers `k` used to build it. If the candidate marker itself is among
those markers, `V` contains the term `c x xᵀ` (`c = σ²_g / M` for a relationship matrix of `M`
markers and genetic variance `σ²_g`): `V = V₀ + c x xᵀ`, where `V₀` is the covariance built
without the candidate. This "proximal contamination" (Listgarten et al. 2012; Yang et al. 2014)
deflates the statistic by an exact factor: by the Sherman–Morrison identity
`V⁻¹ x = V₀⁻¹ x / (1 + c xᵀ V₀⁻¹ x)`, so

  `χ²(V₀ + c x xᵀ) = χ²(V₀) / (1 + c xᵀ V₀⁻¹ x)`

for every phenotype vector `y`. The closed form is derived here from the Sherman–Morrison
identity; the cited papers describe the deflation and remedy it by excluding the candidate's
region from the relationship matrix (leave-one-chromosome-out).

## Main results

* `mmChiSq`: the statistic `(xᵀ V⁻¹ y)² / (xᵀ V⁻¹ x)`.
* `inv_add_smul_vecMulVec_mulVec`: `(V₀ + c x xᵀ)⁻¹ x = (1 + c xᵀ V₀⁻¹ x)⁻¹ • V₀⁻¹ x`.
* `mmChiSq_add_smul_vecMulVec`: `χ²(V₀ + c x xᵀ) = χ²(V₀) / (1 + c xᵀ V₀⁻¹ x)`.
* `mmChiSq_add_smul_vecMulVec_le`: including the candidate never increases the statistic.

## References

* J. Listgarten, C. Lippert, C. M. Kadie, R. I. Davidson, E. Eskin, D. Heckerman, *Improved
  linear mixed models for genome-wide association studies*, Nat. Methods 9 (2012), 525–526.
* J. Yang, N. A. Zaitlen, M. E. Goddard, P. M. Visscher, A. L. Price, *Advantages and pitfalls in
  the application of mixed-model association methods*, Nat. Genet. 46 (2014), 100–106.
* J. Sherman, W. J. Morrison, *Adjustment of an inverse matrix corresponding to a change in one
  element of a given matrix*, Ann. Math. Statist. 21 (1950), 124–127.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Biology.StatisticalGenetics.ProximalContamination

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The mixed-model (generalized-least-squares score) statistic
`χ²(V) = (xᵀ V⁻¹ y)² / (xᵀ V⁻¹ x)` of the marker `x` for the phenotype `y` under the phenotypic
covariance `V`. For positive definite `V` and `x ≠ 0` the denominator is positive. -/
noncomputable def mmChiSq (V : Matrix n n ℝ) (x y : n → ℝ) : ℝ :=
  (x ⬝ᵥ (V⁻¹ *ᵥ y)) ^ 2 / (x ⬝ᵥ (V⁻¹ *ᵥ x))

private theorem posDef_add_smul_vecMulVec {m : Type*} [Finite m] {V₀ : Matrix m m ℝ}
    (hV₀ : V₀.PosDef) {c : ℝ}
    (hc : 0 ≤ c) (x : m → ℝ) : (V₀ + c • vecMulVec x x).PosDef := by
  have h := posSemidef_vecMulVec_self_star x
  simp only [star_trivial] at h
  exact hV₀.add_posSemidef (h.smul hc)

private theorem dotProduct_mulVec_symm {A : Matrix n n ℝ} (hA : A.PosDef) (x y : n → ℝ) :
    x ⬝ᵥ (A⁻¹ *ᵥ y) = y ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hT : (A⁻¹)ᵀ = A⁻¹ := by
    have := hA.inv.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

/-- **Sherman–Morrison applied to the candidate marker**: for positive definite `V₀` and
`c ≥ 0`, `(V₀ + c x xᵀ)⁻¹ x = (1 + c xᵀ V₀⁻¹ x)⁻¹ • V₀⁻¹ x`. -/
theorem inv_add_smul_vecMulVec_mulVec {V₀ : Matrix n n ℝ} (hV₀ : V₀.PosDef) {c : ℝ}
    (hc : 0 ≤ c) (x : n → ℝ) :
    (V₀ + c • vecMulVec x x)⁻¹ *ᵥ x =
      (1 + c * (x ⬝ᵥ (V₀⁻¹ *ᵥ x)))⁻¹ • (V₀⁻¹ *ᵥ x) := by
  set V := V₀ + c • vecMulVec x x
  set u := V₀⁻¹ *ᵥ x
  set q := x ⬝ᵥ u
  have hq : 0 ≤ q := by
    by_cases hx : x = 0
    · simp [q, u, hx]
    · exact (hV₀.inv.dotProduct_mulVec_pos hx).le
  have hpos : 0 < 1 + c * q := by positivity
  have hV : V.PosDef := posDef_add_smul_vecMulVec hV₀ hc x
  have hVu : V *ᵥ u = (1 + c * q) • x := by
    have hdet : IsUnit V₀.det := (isUnit_iff_isUnit_det V₀).mp hV₀.isUnit
    have h1 : V₀ *ᵥ u = x := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, h1, op_smul_eq_smul, smul_smul, add_smul,
      one_smul]
  have hinv : V⁻¹ *ᵥ (V *ᵥ u) = u := by
    rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det V).mp hV.isUnit), one_mulVec]
  rw [hVu, mulVec_smul] at hinv
  rw [← hinv, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

private theorem dotProduct_inv_mulVec_self_nonneg {V₀ : Matrix n n ℝ} (hV₀ : V₀.PosDef)
    (x : n → ℝ) : 0 ≤ x ⬝ᵥ (V₀⁻¹ *ᵥ x) := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hV₀.inv.dotProduct_mulVec_pos hx).le

/-- **Proximal contamination**: including the candidate marker `x` in the covariance,
`V = V₀ + c x xᵀ` with `V₀` positive definite and `c ≥ 0`, divides the mixed-model statistic by
`1 + c xᵀ V₀⁻¹ x`, for every phenotype vector `y`:
`χ²(V₀ + c x xᵀ) = χ²(V₀) / (1 + c xᵀ V₀⁻¹ x)`. -/
theorem mmChiSq_add_smul_vecMulVec {V₀ : Matrix n n ℝ} (hV₀ : V₀.PosDef) {c : ℝ} (hc : 0 ≤ c)
    (x y : n → ℝ) :
    mmChiSq (V₀ + c • vecMulVec x x) x y =
      mmChiSq V₀ x y / (1 + c * (x ⬝ᵥ (V₀⁻¹ *ᵥ x))) := by
  have hV := posDef_add_smul_vecMulVec hV₀ hc x
  have hq := dotProduct_inv_mulVec_self_nonneg hV₀ x
  have hpos : 0 < 1 + c * (x ⬝ᵥ (V₀⁻¹ *ᵥ x)) := by positivity
  unfold mmChiSq
  rw [dotProduct_mulVec_symm hV x y, inv_add_smul_vecMulVec_mulVec hV₀ hc x, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, ← dotProduct_mulVec_symm hV₀ x y]
  set q := x ⬝ᵥ (V₀⁻¹ *ᵥ x)
  set a := x ⬝ᵥ (V₀⁻¹ *ᵥ y)
  rcases hq.eq_or_lt with h0 | hq'
  · rw [← h0]; simp
  · field_simp

/-- Including the candidate marker in the covariance never increases the mixed-model
statistic: `χ²(V₀ + c x xᵀ) ≤ χ²(V₀)` for positive definite `V₀` and `c ≥ 0`. -/
theorem mmChiSq_add_smul_vecMulVec_le {V₀ : Matrix n n ℝ} (hV₀ : V₀.PosDef) {c : ℝ}
    (hc : 0 ≤ c) (x y : n → ℝ) : mmChiSq (V₀ + c • vecMulVec x x) x y ≤ mmChiSq V₀ x y := by
  have hq := dotProduct_inv_mulVec_self_nonneg hV₀ x
  have h0 : 0 ≤ mmChiSq V₀ x y := div_nonneg (sq_nonneg _) hq
  rw [mmChiSq_add_smul_vecMulVec hV₀ hc]
  exact div_le_self h0 (by nlinarith [mul_nonneg hc hq])

end MathlibExt.Biology.StatisticalGenetics.ProximalContamination
