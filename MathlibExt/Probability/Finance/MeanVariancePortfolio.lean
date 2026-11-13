/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Star.Real

/-!
# Mean-variance portfolios: the unique minimum-variance portfolio

Assets are indexed by a finite type `ι`, `S` is the covariance matrix of their returns and `μ` the
vector of expected returns. A portfolio `w` is feasible for target return `m` when it is fully
invested, `∑ i, w i = 1`, and has expected return `∑ i, μ i * w i = m`; short sales are allowed.
With `S` positive definite and `μ` not constant (the budget and mean constraints are
independent), there is exactly one feasible portfolio of minimal variance `wᵀ S w`. It is
`w* = Bᵀ (1, m)`, where `B = (Mᵀ S⁻¹ M)⁻¹ Mᵀ S⁻¹` is the generalized least-squares matrix of the
constraint matrix `M = [1 μ]` (Aitken's theorem,
`MathlibExt.Probability.Statistics.GeneralizedLeastSquares`).

## Main results

* `isUnit_gram_iff`: `Mᵀ S⁻¹ M` is invertible iff `μ` is not constant.
* `minVariancePortfolio_isFeasible`, `portfolioVariance_minVariancePortfolio_le`,
  `eq_minVariancePortfolio_of_portfolioVariance_le`: `w*` is feasible, minimal and the unique
  minimizer.
* `existsUnique_minVariance`: the unique-existence statement.

## References

* R. C. Merton, *An analytic derivation of the efficient portfolio frontier*, J. Financial
  Quant. Anal. 7 (1972), 1851–1872.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.MeanVariancePortfolio

open Matrix MathlibExt.Probability.Statistics.GeneralizedLeastSquares
open MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence (quadForm)

/-- The `ι × 2` constraint matrix `M = [1 μ]` of the Markowitz problem: column `0` is the budget
vector of ones and column `1` is the vector `μ` of expected asset returns. -/
def constraintMatrix {ι : Type*} (μ : ι → ℝ) : Matrix ι (Fin 2) ℝ :=
  Matrix.of fun i j => ![1, μ i] j

/-- A portfolio `w` is feasible for target expected return `m` when it is fully invested
(`∑ i, w i = 1`, the budget constraint) and has expected return `∑ i, μ i * w i = m` (the mean
constraint). Weights may be negative: short sales are allowed. -/
def IsFeasible {ι : Type*} [Fintype ι] (μ : ι → ℝ) (m : ℝ) (w : ι → ℝ) : Prop :=
  ∑ i, w i = 1 ∧ ∑ i, μ i * w i = m

/-- The minimum-variance portfolio for target return `m`: `w* = Bᵀ (1, m)` with
`B = (Mᵀ S⁻¹ M)⁻¹ Mᵀ S⁻¹` the GLS matrix of the constraint matrix `M` and covariance `S`. -/
noncomputable def minVariancePortfolio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (μ : ι → ℝ) (m : ℝ) : ι → ℝ :=
  (glsMatrix (constraintMatrix μ) S)ᵀ *ᵥ ![1, m]

private theorem mulVec_constraintMatrix_apply {ι : Type*} (μ : ι → ℝ) (z : Fin 2 → ℝ)
    (i : ι) : ((constraintMatrix μ) *ᵥ z) i = z 0 + μ i * z 1 := by
  simp [constraintMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private theorem transpose_mulVec_constraintMatrix_zero {ι : Type*} [Fintype ι] (μ : ι → ℝ)
    (w : ι → ℝ) :
    (((constraintMatrix μ)ᵀ *ᵥ w) 0 = ∑ i, w i) := by
  simp [constraintMatrix, Matrix.mulVec, dotProduct, Matrix.cons_val_zero]

private theorem transpose_mulVec_constraintMatrix_one {ι : Type*} [Fintype ι] (μ : ι → ℝ)
    (w : ι → ℝ) :
    (((constraintMatrix μ)ᵀ *ᵥ w) 1 = ∑ i, μ i * w i) := by
  simp [constraintMatrix, Matrix.mulVec, dotProduct, Matrix.cons_val_one]

private theorem injective_mulVec_constraintMatrix {ι : Type*} (μ : ι → ℝ)
    (hμ : ∃ i j, μ i ≠ μ j) : Function.Injective (constraintMatrix μ).mulVec := by
  obtain ⟨a, b, hab⟩ := hμ
  intro x y hxy
  have hker : (constraintMatrix μ) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hsub : x - y = 0 := by
    have h0 : ∀ i, (x - y) 0 + μ i * (x - y) 1 = 0 := fun i => by
      have h := congrFun hker i
      rwa [mulVec_constraintMatrix_apply, Pi.zero_apply] at h
    have ha := h0 a
    have hb := h0 b
    have h1 : (x - y) 1 = 0 := by
      have heq : μ a * (x - y) 1 = μ b * (x - y) 1 := by linarith
      have hmul : (μ a - μ b) * (x - y) 1 = 0 := by rw [sub_mul, heq, sub_self]
      have hne : μ a - μ b ≠ 0 := sub_ne_zero.mpr hab
      exact (mul_eq_zero.mp hmul).resolve_left hne
    have h0' : (x - y) 0 = 0 := by
      rw [h1, mul_zero, add_zero] at ha
      exact ha
    funext j
    fin_cases j
    · simpa using h0'
    · simpa using h1
  exact sub_eq_zero.mp hsub

private theorem isFeasible_iff_transpose {ι : Type*} [Fintype ι] (μ : ι → ℝ) (m : ℝ)
    (w : ι → ℝ) : IsFeasible μ m w ↔ (constraintMatrix μ)ᵀ *ᵥ w = ![1, m] := by
  constructor
  · intro hw
    have h0 : ((constraintMatrix μ)ᵀ *ᵥ w) 0 = ![1, m] 0 := by
      rw [transpose_mulVec_constraintMatrix_zero, hw.1, Matrix.cons_val_zero]
    have h1 : ((constraintMatrix μ)ᵀ *ᵥ w) 1 = ![1, m] 1 := by
      rw [transpose_mulVec_constraintMatrix_one, hw.2, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    funext j
    fin_cases j
    · simpa using h0
    · simpa using h1
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := congrFun h 0
      rwa [transpose_mulVec_constraintMatrix_zero, Matrix.cons_val_zero] at h0
    · have h1 := congrFun h 1
      rwa [transpose_mulVec_constraintMatrix_one, Matrix.cons_val_one, Matrix.cons_val_zero] at h1

private theorem glsMatrix_mul_cov {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : S.PosDef) (μ : ι → ℝ) :
    glsMatrix (constraintMatrix μ) S * S =
      ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ)⁻¹ * (constraintMatrix μ)ᵀ := by
  rw [glsMatrix, Matrix.mul_assoc _ S⁻¹,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit), Matrix.mul_one]

private theorem cov_mul_glsMatrix_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ}
    (hS : S.PosDef) (μ : ι → ℝ) :
    S * (glsMatrix (constraintMatrix μ) S)ᵀ =
      constraintMatrix μ * ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ)⁻¹ᵀ := by
  have hST : Sᵀ = S := by
    have h := hS.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have hBS := glsMatrix_mul_cov hS μ
  have h := congrArg Matrix.transpose hBS
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hST, Matrix.transpose_transpose] at h
  exact h

private theorem cov_mulVec_minVariancePortfolio {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) (m : ℝ) :
    S *ᵥ minVariancePortfolio S μ m =
      constraintMatrix μ *ᵥ
        ((((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ)⁻¹)ᵀ *ᵥ ![1, m]) := by
  have hSB := cov_mul_glsMatrix_transpose hS μ
  change S *ᵥ ((glsMatrix (constraintMatrix μ) S)ᵀ *ᵥ ![1, m]) = _
  rw [Matrix.mulVec_mulVec, hSB, ← Matrix.mulVec_mulVec]

private theorem transpose_mulVec_minVariancePortfolio {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (μ : ι → ℝ) (m : ℝ)
    (hG : IsUnit ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ)) :
    (constraintMatrix μ)ᵀ *ᵥ minVariancePortfolio S μ m = ![1, m] := by
  have hBM : glsMatrix (constraintMatrix μ) S * constraintMatrix μ = 1 :=
    glsMatrix_mul_self hG
  change (constraintMatrix μ)ᵀ *ᵥ ((glsMatrix (constraintMatrix μ) S)ᵀ *ᵥ ![1, m]) = _
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hBM, Matrix.transpose_one,
    Matrix.one_mulVec]

private theorem orthogonality_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : S.PosDef) {μ : ι → ℝ} {m : ℝ} {w : ι → ℝ} (hw : IsFeasible μ m w)
    (hG : IsUnit ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ)) :
    (w - minVariancePortfolio S μ m) ⬝ᵥ (S *ᵥ minVariancePortfolio S μ m) = 0 := by
  have hSw := cov_mulVec_minVariancePortfolio hS μ m
  rw [hSw, ← Matrix.dotProduct_transpose_mulVec]
  have hsub : (constraintMatrix μ)ᵀ *ᵥ (w - minVariancePortfolio S μ m) = 0 := by
    rw [Matrix.mulVec_sub, (isFeasible_iff_transpose μ m w).mp hw,
      transpose_mulVec_minVariancePortfolio μ m hG, sub_self]
  rw [hsub, dotProduct_zero]

private theorem variance_decomp_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : S.PosDef) {μ : ι → ℝ} {m : ℝ} {w : ι → ℝ} (hw : IsFeasible μ m w)
    (hG : IsUnit ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ)) :
    quadForm S w =
      quadForm S (minVariancePortfolio S μ m) +
        quadForm S (w - minVariancePortfolio S μ m) := by
  have hortho := orthogonality_aux hS hw hG
  have hSymm : S.IsSymm := by
    have h := hS.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have hortho2 : minVariancePortfolio S μ m ⬝ᵥ (S *ᵥ (w - minVariancePortfolio S μ m)) = 0 := by
    rw [hSymm.dotProduct_mulVec_comm]
    exact hortho
  have hexpand : quadForm S
      (minVariancePortfolio S μ m + (w - minVariancePortfolio S μ m)) =
      quadForm S (minVariancePortfolio S μ m) +
        quadForm S (w - minVariancePortfolio S μ m) := by
    simp only [quadForm, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
    rw [hortho2, hortho, add_zero, zero_add]
  have hw_eq : minVariancePortfolio S μ m + (w - minVariancePortfolio S μ m) = w := by abel
  rw [hw_eq] at hexpand
  exact hexpand

/-- Under a positive definite covariance, the Gram matrix `Mᵀ S⁻¹ M` of the two constraints is
invertible iff the budget and mean constraints are independent, i.e. the mean vector `μ` is not
constant (not proportional to the vector of ones). -/
theorem isUnit_gram_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : S.PosDef) (μ : ι → ℝ) :
    IsUnit ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ) ↔ ∃ i j, μ i ≠ μ j := by
  constructor
  · intro hG
    by_contra hcon
    push Not at hcon
    by_cases hι : Nonempty ι
    · obtain ⟨i0⟩ := hι
      have hMx : (constraintMatrix μ) *ᵥ ![μ i0, -1] = 0 := by
        funext i
        rw [mulVec_constraintMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_zero, Pi.zero_apply, hcon i i0]
        ring
      have hx0 : ![μ i0, -1] ≠ (0 : Fin 2 → ℝ) := by
        intro hcon2
        have h1 := congrFun hcon2 1
        simp [Matrix.cons_val_one] at h1
      have hG0 : ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ) *ᵥ ![μ i0, -1] = 0 := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMx, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      have hinj := Matrix.mulVec_injective_of_isUnit hG
      have heq : ![μ i0, -1] = (0 : Fin 2 → ℝ) := hinj (by rw [hG0, Matrix.mulVec_zero])
      exact hx0 heq
    · have : IsEmpty ι := ⟨fun x => hι ⟨x⟩⟩
      have hG0 : (constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ = 0 := by
        funext a b
        simp [Matrix.mul_apply]
      rw [hG0, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two] at hG
      simp [isUnit_iff_ne_zero] at hG
  · intro hμ
    have hInv : S⁻¹.PosDef := hS.inv
    have hInj := injective_mulVec_constraintMatrix μ hμ
    have h := hInv.conjTranspose_mul_mul_same (B := constraintMatrix μ) hInj
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact h.isUnit

/-- The minimum-variance portfolio satisfies the budget and mean constraints. -/
theorem minVariancePortfolio_isFeasible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) {μ : ι → ℝ} (hμ : ∃ i j, μ i ≠ μ j) (m : ℝ) :
    IsFeasible μ m (minVariancePortfolio S μ m) := by
  rw [isFeasible_iff_transpose]
  exact transpose_mulVec_minVariancePortfolio μ m ((isUnit_gram_iff hS μ).mpr hμ)

/-- Every feasible portfolio has variance at least that of the minimum-variance portfolio. -/
theorem portfolioVariance_minVariancePortfolio_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) {μ : ι → ℝ} (hμ : ∃ i j, μ i ≠ μ j) {m : ℝ}
    {w : ι → ℝ} (hw : IsFeasible μ m w) :
    quadForm S (minVariancePortfolio S μ m) ≤ quadForm S w := by
  have hG : IsUnit ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ) :=
    (isUnit_gram_iff hS μ).mpr hμ
  have hdecomp := variance_decomp_aux hS hw hG
  have hnonneg : 0 ≤ quadForm S (w - minVariancePortfolio S μ m) := by
    have h := hS.posSemidef.dotProduct_mulVec_nonneg (w - minVariancePortfolio S μ m)
    rw [star_trivial] at h
    simpa [quadForm] using h
  linarith

/-- Uniqueness: a feasible portfolio whose variance does not exceed that of the minimum-variance
portfolio is the minimum-variance portfolio. -/
theorem eq_minVariancePortfolio_of_portfolioVariance_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) {μ : ι → ℝ} (hμ : ∃ i j, μ i ≠ μ j) {m : ℝ}
    {w : ι → ℝ} (hw : IsFeasible μ m w)
    (hle : quadForm S w ≤ quadForm S (minVariancePortfolio S μ m)) :
    w = minVariancePortfolio S μ m := by
  have hG : IsUnit ((constraintMatrix μ)ᵀ * S⁻¹ * constraintMatrix μ) :=
    (isUnit_gram_iff hS μ).mpr hμ
  have hdecomp := variance_decomp_aux hS hw hG
  have hnonneg : 0 ≤ quadForm S (w - minVariancePortfolio S μ m) := by
    have h := hS.posSemidef.dotProduct_mulVec_nonneg (w - minVariancePortfolio S μ m)
    rw [star_trivial] at h
    simpa [quadForm] using h
  have hvar0 : quadForm S (w - minVariancePortfolio S μ m) = 0 := by linarith
  have hd0 : w - minVariancePortfolio S μ m = 0 := by
    by_contra hne
    have hpos := hS.dotProduct_mulVec_pos hne
    rw [star_trivial] at hpos
    simp only [quadForm] at hvar0
    linarith
  exact sub_eq_zero.mp hd0

/-- **Unique minimum-variance portfolio.** With a positive definite covariance matrix and
independent budget/mean constraints, for every target return `m` there is exactly one feasible
portfolio of minimal variance. -/
theorem existsUnique_minVariance {ι : Type*} [Fintype ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) {μ : ι → ℝ} (hμ : ∃ i j, μ i ≠ μ j) (m : ℝ) :
    ∃! w : ι → ℝ, IsFeasible μ m w ∧
      ∀ v : ι → ℝ, IsFeasible μ m v → quadForm S w ≤ quadForm S v := by
  classical
  refine ⟨minVariancePortfolio S μ m, ⟨?_, ?_⟩, ?_⟩
  · exact minVariancePortfolio_isFeasible hS hμ m
  · intro v hv
    exact portfolioVariance_minVariancePortfolio_le hS hμ hv
  · intro y hy
    exact eq_minVariancePortfolio_of_portfolioVariance_le hS hμ hy.1
      (hy.2 (minVariancePortfolio S μ m) (minVariancePortfolio_isFeasible hS hμ m))

end MathlibExt.Probability.Finance.MeanVariancePortfolio
