/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.Star.Real

/-!
# qpGraph scores: generalized least squares in the edge lengths

Patterson et al. (2012, section "Admixture graph fitting") fit an admixture graph to a vector
`f` of estimated f-statistics on a basis of the space of f-statistics (of length
`n choose 2`), with estimated error covariance `Q`, by maximizing a score of the vector `g` of
f-statistics predicted by the graph:

* eq. (6): `S1(g) = -½ (g - f)ᵀ Q⁻¹ (g - f)`, an approximate log-likelihood (`scoreS1`);
* eq. (7): `S2(g) = -½ ∑ᵢ (gᵢ - fᵢ)² / (Qᵢᵢ + λ)`, a least-squares variant with a small
  constant `λ` (`scoreS2`).

The paper notes that `S2` is not basis independent, and that for fixed admixture weights both
scores are quadratic in the edge lengths, so they can be maximized by linear algebra. We prove
these facts:

* in the drift model the predicted statistics are linear in the edge lengths, `g = B ℓ`, with
  design matrix `B i e = (w Aᵢ e - w Bᵢ e) * (w Cᵢ e - w Dᵢ e)` (`f4_eq_designMatrix_mulVec`);
* `S1` is invariant under every invertible change of basis `f ↦ A f`, `g ↦ A g`,
  `Q ↦ A Q Aᵀ` (`scoreS1_basis_change`), while `S2` is not
  (`exists_scoreS2_basis_change_ne`);
* maximizing `S1` over the edge lengths is generalized least squares: for positive definite
  `Q`, every solution `ℓ̂` of the normal equations `Bᵀ Q⁻¹ B ℓ̂ = Bᵀ Q⁻¹ f` maximizes
  `ℓ ↦ S1(B ℓ)` (`scoreS1_le_of_normal_eq`); it is the unique maximizer when `B` has full column
  rank (`eq_of_scoreS1_eq`), and then `ℓ̂ = (Bᵀ Q⁻¹ B)⁻¹ Bᵀ Q⁻¹ f`
  (`isUnit_det_gram`, `normal_eq_gls`);
* `S2` is `S1` with `Q` replaced by the diagonal matrix of the `Qᵢᵢ + λ`
  (`scoreS2_eq_scoreS1_diagonal`), so the same results give weighted least squares.

Not covered: the nonnegativity constraint on edge lengths that the software imposes
(a constrained quadratic program), and the outer optimization over admixture weights. Mathlib's
inverse of a singular matrix is `0`, so `S1` is meaningful only for invertible `Q` (a
nondegenerate covariance), and `S2` only when every `Qᵢᵢ + λ` is nonzero (in the paper
`Qᵢᵢ ≥ 0` is a variance and `λ > 0`).

## References

* N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck,
  T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093,
  eqs. (6)–(7).
-/

@[expose] public section

open Matrix MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.QpGraph

variable {ι E : Type*} [Fintype ι]

/-- The qpGraph score `S1(g) = -½ (g - f)ᵀ Q⁻¹ (g - f)` (Patterson et al. 2012, eq. 6) of
predicted statistics `g` against estimated statistics `f` with error covariance `Q`. -/
noncomputable def scoreS1 [DecidableEq ι] (Q : Matrix ι ι ℝ) (f g : ι → ℝ) : ℝ :=
  -(1 / 2) * ((g - f) ⬝ᵥ (Q⁻¹ *ᵥ (g - f)))

/-- The least-squares qpGraph score `S2(g) = -½ ∑ᵢ (gᵢ - fᵢ)² / (Qᵢᵢ + λ)` (Patterson et al.
2012, eq. 7). A term with `Qᵢᵢ + λ = 0` is `0` by the convention `x / 0 = 0`. -/
noncomputable def scoreS2 (Q : Matrix ι ι ℝ) (lam : ℝ) (f g : ι → ℝ) : ℝ :=
  -(1 / 2) * ∑ i, (g i - f i) ^ 2 / (Q i i + lam)

private theorem mulVec_dotProduct {κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (v : κ → ℝ)
    (u : ι → ℝ) : (A *ᵥ v) ⬝ᵥ u = v ⬝ᵥ (Aᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- `S1` is basis independent: under an invertible change of basis `A` of the statistics, with
the covariance transformed to `A Q Aᵀ`, the score is unchanged. (The identity holds for every
`Q`; for singular `Q` both sides are `0` by Mathlib's convention `Q⁻¹ = 0`.) -/
theorem scoreS1_basis_change [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : IsUnit A.det)
    (Q : Matrix ι ι ℝ)
    (f g : ι → ℝ) : scoreS1 (A * Q * Aᵀ) (A *ᵥ f) (A *ᵥ g) = scoreS1 Q f g := by
  have hAt : IsUnit Aᵀ.det := by rwa [det_transpose]
  unfold scoreS1
  rw [← mulVec_sub, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_mulVec (g - f) A⁻¹ A, nonsing_inv_mul A hA, one_mulVec, mulVec_dotProduct,
    mulVec_mulVec, mul_nonsing_inv _ hAt, one_mulVec]

/-- `S2` is not basis independent (Patterson et al. 2012, after eq. 7): there are a positive
definite covariance `Q`, an invertible change of basis `A` and statistics `f`, `g` such that,
for every `λ`, the score changes. -/
theorem exists_scoreS2_basis_change_ne :
    ∃ (Q A : Matrix (Fin 2) (Fin 2) ℝ) (f g : Fin 2 → ℝ), Q.PosDef ∧ IsUnit A.det ∧
      ∀ lam : ℝ, scoreS2 (A * Q * Aᵀ) lam (A *ᵥ f) (A *ᵥ g) ≠ scoreS2 Q lam f g := by
  refine ⟨1, !![1, 1; 0, 1], 0, ![1, 0], PosDef.one, by simp [det_fin_two_of], fun lam => ?_⟩
  simp [scoreS2, mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]

/-- `S2` is `S1` with the covariance replaced by the diagonal matrix of the `Qᵢᵢ + λ`, when these
are nonzero. -/
theorem scoreS2_eq_scoreS1_diagonal [DecidableEq ι] (Q : Matrix ι ι ℝ) (lam : ℝ)
    (h : ∀ i, Q i i + lam ≠ 0)
    (f g : ι → ℝ) : scoreS2 Q lam f g = scoreS1 (diagonal fun i => Q i i + lam) f g := by
  have hinv : (diagonal fun i => Q i i + lam)⁻¹ = diagonal fun i => (Q i i + lam)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal]
    convert diagonal_one with i
    exact inv_mul_cancel₀ (h i)
  unfold scoreS2 scoreS1
  rw [hinv]
  congr 1
  simp only [dotProduct, mulVec_diagonal, Pi.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp [h i]

/-- The qpGraph design matrix of basis statistics `f4 (A i) (B i) (C i) (D i)` for lineage
weights `w`: entry `(i, e)` is `(w Aᵢ e - w Bᵢ e) * (w Cᵢ e - w Dᵢ e)`. -/
def designMatrix {ι E P : Type*} (w : P → E → ℝ) (A B C D : ι → P) : Matrix ι E ℝ :=
  fun i e => (w (A i) e - w (B i) e) * (w (C i) e - w (D i) e)

/-- In the drift model, with the admixture weights fixed, the predicted statistics are linear in
the edge lengths: `g = B ℓ` for the design matrix `B`. -/
theorem f4_eq_designMatrix_mulVec {ι E Ω P : Type*} [Fintype E] {m : MeasurableSpace Ω}
    {μ : Measure Ω}
    (M : DriftModel μ E P) (A B C D : ι → P) :
    (fun i => f4 μ M.freq (A i) (B i) (C i) (D i)) = designMatrix M.weight A B C D *ᵥ M.len := by
  funext i
  rw [M.f4_freq]
  simp [designMatrix, mulVec, dotProduct]

private theorem transpose_inv_of_posDef [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) :
    (Q⁻¹)ᵀ = Q⁻¹ := by
  have h := hQ.inv.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

/-- The Pythagorean decomposition behind GLS: for symmetric `W = Q⁻¹` and a solution `ℓ̂` of
the normal equations, `S1(B ℓ) = S1(B ℓ̂) - ½ (B (ℓ - ℓ̂))ᵀ Q⁻¹ (B (ℓ - ℓ̂))`. -/
private theorem scoreS1_eq_sub [DecidableEq ι] [Fintype E] {Q : Matrix ι ι ℝ}
    (hW : (Q⁻¹)ᵀ = Q⁻¹) (B : Matrix ι E ℝ) (f : ι → ℝ) {lhat : E → ℝ}
    (hnorm : (Bᵀ * Q⁻¹ * B) *ᵥ lhat = (Bᵀ * Q⁻¹) *ᵥ f) (l : E → ℝ) :
    scoreS1 Q f (B *ᵥ l) = scoreS1 Q f (B *ᵥ lhat) -
      1 / 2 * ((B *ᵥ (l - lhat)) ⬝ᵥ (Q⁻¹ *ᵥ (B *ᵥ (l - lhat)))) := by
  set x := B *ᵥ lhat - f
  set y := B *ᵥ (l - lhat)
  have hxy : B *ᵥ l - f = x + y := by
    simp only [x, y, mulVec_sub]
    abel
  have hsym : x ⬝ᵥ (Q⁻¹ *ᵥ y) = y ⬝ᵥ (Q⁻¹ *ᵥ x) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]
  have hcross : y ⬝ᵥ (Q⁻¹ *ᵥ x) = 0 := by
    have h0 : Bᵀ *ᵥ (Q⁻¹ *ᵥ x) = 0 := by
      simp only [x, mulVec_sub, mulVec_mulVec]
      rw [← Matrix.mul_assoc, hnorm, sub_self]
    simp only [y]
    rw [mulVec_dotProduct, h0, dotProduct_zero]
  unfold scoreS1
  rw [hxy, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hsym, hcross]
  ring

/-- GLS maximizes `S1`: for positive definite `Q`, a solution `ℓ̂` of the normal equations
`Bᵀ Q⁻¹ B ℓ̂ = Bᵀ Q⁻¹ f` maximizes `ℓ ↦ S1(B ℓ)` over all `ℓ`. -/
theorem scoreS1_le_of_normal_eq [DecidableEq ι] [Fintype E] {Q : Matrix ι ι ℝ} (hQ : Q.PosDef)
    (B : Matrix ι E ℝ)
    (f : ι → ℝ) {lhat : E → ℝ} (hnorm : (Bᵀ * Q⁻¹ * B) *ᵥ lhat = (Bᵀ * Q⁻¹) *ᵥ f)
    (l : E → ℝ) : scoreS1 Q f (B *ᵥ l) ≤ scoreS1 Q f (B *ᵥ lhat) := by
  rw [scoreS1_eq_sub (transpose_inv_of_posDef hQ) B f hnorm l]
  have h := hQ.inv.posSemidef.dotProduct_mulVec_nonneg (B *ᵥ (l - lhat))
  rw [star_trivial] at h
  linarith

/-- Uniqueness of the GLS maximizer: for positive definite `Q` and a design matrix of full
column rank (`B.mulVec` injective), a vector `ℓ` with the same score as a solution `ℓ̂` of the
normal equations equals `ℓ̂`. -/
theorem eq_of_scoreS1_eq [DecidableEq ι] [Fintype E] {Q : Matrix ι ι ℝ} (hQ : Q.PosDef)
    {B : Matrix ι E ℝ}
    (hB : Function.Injective B.mulVec) (f : ι → ℝ) {lhat : E → ℝ}
    (hnorm : (Bᵀ * Q⁻¹ * B) *ᵥ lhat = (Bᵀ * Q⁻¹) *ᵥ f) {l : E → ℝ}
    (h : scoreS1 Q f (B *ᵥ l) = scoreS1 Q f (B *ᵥ lhat)) : l = lhat := by
  rw [scoreS1_eq_sub (transpose_inv_of_posDef hQ) B f hnorm l] at h
  by_contra hne
  have hd : B *ᵥ (l - lhat) ≠ 0 := fun h0 =>
    hne (sub_eq_zero.mp (hB (h0.trans (mulVec_zero B).symm)))
  have hpos := hQ.inv.dotProduct_mulVec_pos hd
  rw [star_trivial] at hpos
  linarith

/-- For positive definite `Q` and a design matrix of full column rank, the GLS Gram matrix
`Bᵀ Q⁻¹ B` is invertible. -/
theorem isUnit_det_gram [DecidableEq ι] [Fintype E] [DecidableEq E] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosDef) {B : Matrix ι E ℝ}
    (hB : Function.Injective B.mulVec) : IsUnit (Bᵀ * Q⁻¹ * B).det := by
  have h := hQ.inv.conjTranspose_mul_mul_same hB
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact isUnit_iff_ne_zero.mpr h.det_pos.ne'

/-- The closed-form GLS estimate `ℓ̂ = (Bᵀ Q⁻¹ B)⁻¹ Bᵀ Q⁻¹ f` solves the normal equations when the
Gram matrix is invertible. -/
theorem normal_eq_gls [DecidableEq ι] [Fintype E] [DecidableEq E] {Q : Matrix ι ι ℝ}
    {B : Matrix ι E ℝ} (h : IsUnit (Bᵀ * Q⁻¹ * B).det)
    (f : ι → ℝ) :
    (Bᵀ * Q⁻¹ * B) *ᵥ ((Bᵀ * Q⁻¹ * B)⁻¹ *ᵥ ((Bᵀ * Q⁻¹) *ᵥ f)) = (Bᵀ * Q⁻¹) *ᵥ f := by
  rw [mulVec_mulVec, mul_nonsing_inv _ h, one_mulVec]

end MathlibExt.Biology.PopulationGenetics.QpGraph
