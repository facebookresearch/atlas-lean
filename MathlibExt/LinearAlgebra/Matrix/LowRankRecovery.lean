/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Matrix.Normed

import MathlibExt.LinearAlgebra.Matrix.RankAddGeneral

/-!
# Low-rank matrix recovery: nuclear norm and restricted isometry

Affine rank minimization asks for the matrix of least rank in an affine space `{X : 𝒜(X) = b}`.
B. Recht, M. Fazel and P. A. Parrilo (*Guaranteed minimum-rank solutions of linear matrix
equations via nuclear norm minimization*, SIAM Review 52 (2010), arXiv:0706.4138) replace the rank
by the nuclear norm `‖X‖_* = ∑ᵢ σᵢ(X)` and show that the two problems have the same solution when
the linear map `𝒜` satisfies a restricted isometry property on low-rank matrices.

## Main definitions

- `nuclearNorm X`: the sum of the singular values of `X`.
- `IsRestrictedIsometry 𝒜 r δ`: `(1 - δ) ‖X‖_F ≤ ‖𝒜(X)‖ ≤ (1 + δ) ‖X‖_F` for every `X` of rank
  at most `r` (Definition 3.1 of Recht–Fazel–Parrilo, with `δ` any admissible constant), with
  Mathlib's Frobenius norm (`open scoped Matrix.Norms.Frobenius`).

## Main results

- `eq_of_isRestrictedIsometry_two_mul`: if `𝒜` is a restricted isometry of order `2 r` with
  constant `δ < 1`, then `X₀` is the only matrix of rank at most `r` with `𝒜(X) = 𝒜(X₀)`
  (Theorem 3.2). The rank step uses the subadditivity of the rank, `Matrix.rank_sub_le` from
  `MathlibExt.LinearAlgebra.Matrix.RankAddGeneral`.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Frobenius

namespace MathlibExt.LinearAlgebra.Matrix.LowRankRecovery

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Nuclear norm.** The nuclear norm `‖X‖_* = ∑ᵢ σᵢ(X)` of a real matrix `X`, the sum of the
singular values of `X` acting as a linear map between Euclidean spaces.

Source: B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear
matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), arXiv:0706.4138,
Section 2 (the nuclear norm `‖X‖_* := ∑_{i=1}^r σᵢ(X)`). -/
noncomputable def nuclearNorm [DecidableEq n] (X : Matrix m n ℝ) : ℝ :=
  (Matrix.toEuclideanLin X).singularValues.sum fun _ s => s

/-- **The nuclear norm is nonnegative.** `0 ≤ ‖X‖_*`, since singular values are nonnegative.

Source: B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear
matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), arXiv:0706.4138,
Section 2 (the nuclear norm is a norm). -/
theorem nuclearNorm_nonneg [DecidableEq n] (X : Matrix m n ℝ) : 0 ≤ nuclearNorm X :=
  Finsupp.sum_nonneg fun i _ => LinearMap.singularValues_nonneg _ i

/-- **Restricted isometry property.** A linear map `𝒜` from real `m × n` matrices to `ℝ^p` is a
restricted isometry of order `r` with constant `δ` if
`(1 - δ) ‖X‖_F ≤ ‖𝒜(X)‖ ≤ (1 + δ) ‖X‖_F` for every matrix `X` of rank at most `r`, where `‖X‖_F`
is Mathlib's Frobenius norm `(∑ᵢ ∑ⱼ Xᵢⱼ²)^{1/2}` (`Matrix.frobenius_norm_def`). The
`r`-restricted isometry constant `δ_r(𝒜)` of the source is the least such `δ`, so `δ_r(𝒜) < c`
if and only if `𝒜` is a restricted isometry of order `r` with some constant `δ < c`.

Source: B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear
matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), arXiv:0706.4138,
Definition 3.1, inequality (3.2) (norms not squared, as in the source). -/
def IsRestrictedIsometry {p : ℕ} (𝒜 : Matrix m n ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (r : ℕ)
    (δ : ℝ) : Prop :=
  ∀ X : Matrix m n ℝ, X.rank ≤ r →
    (1 - δ) * ‖X‖ ≤ ‖𝒜 X‖ ∧ ‖𝒜 X‖ ≤ (1 + δ) * ‖X‖

/-- **Uniqueness of the low-rank solution under restricted isometry.** Let `𝒜` be a restricted
isometry of order `2 r` with constant `δ < 1` (that is, `δ_{2r}(𝒜) < 1`). If `X` and `X₀` both have
rank at most `r` and `𝒜(X) = 𝒜(X₀)`, then `X = X₀`: `X₀` is the only matrix of rank at most `r`
in its affine space `{X : 𝒜(X) = 𝒜(X₀)}`.

Source: B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear
matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), arXiv:0706.4138,
Theorem 3.2. -/
theorem eq_of_isRestrictedIsometry_two_mul {p : ℕ}
    {𝒜 : Matrix m n ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {r : ℕ} {δ : ℝ}
    (hRIP : IsRestrictedIsometry 𝒜 (2 * r) δ) (hδ : δ < 1) {X X₀ : Matrix m n ℝ}
    (hX : X.rank ≤ r) (hX₀ : X₀.rank ≤ r) (h : 𝒜 X = 𝒜 X₀) : X = X₀ := by
  have hrank : (X₀ - X).rank ≤ 2 * r := (Matrix.rank_sub_le X₀ X).trans (by omega)
  have hzero : 𝒜 (X₀ - X) = 0 := by rw [map_sub, h, sub_self]
  have hlow := (hRIP (X₀ - X) hrank).1
  rw [hzero, norm_zero] at hlow
  have hnn : 0 ≤ ‖X₀ - X‖ := norm_nonneg _
  have hF : ‖X₀ - X‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖X₀ - X‖ := lt_of_le_of_ne hnn (Ne.symm hne)
    nlinarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hF)).symm

end MathlibExt.LinearAlgebra.Matrix.LowRankRecovery
