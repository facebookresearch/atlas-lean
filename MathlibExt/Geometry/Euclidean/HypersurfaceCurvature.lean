/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Analysis.InnerProductSpace.NormSqHessian

/-!
# Second fundamental form and mean curvature of hypersurfaces of Euclidean space

A `C²` hypersurface `S` of a finite-dimensional real inner product space `E` is locally the zero
set of a `C²` function `ρ : E → ℝ` with nonvanishing differential (a local defining function,
`EuclideanGeometry.IsLocalDefiningFunction`). We define the second fundamental form and the mean
curvature of a level set of `ρ` at `p`, with respect to the unit normal `ν = ∇ρ(p) / ‖∇ρ(p)‖`:
```
II(u, v) = D²ρ(p)(u, v) / ‖∇ρ(p)‖                  (u, v ⊥ ∇ρ(p)),
H        = tr_{∇ρ(p)⊥} D²ρ(p) / ‖∇ρ(p)‖ = (Δρ(p) - D²ρ(p)(ν, ν)) / ‖∇ρ(p)‖,
```
so that `II(u, v) = ⟪D_u ν, v⟫` and `H = div ν` at `p`: `H` is the trace of `II` on the tangent
hyperplane, the sum of the principal curvatures with respect to `ν`. The formula for `II` is the
second fundamental form only on tangent vectors `u`, `v ⊥ ∇ρ(p)`; for other vectors its value
depends on the choice of `ρ`, so statements should restrict `II` to tangent vectors. The values
only depend on the hypersurface and on the side toward which `ν` points: replacing `ρ` by `f ρ`
with `f > 0` leaves them unchanged (on tangent vectors), and replacing `ρ` by `-ρ` changes their
sign. This is proved here for constant `f`
(`levelSetMeanCurvature_smul`); the general case is the same computation with the product rule,
using `ρ(p) = 0` and `Dρ(p) = 0` on tangent vectors.

Conventions: `H` is the sum (not the average) of the principal curvatures, and it is positive on
the unit sphere for the outward normal (`levelSetMeanCurvature_sphere`: `H = n - 1`). For a domain
`Ω = {ρ < 0}` the normal `∇ρ / ‖∇ρ‖` is the outward normal of `∂Ω`; with this convention a convex
domain has `H ≥ 0` (mean convex).

Relation to standard references, which use other normalizations (so neither is the source of these
exact conventions):
* Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, take the mean
  curvature to be the average of the principal curvatures (§14.6, and the mean curvature equation
  (16.1) with right-hand side `nH(1 + |Du|²)^{3/2}`), with the same sign for the boundary of a
  convex domain: `levelSetMeanCurvature = (n - 1) H_GT` for a hypersurface of `ℝⁿ`.
* Spivak, *A Comprehensive Introduction to Differential Geometry*, Vol. III (3rd ed.), defines the
  second fundamental form for a unit normal `ν` as `-⟨dν(X), Y⟩` (Ch. 1, Cor. 9) and the mean
  curvature of a surface as half the trace (Ch. 2, p. 49; Ch. 3, p. 136). For the same `ν`,
  `levelSetSecondFundamentalForm = -II_Spivak`, and for surfaces in `ℝ³`,
  `levelSetMeanCurvature = -2 H_Spivak`.
* In the implicit form of Wikipedia's "Mean curvature" (surfaces in `ℝ³`, curvature positive when
  the surface bends toward the normal), `H = -½ ∇ · (∇F / |∇F|)`; ours is `-2` times that.

## Main definitions and results

* `EuclideanGeometry.IsLocalDefiningFunction S ρ p`: `ρ p = 0` and near `p`, `S = {ρ = 0}`, with
  `ρ` of class `C²` at `p` and `Dρ(p) ≠ 0`.
* `EuclideanGeometry.levelSetSecondFundamentalForm ρ p u v` and
  `EuclideanGeometry.levelSetMeanCurvature ρ p`.
* `EuclideanGeometry.levelSetMeanCurvature_sphere`: the unit sphere has `H = n - 1`.
* `EuclideanGeometry.levelSetMeanCurvature_affine`: hyperplanes have `H = 0`.
* `EuclideanGeometry.levelSetMeanCurvature_smul`, `levelSetSecondFundamentalForm_smul`: rescaling
  `ρ` by `c ≠ 0` multiplies both by the sign of `c` (`levelSetMeanCurvature_smul_of_pos`,
  `levelSetMeanCurvature_neg`).
-/

@[expose] public section

open Module Filter
open scoped Topology Gradient

noncomputable section

namespace EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- `ρ` is a local defining function of `S ⊆ E` at `p`: `p` lies on the zero set of `ρ`, `ρ` is
`C²` at `p`, its differential at `p` is nonzero, and near `p` the set `S` is the zero set of `ρ`
(in particular `p ∈ S`). Every point of a `C²` hypersurface has local defining functions, and every
point of a regular level set of a `C²` function is of this form. -/
def IsLocalDefiningFunction (S : Set E) (ρ : E → ℝ) (p : E) : Prop :=
  ρ p = 0 ∧ ContDiffAt ℝ 2 ρ p ∧ fderiv ℝ ρ p ≠ 0 ∧ ∀ᶠ x in 𝓝 p, x ∈ S ↔ ρ x = 0

omit [FiniteDimensional ℝ E] in
/-- A point with a local defining function lies on the hypersurface. -/
theorem IsLocalDefiningFunction.mem {S : Set E} {ρ : E → ℝ} {p : E}
    (h : IsLocalDefiningFunction S ρ p) : p ∈ S :=
  h.2.2.2.self_of_nhds.2 h.1

/-- The second fundamental form at `p` of the level set of `ρ` through `p`, with respect to the
unit normal `∇ρ(p) / ‖∇ρ(p)‖`: `II(u, v) = D²ρ(p)(u, v) / ‖∇ρ(p)‖`, for tangent vectors `u`, `v`
(orthogonal to `∇ρ(p)`). It equals `⟪D_u ν, v⟫` for the unit normal field `ν = ∇ρ / ‖∇ρ‖`.

The formula is defined for all `u v : E`, but it is the second fundamental form (independent of
the defining function, up to the sign fixed by the normal) only for tangent `u` and `v`: two
defining functions of the same hyperplane can give different values on the normal vector. -/
def levelSetSecondFundamentalForm (ρ : E → ℝ) (p u v : E) : ℝ :=
  fderiv ℝ (fderiv ℝ ρ) p u v / ‖∇ ρ p‖

/-- The mean curvature at `p` of the level set of `ρ` through `p`, with respect to the unit normal
`ν = ∇ρ(p) / ‖∇ρ(p)‖`: the trace of the second fundamental form on the tangent hyperplane
`∇ρ(p)⊥`, `H = (Δρ(p) - D²ρ(p)(ν, ν)) / ‖∇ρ(p)‖ = div (∇ρ / ‖∇ρ‖)(p)`, the sum of the principal
curvatures. The Laplacian is computed in the orthonormal basis `stdOrthonormalBasis ℝ E`; since
`D²ρ(p)` is bilinear, this does not depend on the basis. -/
def levelSetMeanCurvature (ρ : E → ℝ) (p : E) : ℝ :=
  ((∑ i, fderiv ℝ (fderiv ℝ ρ) p (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)) -
      fderiv ℝ (fderiv ℝ ρ) p (∇ ρ p) (∇ ρ p) / ‖∇ ρ p‖ ^ 2) / ‖∇ ρ p‖

omit [FiniteDimensional ℝ E] in
private theorem fderiv_fderiv_smul (ρ : E → ℝ) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (c • ρ)) = c • fderiv ℝ (fderiv ℝ ρ) := by
  rw [fderiv_const_smul_field c]
  exact fderiv_const_smul_field (f := fderiv ℝ ρ) c

private theorem gradient_smul (ρ : E → ℝ) (c : ℝ) (p : E) : ∇ (c • ρ) p = c • ∇ ρ p := by
  simp [gradient, fderiv_const_smul_field c]

/-- Rescaling the defining function by `c ≠ 0` multiplies the second fundamental form by the sign
of `c`: it only depends on the level set and on the side toward which the normal points. -/
theorem levelSetSecondFundamentalForm_smul (ρ : E → ℝ) (p u v : E) {c : ℝ} (hc : c ≠ 0) :
    levelSetSecondFundamentalForm (c • ρ) p u v =
      c / |c| * levelSetSecondFundamentalForm ρ p u v := by
  simp only [levelSetSecondFundamentalForm, fderiv_fderiv_smul, gradient_smul, Pi.smul_apply,
    smul_apply, norm_smul, Real.norm_eq_abs, smul_eq_mul]
  have ha : |c| ≠ 0 := abs_ne_zero.mpr hc
  by_cases hg : ∇ ρ p = 0
  · simp [hg]
  · have hn : ‖∇ ρ p‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    field_simp

/-- Rescaling the defining function by `c ≠ 0` multiplies the mean curvature by the sign of `c`. -/
theorem levelSetMeanCurvature_smul (ρ : E → ℝ) (p : E) {c : ℝ} (hc : c ≠ 0) :
    levelSetMeanCurvature (c • ρ) p = c / |c| * levelSetMeanCurvature ρ p := by
  simp only [levelSetMeanCurvature, fderiv_fderiv_smul, gradient_smul, Pi.smul_apply,
    smul_apply, map_smul, norm_smul, Real.norm_eq_abs, smul_eq_mul]
  by_cases hg : ∇ ρ p = 0
  · simp [hg]
  · have hn : ‖∇ ρ p‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    have ha : |c| ≠ 0 := abs_ne_zero.mpr hc
    rw [← Finset.mul_sum]
    field_simp
    rw [sq_abs]
    ring

/-- A positive multiple of the defining function has the same mean curvature. -/
theorem levelSetMeanCurvature_smul_of_pos (ρ : E → ℝ) (p : E) {c : ℝ} (hc : 0 < c) :
    levelSetMeanCurvature (c • ρ) p = levelSetMeanCurvature ρ p := by
  rw [levelSetMeanCurvature_smul ρ p hc.ne', abs_of_pos hc, div_self hc.ne', one_mul]

/-- Reversing the normal (replacing `ρ` by `-ρ`) changes the sign of the mean curvature. -/
theorem levelSetMeanCurvature_neg (ρ : E → ℝ) (p : E) :
    levelSetMeanCurvature (-ρ) p = -levelSetMeanCurvature ρ p := by
  rw [← neg_one_smul ℝ ρ, levelSetMeanCurvature_smul ρ p (by norm_num)]
  norm_num

private theorem gradient_norm_sq_sub_one (p : E) :
    ∇ (fun x : E ↦ ‖x‖ ^ 2 - 1) p = (2 : ℝ) • p := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.sub_const 1) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

/-- Sanity check: the unit sphere of `E`, as the zero set of `‖x‖² - 1`, has mean curvature
`n - 1` with respect to the outward normal (sum convention). -/
theorem levelSetMeanCurvature_sphere (p : E) (hp : ‖p‖ = 1) :
    levelSetMeanCurvature (fun x : E ↦ ‖x‖ ^ 2 - 1) p = finrank ℝ E - 1 := by
  have h1 : fderiv ℝ (fun x : E ↦ ‖x‖ ^ 2 - 1) = fderiv ℝ (fun x : E ↦ ‖x‖ ^ 2) := by
    funext x; exact fderiv_sub_const _
  have hb : ∀ i, inner ℝ (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) = (1 : ℝ) :=
    fun i ↦ by simp [(stdOrthonormalBasis ℝ E).orthonormal.1 i]
  rw [levelSetMeanCurvature, gradient_norm_sq_sub_one, h1]
  simp only [fderiv_fderiv_norm_sq_apply, hb, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hp, norm_smul]
  norm_num
  ring

/-- Sanity check: a hyperplane `{x | ⟪a, x⟫ = c}` has mean curvature `0`. -/
theorem levelSetMeanCurvature_affine (a : E) (c : ℝ) (p : E) :
    levelSetMeanCurvature (fun x : E ↦ inner ℝ a x - c) p = 0 := by
  have h : fderiv ℝ (fun x : E ↦ inner ℝ a x - c) = fun _ ↦ innerSL ℝ a := by
    funext x
    exact ((innerSL ℝ a).hasFDerivAt.sub_const c).fderiv
  simp [levelSetMeanCurvature, h]

end EuclideanGeometry
