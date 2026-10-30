/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature

/-!
# Riemann, Ricci, scalar and sectional curvature of a Riemannian manifold

Let `M` be a `C^∞` manifold with a `C^∞` Riemannian metric `g`, given as in
`Mathlib.Geometry.Manifold.Riemannian.Basic` by
```
[IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
[IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
```
and let `∇` be its Levi-Civita connection `CovariantDerivative.leviCivitaConnection I M`.
We define the curvature quantities of `(M, g)`. References with the same conventions: Lang,
*Lecture Notes on Riemannian Geometry* (ETH Zürich, 2020) [Lang]; Gudmundsson, *An Introduction to
Riemannian Geometry* (Lund University lecture notes) [Gud]; Lee, *Introduction to Riemannian
Manifolds* (2nd ed., GTM 176, 2018), Ch. 7-8.

* `Manifold.riemannCurvature I x u v w`: the Riemann curvature endomorphism
  `R(u, v) w = ∇_u ∇_v w - ∇_v ∇_u w - ∇_[u, v] w` of the Levi-Civita connection
  (`CovariantDerivative.extendCurvature`; [Lang, Def. 2.1], [Gud, Def. 8.8]). The opposite sign
  convention is also common.
* `Manifold.sectionalCurvature I x u v = ⟪R(u, v) v, u⟫ / (‖u‖² ‖v‖² - ⟪u, v⟫²)`, the sectional
  curvature of the plane spanned by linearly independent `u` and `v` ([Lang, Def. 2.4],
  [Gud, Def. 8.14]). The round unit sphere has sectional curvature `1` ([Gud, Example 8.23]).
* `Manifold.ricci I x v w = tr (z ↦ R(z, v) w)`, the Ricci tensor ([Lang, Def. 2.7]): the
  metric-free Ricci contraction `CovariantDerivative.extendRicci` of the Levi-Civita connection.
* `Manifold.scalarCurvature I x = ∑ i, Ric(eᵢ, eᵢ)`, the metric trace of the Ricci tensor over an
  orthonormal basis ([Gud, Def. 8.32], [Lang, Def. 2.8]). Constant sectional curvature `κ` gives
  `Ric = (n - 1) κ g` and scalar curvature `n (n - 1) κ` ([Gud, Cor. 8.33]); the round unit
  `n`-sphere has `n (n - 1)`.
* The curvature-bound predicates `Manifold.SectionalCurvatureGE`,
  `Manifold.SectionalCurvatureLE`, `Manifold.RicciGE` (`Ric ≥ k g`) and
  `Manifold.ScalarCurvatureGE`, and the Einstein condition `Manifold.IsEinstein` (`Ric = λ g`).

## Implementation notes

The curvature is computed pointwise from extensions of tangent vectors to vector fields
(`CovariantDerivative.extendCurvature`). This is the textbook curvature of `(M, g)` because the
Levi-Civita connection of a `C^∞` metric is `C^∞` (its Christoffel symbols in a chart are smooth
functions of the `g_ij` and their first derivatives), so it sends the smooth extensions to smooth
vector fields, where it is uniquely determined
(`CovariantDerivative.IsLeviCivitaConnection.uniqueness`), and the curvature expression is
tensorial. Mathlib does not yet prove that regularity of its
`leviCivitaConnection` (see the TODO in `LeviCivita.lean`); until it does, this agreement is a
standard fact that is not formalized here, and `riemannCurvature` is a function of its three
tangent arguments rather than a bundled trilinear map. For the same reason `ricci` takes its trace
through the basis `Module.finBasis ℝ (TangentSpace I x)` and `scalarCurvature` takes the metric
trace through the orthonormal basis `stdOrthonormalBasis ℝ (TangentSpace I x)`; for the textbook
curvature tensor (which is trilinear) these traces do not depend on the bases.

The declarations that do not use the metric (`CovariantDerivative.extendCurvature` and
`CovariantDerivative.extendRicci`, in
`MathlibExt.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature`) apply to any covariant
derivative on `TM`, for instance the Levi-Civita connection of a pseudo-Riemannian metric; this file
only adds the Riemannian specializations and the notions that use the inner product.

All definitions assume a `C^∞` manifold and a `C^∞` metric, as in the textbooks: this is the
hypothesis under which the identification above holds (the Levi-Civita connection itself only
needs a `C²` manifold and a `C¹` metric).
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Riemann curvature endomorphism of a `C^∞` Riemannian manifold `(M, g)` at `x`:
`R(u, v) w = ∇_u ∇_v w - ∇_v ∇_u w - ∇_[u, v] w`, the curvature expression
(`CovariantDerivative.extendCurvature`) of the Levi-Civita connection on the extensions of
`u`, `v`, `w`; since the Levi-Civita connection of a `C^∞` metric is `C^∞`, this is the textbook
curvature (see the module docstring).

Sign convention of [Lang, Def. 2.1] and [Gud, Def. 8.8] (see the module docstring); the opposite
sign convention is also common. -/
def riemannCurvature (x : M) (u v w : TangentSpace I x) : TangentSpace I x :=
  (CovariantDerivative.leviCivitaConnection I M).extendCurvature x u v w

/-- The Riemann curvature endomorphism is antisymmetric in its first two arguments. -/
theorem riemannCurvature_antisymm (x : M) (u v w : TangentSpace I x) :
    riemannCurvature I x u v w = - riemannCurvature I x v u w :=
  (CovariantDerivative.leviCivitaConnection I M).extendCurvature_antisymm x u v w

/-- The sectional curvature `K(u, v) = ⟪R(u, v) v, u⟫ / (‖u‖² ‖v‖² - ⟪u, v⟫²)` of the plane
spanned by tangent vectors `u` and `v` at `x` ([Lang, Def. 2.4], [Gud, Def. 8.14]). With the sign
convention of `riemannCurvature`, the round unit sphere has `K = 1`. The denominator vanishes, and
so does the value, when `u` and `v` are linearly dependent. -/
def sectionalCurvature (x : M) (u v : TangentSpace I x) : ℝ :=
  inner ℝ (riemannCurvature I x u v v) u / (‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2)

/-- The sectional curvature formula vanishes on linearly dependent pairs `u`, `c • u`, where its
denominator `‖u‖² ‖c • u‖² - ⟪u, c • u⟫²` vanishes. -/
theorem sectionalCurvature_smul_right (x : M) (u : TangentSpace I x) (c : ℝ) :
    sectionalCurvature I x u (c • u) = 0 := by
  have h : ‖u‖ ^ 2 * ‖c • u‖ ^ 2 - inner ℝ u (c • u) ^ 2 = 0 := by
    rw [norm_smul, inner_smul_right, real_inner_self_eq_norm_sq, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  rw [sectionalCurvature, h, div_zero]

/-- The sectional curvature formula vanishes on a pair of equal vectors. -/
@[simp]
theorem sectionalCurvature_self (x : M) (u : TangentSpace I x) :
    sectionalCurvature I x u u = 0 := by
  simpa using sectionalCurvature_smul_right I x u 1

/-- The Ricci curvature `Ric(v, w)` at `x`: the trace of the endomorphism `z ↦ R(z, v) w` of
`T_x M` ([Lang, Def. 2.7]), i.e. the metric-free Ricci contraction
`CovariantDerivative.extendRicci` of the Levi-Civita connection. The unit `n`-sphere has
`Ric = (n - 1) g`. -/
def ricci (x : M) (v w : TangentSpace I x) : ℝ :=
  (CovariantDerivative.leviCivitaConnection I M).extendRicci x v w

/-- The scalar curvature at `x`: the metric trace `∑ i, Ric(eᵢ, eᵢ)` of the Ricci curvature, for
the orthonormal basis `e = stdOrthonormalBasis ℝ (TangentSpace I x)` ([Gud, Def. 8.32]). The
unit `n`-sphere has scalar curvature `n (n - 1)`. -/
def scalarCurvature (x : M) : ℝ :=
  ∑ i, ricci I x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

variable (M)

/-- `M` has sectional curvature `≥ k`: `K(u, v) ≥ k` for every point `x` and all linearly
independent `u v : T_x M`. -/
def SectionalCurvatureGE (k : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
    k ≤ sectionalCurvature I x u v

/-- `M` has sectional curvature `≤ k`: `K(u, v) ≤ k` for every point `x` and all linearly
independent `u v : T_x M`. -/
def SectionalCurvatureLE (k : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
    sectionalCurvature I x u v ≤ k

/-- `M` has Ricci curvature `≥ k`, i.e. `Ric ≥ k g`: `Ric(v, v) ≥ k ‖v‖²` for every point `x` and
every `v : T_x M`. -/
def RicciGE (k : ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), k * ‖v‖ ^ 2 ≤ ricci I x v v

/-- `M` has scalar curvature `≥ k` at every point. -/
def ScalarCurvatureGE (k : ℝ) : Prop :=
  ∀ x : M, k ≤ scalarCurvature I x

/-- The metric of `M` is Einstein: `Ric = λ g` for a constant `λ` ([Lang], Einstein manifolds).
Ricci-flat is the case `λ = 0`. -/
def IsEinstein : Prop :=
  ∃ c : ℝ, ∀ (x : M) (v w : TangentSpace I x), ricci I x v w = c * inner ℝ v w

end Manifold
