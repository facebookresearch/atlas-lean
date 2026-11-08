/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Geodesic flow of a Riemannian manifold

Let `M` be a manifold modeled on `I : ModelWithCorners ℝ E H` with `E` finite-dimensional,
endowed with a Riemannian metric `g` given by the installed instance
`RiemannianBundle (fun x : M ↦ TangentSpace I x)`, and let `∇` be its Levi-Civita connection
`CovariantDerivative.leviCivitaConnection I M`. We define the unit tangent bundle and the
geodesic flow of `(M, g)`. References with the same conventions: do Carmo, *Riemannian
Geometry*, Ch. 3; Lee, *Introduction to Riemannian Manifolds* (2nd ed.), Ch. 4-5; Paternain,
*Geodesic Flows*, Ch. 1.

* `Manifold.unitTangentBundle I M`: the unit tangent bundle `SM`, the tangent vectors of
  norm `1` for the installed metric, as a set of `TangentBundle I M`.
* `Manifold.IsGeodesicVelocityCurve I u`: `u : ℝ → TangentBundle I M` is the velocity curve
  `t ↦ γ'(t)` of a geodesic `γ` of `g`.
* `Manifold.IsGeodesicFlow I φ`: `φ : ℝ → TangentBundle I M → TangentBundle I M` is the
  geodesic flow of `g` on the tangent bundle.
* `Manifold.IsUnitGeodesicFlow I φ`: `φ : ℝ → SM → SM` is the geodesic flow on `SM`.

## Implementation notes

The predicates below are deliberately stated in a broader low-regularity setting: any `C^2`
manifold with a `C^1` metric, with boundary or corners allowed, where they remain meaningful
as characterizations of geodesic velocity curves. The intended consumers (Burns-Matveev rows)
use a `C^∞` metric on a closed boundaryless manifold.

The flow is characterized, not constructed. For a `C^∞` Riemannian metric on a boundaryless
manifold, uniqueness of geodesics with given initial velocity gives at most one flow
satisfying `IsGeodesicFlow` or `IsUnitGeodesicFlow`; if the metric is in addition complete
(for instance on a closed manifold, the source setting of Burns-Matveev) the global flow
exists. Both facts are classical and NOT formalized here (uniqueness needs smoothness of
Mathlib's Levi-Civita connection in charts, a Mathlib TODO). Under the file's general `C^1`
hypotheses, with boundary allowed, neither fact is claimed: uniqueness of geodesics with
given initial velocity can fail for a merely `C^1` metric, whose Christoffel symbols are only
continuous, and global existence can fail on a manifold with boundary or for an incomplete
metric.

No continuity, smoothness or conservation of speed is assumed: these are classical
properties of the geodesic flow of a `C^∞` metric on a boundaryless manifold (complete, for
the global flow), not hypotheses of the predicates, and this file does not claim them in its
general setting. The group law is assumed: it is the `map_add` field of both flow structures.

Usage: a property `P` of the geodesic flow of a complete metric is stated as
`∀ φ, IsUnitGeodesicFlow I φ → P φ` (equivalently, given existence and uniqueness,
`∃ φ, IsUnitGeodesicFlow I φ ∧ P φ`), and `φ` may be a Mathlib
`Flow ℝ (unitTangentBundle I M)` coerced to a function when `P` uses Mathlib flow notions.

A quantified metric `g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)` is
installed with `letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩`.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- The unit tangent bundle `SM` of a Riemannian manifold `(M, g)`: the tangent vectors whose
norm for the installed metric on their fiber is `1`, as a set of `TangentBundle I M` with the
subspace topology. Source: Burns-Matveev, ETDS 41 (2021), §1 ("the unit tangent bundle ... is
denoted by SM"). -/
def unitTangentBundle (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] :
    Set (TangentBundle I M) :=
  {p : TangentBundle I M | ‖p.snd‖ = 1}

/-- `u : ℝ → TangentBundle I M` is the velocity curve `t ↦ γ'(t)` of a geodesic `γ` of `g`,
with `γ = fun t ↦ (u t).proj`. The textbook definition is `∇_{γ'} γ' = 0`; Mathlib has no
covariant derivative along curves, so the geodesic equation is stated in weak form: pairing
with every vector field `W` differentiable at the base point. Under the structure's own
hypotheses the two fields force the needed regularity: testing the geodesic equation against
the coordinate vector fields of a chart shows that the coordinates of the velocity are
differentiable, with derivative given by the geodesic equation, which is continuous since the
metric is `C^1`; so the base curve is `C^2` in charts. For such curves the weak form is
equivalent to `∇_{γ'} γ' = 0` by metric compatibility along `γ`
(`d/dt g(γ', W∘γ) = g(∇_{γ'}γ', W) + g(γ', ∇_{γ'}W)`, and the values `W(γ t)` exhaust the
tangent space); in a chart it is the Euler-Lagrange equation
`g(γ'', w) + (∂_{γ'} g)(γ', w) - ½ (∂_w g)(γ', γ') = 0`. The connection is applied only to
fields differentiable at the point, where Mathlib's connection is uniquely determined
(`CovariantDerivative.IsLeviCivitaConnection.uniqueness`) by the Koszul formula
(`leviCivitaConnection_apply_inner`) and equals the textbook value. No smoothness of the curve
beyond what the two fields assert is assumed. -/
structure IsGeodesicVelocityCurve (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (u : ℝ → TangentBundle I M) : Prop where
  /-- Velocity link: the base curve `fun s ↦ (u s).proj` has manifold derivative at `t`
  equal to `ContinuousLinearMap.toSpanSingleton ℝ (u t).snd`, i.e. its velocity at `t` is the
  fiber component of `u t`. -/
  hasMFDerivAt_proj : ∀ (t : ℝ), HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ (u s).proj) t
    (ContinuousLinearMap.toSpanSingleton ℝ (u t).snd)
  /-- Geodesic equation, weak form: for every vector field `W` differentiable at the base point,
  the real function `s ↦ ⟪(u s).snd, W (u s).proj⟫` has derivative at `t` equal to
  `⟪(u t).snd, ∇_{(u t).snd} W⟫`, with `∇ = CovariantDerivative.leviCivitaConnection I M`. -/
  hasDerivAt_inner : ∀ (t : ℝ) (W : Π x : M, TangentSpace I x),
    MDiffAt (T% W) (u t).proj →
      HasDerivAt (fun s ↦ inner ℝ (u s).snd (W (u s).proj))
        (inner ℝ (u t).snd
          (CovariantDerivative.leviCivitaConnection I M W (u t).proj (u t).snd)) t

/-- `φ : ℝ → TangentBundle I M → TangentBundle I M` is the geodesic flow of `g` on the tangent
bundle: `φ 0 v = v` for every `v`, the flow law `φ (t + s) v = φ t (φ s v)` holds, and every
orbit `fun t ↦ φ t v` is a geodesic velocity curve, so `φ t v = γ̇_v(t)` where `γ_v` is the
geodesic with initial velocity `v`. The flow is characterized, not constructed; for a `C^∞`
metric on a boundaryless manifold (complete, for the global flow) existence and uniqueness are
classical and not formalized here. The group law is a field; no continuity, smoothness or
conservation of speed is assumed: those are classical properties in that smooth setting only,
not claimed in the file's general setting. -/
structure IsGeodesicFlow (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (φ : ℝ → TangentBundle I M → TangentBundle I M) : Prop where
  /-- The flow at time `0` is the identity: `φ 0 v = v` for every `v`. -/
  map_zero : ∀ (v : TangentBundle I M), φ 0 v = v
  /-- Flow law: `φ (t + s) v = φ t (φ s v)` for all times `t s` and every `v`. -/
  map_add : ∀ (t s : ℝ) (v : TangentBundle I M), φ (t + s) v = φ t (φ s v)
  /-- Every orbit `fun t ↦ φ t v` is a geodesic velocity curve. -/
  isGeodesicVelocityCurve : ∀ (v : TangentBundle I M),
    IsGeodesicVelocityCurve I (fun t ↦ φ t v)

/-- `φ : ℝ → SM → SM` is the geodesic flow `φ_t : SM → SM` of Burns-Matveev §1 ("φ_t is the
geodesic flow on SM; the geodesic defined by `v ∈ SM` is `γ_v`, parametrized by arclength").
`φ 0 v = v` for every `v`, the flow law `φ (t + s) v = φ t (φ s v)` holds, and every orbit
`fun t ↦ (φ t v : TangentBundle I M)` is a geodesic velocity curve. The flow is characterized,
not constructed; for a `C^∞` metric on a boundaryless manifold (complete, for the global flow)
existence and uniqueness are classical and not formalized here. The group law is a field; no
continuity, smoothness or conservation of speed is assumed: those are classical properties in
that smooth setting only, not claimed in the file's general setting. -/
structure IsUnitGeodesicFlow (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E]
    (φ : ℝ → unitTangentBundle I M → unitTangentBundle I M) : Prop where
  /-- The flow at time `0` is the identity: `φ 0 v = v` for every `v`. -/
  map_zero : ∀ (v : unitTangentBundle I M), φ 0 v = v
  /-- Flow law: `φ (t + s) v = φ t (φ s v)` for all times `t s` and every `v`. -/
  map_add : ∀ (t s : ℝ) (v : unitTangentBundle I M), φ (t + s) v = φ t (φ s v)
  /-- Every orbit `fun t ↦ (φ t v : TangentBundle I M)` is a geodesic velocity curve. -/
  isGeodesicVelocityCurve : ∀ (v : unitTangentBundle I M),
    IsGeodesicVelocityCurve I (fun t ↦ (φ t v : TangentBundle I M))

end Manifold
