/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Projectively equivalent Finsler metrics on hyperbolic surfaces (AIM Geodesics, Question 10.1.3)

AIM workshop *Geodesics* (2010) problem list, Question 10.1.3 (also Burns–Matveev, *Open problems
and questions about geodesics*, Question 10.1.3): if every unparameterized geodesic of a Finsler
metric `F₁` on a closed surface of genus at least two is a geodesic of a Finsler metric `F₂`, must
`F₁` be a constant multiple of `F₂` plus a closed 1-form? The list asks the same for closed
manifolds carrying a hyperbolic metric. J. Lang (J. Topol. Anal. 14 (2022)) proved the answer is
yes for real-analytic metrics on surfaces of negative Euler characteristic and no for smooth ones,
by smooth projectively equivalent metrics on every closed surface that are not so related.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.Manifold.Finsler
public import MathlibExt.Geometry.Manifold.Riemannian.Curvature
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace MathlibExt.Geometry.FinslerProjectiveRigidityHyperbolicSurfaceAIMGeometryProblem268Wanted

/-!
Source: AIM workshop Geodesics (Tianjin, 2010), problem list by K. Burns and V. S. Matveev,
Question 10.1.3, https://aimath.org/pastworkshops/geodesicsproblems.pdf; the same question is
Question 10.1.3 of K. Burns and V. S. Matveev, Open problems and questions about geodesics,
Ergodic Theory Dynam. Systems 41 (2021), 641-684. UnsolvedMath record UM-20001930
(`AIM-GEOMETRY-0268`), dataset ulamai/UnsolvedMath v1.8.0.

Reading choices. A closed surface is a compact connected Hausdorff `C^∞` manifold without boundary
modelled on `𝓡 2`. Mathlib has no genus or orientation, so "genus at least two" is replaced by the
list's own second formulation, "closed manifolds that can carry a hyperbolic metric", in dimension
two: the surface carries a `C^∞` Riemannian metric of constant sectional curvature `-1`
(`Manifold.sectionalCurvature`, convention: the round unit sphere has curvature `1`). Orientable
closed surfaces carry such a metric exactly when their genus is at least two; the class also
contains the non-orientable closed surfaces of negative Euler characteristic, and Lang's examples
cover every closed surface.

Finsler metrics are `Manifold.FinslerMetric (𝓡 2) M` (`C^∞`, strongly convex, possibly
irreversible). An unparameterized `F₁`-geodesic is an `F₂`-geodesic when an orientation-preserving
reparametrization of it (an order isomorphism `ℝ ≃o ℝ`) is an `F₂`-geodesic; geodesics are the
layer's forward-distance metric geodesics, which on a closed boundaryless surface are the
geodesics of the smooth metric, and on a compact surface every geodesic segment extends to all
times. A closed 1-form is a function `β` on the tangent bundle that near every point is the
differential of a `C^∞` function (closed forms are the locally exact ones, by the Poincaré lemma).
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

/-- The Euclidean plane, the model space of surfaces. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- `M` carries a hyperbolic metric: a `C^∞` Riemannian metric of constant sectional curvature
`-1`. -/
def CarriesHyperbolicMetric (M : Type) [TopologicalSpace M] [ChartedSpace E2 M]
    [IsManifold (𝓡 2) ∞ M] : Prop :=
  ∃ g : ContMDiffRiemannianMetric (𝓡 2) ∞ E2 (fun x : M ↦ TangentSpace (𝓡 2) x),
    letI : RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 2) x) := ⟨g.toRiemannianMetric⟩
    ∀ (x : M) (u v : TangentSpace (𝓡 2) x), LinearIndependent ℝ ![u, v] →
      sectionalCurvature (𝓡 2) x u v = -1

/-- `β : TM → ℝ` is a closed 1-form: near every point it is the differential of a `C^∞`
function. -/
def IsClosedOneForm {M : Type} [TopologicalSpace M] [ChartedSpace E2 M]
    (β : TangentBundle (𝓡 2) M → ℝ) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ f : M → ℝ, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ f U ∧
    ∀ y ∈ U, ∀ w : TangentSpace (𝓡 2) y, β ⟨y, w⟩ = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y w

/-- Every unparameterized geodesic of `F₁` is a geodesic of `F₂`: an orientation-preserving
reparametrization of each `F₁`-geodesic is an `F₂`-geodesic. -/
def GeodesicsAreGeodesics {M : Type} [TopologicalSpace M] [ChartedSpace E2 M]
    [IsManifold (𝓡 2) ∞ M] (F₁ F₂ : FinslerMetric (𝓡 2) M) : Prop :=
  ∀ γ : ℝ → M, F₁.IsGeodesic γ → ∃ φ : ℝ ≃o ℝ, F₂.IsGeodesic (γ ∘ φ)

/-- Question 10.1.3, in the list's formulation for closed surfaces carrying a hyperbolic metric:
if every unparameterized geodesic of a Finsler metric `F₁` is a geodesic of a Finsler metric `F₂`,
then `F₁ = c F₂ + β` for a constant `c > 0` and a closed 1-form `β`. -/
def projectiveRigidity : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace E2 M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M], CarriesHyperbolicMetric M →
    ∀ F₁ F₂ : FinslerMetric (𝓡 2) M, GeodesicsAreGeodesics F₁ F₂ →
      ∃ c : ℝ, 0 < c ∧ ∃ β : TangentBundle (𝓡 2) M → ℝ, IsClosedOneForm β ∧
        ∀ v : TangentBundle (𝓡 2) M, F₁ v = c * F₂ v + β v

/--
Resolved false: on every closed surface there are smooth Finsler metrics with the same
unparameterized oriented geodesics that are not related by scaling and addition of a closed 1-form
(J. Lang, Example 1); in particular on a closed surface of genus two, which carries a hyperbolic
metric. Lang's Theorem 1 shows that real-analytic projectively equivalent metrics on a surface of
negative Euler characteristic are so related, and Example 1 that real-analyticity is necessary:
Crofton-type reversible metrics on `S²`, projectively equivalent to the round metric and equal to
it over an open set `V`, glued to handles attached in `V`. Source: AIM workshop Geodesics (2010)
problem list (K. Burns and V. S. Matveev), Question 10.1.3,
https://aimath.org/pastworkshops/geodesicsproblems.pdf; resolution: J. Lang, Projectively
equivalent Finsler metrics on surfaces of negative Euler characteristic, J. Topol. Anal. 14 (2022),
no. 1, 287-296 (arXiv:1908.02701), §1, Theorem 1 and Example 1 ("On any closed surface there are
(non real-analytic) projectively equivalent metrics that are not related by scaling and addition
of a closed 1-form"), https://doi.org/10.1142/S1793525320500491.
-/
public theorem_wanted projectiveRigidity_refuted : ¬ projectiveRigidity

end MathlibExt.Geometry.FinslerProjectiveRigidityHyperbolicSurfaceAIMGeometryProblem268Wanted
