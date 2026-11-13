/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow

/-!
# First integrals of the geodesic flow

Scalar functions on the tangent bundle constant along all-time geodesic velocity curves,
in the invariant-component sense only (no regularity assumed).

## Main definitions

* `Manifold.IsFirstIntegralOfGeodesics I F`: `F` is constant along every geodesic
  velocity curve, with no continuity or smoothness hypothesis.

## Main results

* `Manifold.IsFirstIntegralOfGeodesics.const_on_flow`: constancy along the orbits
  of a geodesic flow.
* `Manifold.IsFirstIntegralOfGeodesics.const_on_unit_flow`: the unit tangent bundle version.
* Closure laws for this constancy predicate: constants, sums, differences, products,
  scalar multiples, powers, postcomposition.
* `Manifold.IsFirstIntegralOfGeodesics.exists_const_on_range`: constancy on the range.

## Implementation notes

The notion is stated through all-time geodesic velocity curves rather than through a flow
object, so it is available without existence or uniqueness of the flow. It imposes
orbitwise constancy only, with no continuity or smoothness hypothesis on `F`, and hence
records only the invariant-along-geodesics component of the textbook first-integral
notion, which additionally requires regularity. On manifolds with incomplete geodesics
even this constancy test is weaker than the textbook local-geodesic test. Under the
further assumption that every local geodesic extends to an all-time geodesic velocity
curve, as holds for a smooth geodesically complete boundaryless metric (for instance on
a closed manifold), the two constancy tests range over the same curves; this does not
upgrade the predicate to the textbook smooth notion, since postcomposing a smooth
conserved quantity with a discontinuous real indicator preserves constancy (see `.comp`)
but destroys regularity. Metric completeness alone does not suffice with boundary or
corners allowed (for instance a closed Euclidean interval is metrically complete but
admits only constant all-time geodesics). This comparison is classical and is not proved
here.

## References

* G. P. Paternain, Geodesic Flows, Ch. 1.
* K. Burns and V. Matveev, Open problems and questions about geodesics, Ergodic Theory
  Dynam. Systems 41 (2021), §10.2.
-/

@[expose] public section

open Bundle

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- A function `F` on the tangent bundle is a first integral of the geodesic flow in the
global-curve invariant-component sense: it is constant along every all-time geodesic
velocity curve, with no continuity or smoothness hypothesis on `F`. This is stated through
geodesic velocity curves so that it does not presuppose that the flow exists. It therefore
records only the invariant-along-geodesics component of the textbook first-integral
notion, which additionally requires regularity (for instance smoothness): even on a
geodesically complete manifold, postcomposing a smooth conserved quantity with a
discontinuous real indicator preserves this predicate (see `.comp`) but is not a textbook
smooth first integral. On manifolds with incomplete geodesics even the constancy test is
weaker than the textbook local-geodesic test. Under the further assumption that every
local geodesic extends to an all-time geodesic velocity curve, as holds for a smooth
geodesically complete boundaryless metric (for instance on a closed manifold), the two
constancy tests range over the same curves; metric completeness alone does not suffice
with boundary or corners allowed. This comparison is classical and is not proved here.
Chapter-level pointers: Paternain, Geodesic Flows, Ch. 1; Burns and Matveev, Open
problems and questions about geodesics, Ergodic Theory Dynam. Systems 41 (2021), §10.2. -/
def IsFirstIntegralOfGeodesics (F : TangentBundle I M → ℝ) : Prop :=
  ∀ (u : ℝ → TangentBundle I M), IsGeodesicVelocityCurve I u → ∀ s t : ℝ, F (u t) = F (u s)

/-- A first integral is constant along every orbit of a geodesic flow. -/
theorem IsFirstIntegralOfGeodesics.const_on_flow {F : TangentBundle I M → ℝ}
    {φ : ℝ → TangentBundle I M → TangentBundle I M} (hF : IsFirstIntegralOfGeodesics I F)
    (hφ : IsGeodesicFlow I φ) (t : ℝ) (v : TangentBundle I M) : F (φ t v) = F v := by
  have h : F ((fun s ↦ φ s v) t) = F ((fun s ↦ φ s v) 0) :=
    hF _ (hφ.isGeodesicVelocityCurve v) 0 t
  have h0 : φ 0 v = v := hφ.map_zero v
  simpa [h0] using h

/-- A first integral is constant along every orbit of a unit geodesic flow. -/
theorem IsFirstIntegralOfGeodesics.const_on_unit_flow {F : TangentBundle I M → ℝ}
    {φ : ℝ → unitTangentBundle I M → unitTangentBundle I M}
    (hF : IsFirstIntegralOfGeodesics I F) (hφ : IsUnitGeodesicFlow I φ) (t : ℝ)
    (v : unitTangentBundle I M) :
    F ((φ t v : TangentBundle I M)) = F (v : TangentBundle I M) := by
  have h : F ((fun s ↦ ((φ s v : TangentBundle I M))) t) =
      F ((fun s ↦ ((φ s v : TangentBundle I M))) 0) :=
    hF _ (hφ.isGeodesicVelocityCurve v) 0 t
  have h0 : ((φ 0 v : TangentBundle I M)) = (v : TangentBundle I M) :=
    congrArg Subtype.val (hφ.map_zero v)
  simpa [h0] using h

/-- Constant functions satisfy the invariant-component first-integral predicate. -/
theorem IsFirstIntegralOfGeodesics.const (c : ℝ) :
    IsFirstIntegralOfGeodesics I (fun _ : TangentBundle I M ↦ c) :=
  fun _ _ _ _ ↦ rfl

/-- The sum of two functions satisfying the constancy predicate satisfies it. -/
theorem IsFirstIntegralOfGeodesics.add {F G : TangentBundle I M → ℝ}
    (hF : IsFirstIntegralOfGeodesics I F) (hG : IsFirstIntegralOfGeodesics I G) :
    IsFirstIntegralOfGeodesics I (F + G) := by
  intro u hu s t
  simp only [Pi.add_apply, hF u hu s t, hG u hu s t]

/-- The difference of two functions satisfying the constancy predicate satisfies it. -/
theorem IsFirstIntegralOfGeodesics.sub {F G : TangentBundle I M → ℝ}
    (hF : IsFirstIntegralOfGeodesics I F) (hG : IsFirstIntegralOfGeodesics I G) :
    IsFirstIntegralOfGeodesics I (F - G) := by
  intro u hu s t
  simp only [Pi.sub_apply, hF u hu s t, hG u hu s t]

/-- The product of two functions satisfying the constancy predicate satisfies it. -/
theorem IsFirstIntegralOfGeodesics.mul {F G : TangentBundle I M → ℝ}
    (hF : IsFirstIntegralOfGeodesics I F) (hG : IsFirstIntegralOfGeodesics I G) :
    IsFirstIntegralOfGeodesics I (F * G) := by
  intro u hu s t
  simp only [Pi.mul_apply, hF u hu s t, hG u hu s t]

/-- A real scalar multiple preserves the constancy predicate. -/
theorem IsFirstIntegralOfGeodesics.const_smul {F : TangentBundle I M → ℝ}
    (hF : IsFirstIntegralOfGeodesics I F) (c : ℝ) :
    IsFirstIntegralOfGeodesics I (c • F) := by
  intro u hu s t
  simp only [Pi.smul_apply, hF u hu s t]

/-- The `n`-th power preserves the constancy predicate. -/
theorem IsFirstIntegralOfGeodesics.pow {F : TangentBundle I M → ℝ}
    (hF : IsFirstIntegralOfGeodesics I F) (n : ℕ) :
    IsFirstIntegralOfGeodesics I (fun p ↦ F p ^ n) := by
  intro u hu s t
  simp only [hF u hu s t]

/-- Postcomposition with any real function preserves the constancy-only predicate. This
uses that no regularity is assumed: a discontinuous postcomposition preserves constancy
but destroys smoothness, so a textbook smooth first-integral wrapper would have to
restrict `g` (for instance to smooth maps). -/
theorem IsFirstIntegralOfGeodesics.comp {F : TangentBundle I M → ℝ}
    (hF : IsFirstIntegralOfGeodesics I F) (g : ℝ → ℝ) :
    IsFirstIntegralOfGeodesics I (g ∘ F) := by
  intro u hu s t
  simp only [Function.comp_apply, hF u hu s t]

/-- A function satisfying the constancy predicate takes a single value on the range of
each geodesic velocity curve. -/
theorem IsFirstIntegralOfGeodesics.exists_const_on_range {F : TangentBundle I M → ℝ}
    (hF : IsFirstIntegralOfGeodesics I F) {u : ℝ → TangentBundle I M}
    (hu : IsGeodesicVelocityCurve I u) :
    ∃ c : ℝ, ∀ p ∈ Set.range u, F p = c := by
  refine ⟨F (u 0), fun p hp ↦ ?_⟩
  obtain ⟨t, rfl⟩ := hp
  exact hF u hu 0 t

end Manifold
