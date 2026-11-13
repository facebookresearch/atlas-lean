/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow
public import MathlibExt.Geometry.Manifold.Riemannian.Curvature

/-!
# Covariant derivatives along curves, Jacobi fields and conjugate points

Let `M` be a manifold modeled on `I : ModelWithCorners ℝ E H` with `E` finite-dimensional,
endowed with the installed Riemannian metric `RiemannianBundle (fun x ↦ TangentSpace I x)`,
with Levi-Civita connection `CovariantDerivative.leviCivitaConnection I M` and curvature
`Manifold.riemannCurvature I`. We define the covariant derivative along a curve, Jacobi fields
and conjugate points. Textbook sources: Lee, *Introduction to Riemannian Manifolds* (2nd ed.),
Thm. 4.24, Prop. 5.5, Ch. 10; do Carmo, *Riemannian Geometry*, Ch. 2 Prop. 2.2, Ch. 5 Def. 2.1,
Def. 3.1; Burns-Matveev, ETDS 41 (2021), Sections 4 and 7.

* `Manifold.HasCovariantDerivAlong I u V V' t`: `V' t` is the covariant derivative `D_t V` of
  the field `V` along the curve `u` at time `t`.
* `Manifold.HasCovariantDerivAlong.unique`: determinacy of `D_t V` at `t`.
* `Manifold.isGeodesicVelocityCurve_iff_hasCovariantDerivAlong`: a curve is a geodesic iff its
  velocity is parallel along it.
* `Manifold.SatisfiesJacobiEquation I u J`: `J` satisfies the Jacobi equation along `u`.
* `Manifold.IsJacobiField I u J`: `u` is a geodesic and `J` is a Jacobi field along it.
* `Manifold.AreConjugateAlong I u a b`: times `a` and `b` are conjugate along `u`.
* `Manifold.HasNoConjugatePoints I M`: `M` has no conjugate points.
* `Manifold.hasNoConjugatePoints_iff`: Burns-Matveev Section 4 characterization.

## Implementation notes

Fields along curves are dependent functions over `(u s).proj`. The covariant derivative along
a curve is characterized by metric compatibility against test fields differentiable at the point
(Mathlib has no covariant derivative along curves), with determinacy
`HasCovariantDerivAlong.unique`. No smoothness of fields is assumed (Jacobi fields are smooth by
ODE theory, not formalized). Existence and uniqueness of geodesics and Jacobi fields are
classical and NOT formalized.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- `V' t` is the covariant derivative `D_t V` of the field `V` along the curve with velocity
curve `u` at time `t`. The textbook operator `D_t` (Lee Thm. 4.24; do Carmo Ch. 2 Prop. 2.2) is
characterized here by metric compatibility `d/dt g(V, W ∘ γ) = g(D_t V, W) + g(V, ∇_{γ'} W)`
(Lee Prop. 5.5): the textbook `D_t V` satisfies it for every test field differentiable at the
point, whose values exhaust the fiber, so `V'` is determined at `t`
(`HasCovariantDerivAlong.unique`). The connection is evaluated only on fields differentiable at
the point, where it is uniquely determined
(`CovariantDerivative.IsLeviCivitaConnection.uniqueness`). The geodesic-equation field
`hasDerivAt_inner` of `Manifold.IsGeodesicVelocityCurve` is the case `V = (u ·).snd`, `V' = 0`. -/
structure HasCovariantDerivAlong (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (u : ℝ → TangentBundle I M)
    (V V' : (s : ℝ) → TangentSpace I (u s).proj) (t : ℝ) : Prop where
  /-- Velocity link: the base curve has manifold derivative at `t` equal to
  `toSpanSingleton ℝ (u t).snd` (same shape as `hasMFDerivAt_proj` of
  `Manifold.IsGeodesicVelocityCurve`). -/
  hasMFDerivAt_proj : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ (u s).proj) t
    (ContinuousLinearMap.toSpanSingleton ℝ (u t).snd)
  /-- Metric compatibility at `t` against every test field differentiable at the base point. -/
  hasDerivAt_inner : ∀ (W : Π x : M, TangentSpace I x),
    MDiffAt (T% W) (u t).proj →
      HasDerivAt (fun s ↦ inner ℝ (V s) (W (u s).proj))
        (inner ℝ (V' t) (W (u t).proj) + inner ℝ (V t)
          (CovariantDerivative.leviCivitaConnection I M W (u t).proj (u t).snd)) t

/-- Determinacy of the covariant derivative along a curve at `t`: two candidates agree. The
pairing of the difference with every admissible value vanishes; take `FiberBundle.extend`. -/
theorem HasCovariantDerivAlong.unique (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] {u : ℝ → TangentBundle I M}
    {V : (s : ℝ) → TangentSpace I (u s).proj}
    {V1 V2 : (s : ℝ) → TangentSpace I (u s).proj} {t : ℝ}
    (h1 : HasCovariantDerivAlong I u V V1 t)
    (h2 : HasCovariantDerivAlong I u V V2 t) : V1 t = V2 t := by
  have heq : ∀ (W : Π x : M, TangentSpace I x), MDiffAt (T% W) (u t).proj →
      inner ℝ (V1 t) (W (u t).proj) = inner ℝ (V2 t) (W (u t).proj) := by
    intro W hW
    have e1 : HasDerivAt (fun s ↦ inner ℝ (V s) (W (u s).proj))
        (inner ℝ (V1 t) (W (u t).proj) + inner ℝ (V t)
          (CovariantDerivative.leviCivitaConnection I M W (u t).proj (u t).snd)) t :=
      h1.hasDerivAt_inner W hW
    have e2 : HasDerivAt (fun s ↦ inner ℝ (V s) (W (u s).proj))
        (inner ℝ (V2 t) (W (u t).proj) + inner ℝ (V t)
          (CovariantDerivative.leviCivitaConnection I M W (u t).proj (u t).snd)) t :=
      h2.hasDerivAt_inner W hW
    have hEq : inner ℝ (V1 t) (W (u t).proj) + inner ℝ (V t)
          (CovariantDerivative.leviCivitaConnection I M W (u t).proj (u t).snd) =
        inner ℝ (V2 t) (W (u t).proj) + inner ℝ (V t)
          (CovariantDerivative.leviCivitaConnection I M W (u t).proj (u t).snd) :=
      HasDerivAt.unique e1 e2
    linear_combination hEq
  have hW : MDiffAt (T% (FiberBundle.extend E (V1 t - V2 t))) (u t).proj :=
    FiberBundle.mdifferentiableAt_extend I E (V1 t - V2 t)
  have hPair : inner ℝ (V1 t) (V1 t - V2 t) = inner ℝ (V2 t) (V1 t - V2 t) := by
    have h : inner ℝ (V1 t) (FiberBundle.extend E (V1 t - V2 t) (u t).proj) =
        inner ℝ (V2 t) (FiberBundle.extend E (V1 t - V2 t) (u t).proj) :=
      heq _ hW
    rwa [FiberBundle.extend_apply_self] at h
  have hZero : inner ℝ (V1 t - V2 t) (V1 t - V2 t) = 0 := by
    rw [inner_sub_left, hPair, sub_self]
  have hSub : V1 t - V2 t = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hZero
  exact sub_eq_zero.mp hSub

/-- A curve is a geodesic iff its velocity is parallel along it (`D_t γ' = 0`). Both directions;
the fields correspond one to one with those of `Manifold.IsGeodesicVelocityCurve` for
`V = (u ·).snd`, `V' = 0`. -/
theorem isGeodesicVelocityCurve_iff_hasCovariantDerivAlong (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (u : ℝ → TangentBundle I M) :
    IsGeodesicVelocityCurve I u ↔
      ∀ t : ℝ, HasCovariantDerivAlong I u (fun s ↦ (u s).snd) (fun _ ↦ 0) t := by
  constructor
  · intro h t
    refine ⟨h.hasMFDerivAt_proj t, fun W hW => ?_⟩
    simpa [inner_zero_left] using h.hasDerivAt_inner t W hW
  · intro h
    refine ⟨fun t => (h t).hasMFDerivAt_proj, fun t W hW => ?_⟩
    simpa [inner_zero_left] using (h t).hasDerivAt_inner W hW

/-- `J` satisfies the Jacobi equation along the curve with velocity curve `u`: there is `J'`
with, at every time, `J'` the covariant derivative of `J` and `-R(J, γ')γ'` that of `J'` (Lee
Ch. 10, sign convention of `Manifold.riemannCurvature`; do Carmo Ch. 5 Def. 2.1 uses the
opposite curvature sign, so his `R(γ', J)γ'` is our `R(J, γ')γ'`). `J'` is `D_t J`, unique by
`Manifold.HasCovariantDerivAlong.unique`. The curve need not be a geodesic; `IsJacobiField`
adds that requirement. The curvature caveat documented for `Manifold.riemannCurvature` in
`MathlibExt.Geometry.Manifold.Riemannian.Curvature` (Mathlib's connection not yet proved
smooth) applies. -/
def SatisfiesJacobiEquation (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (u : ℝ → TangentBundle I M)
    (J : (s : ℝ) → TangentSpace I (u s).proj) : Prop :=
  ∃ J' : (s : ℝ) → TangentSpace I (u s).proj, ∀ t : ℝ,
    HasCovariantDerivAlong I u J J' t ∧
      HasCovariantDerivAlong I u J'
        (fun s ↦ -riemannCurvature I (u s).proj (J s) (u s).snd (u s).snd) t

/-- `J` is a Jacobi field along the geodesic with velocity curve `u`: `u` is a geodesic velocity
curve and `J` satisfies the Jacobi equation along it (Lee Ch. 10; do Carmo Ch. 5 Def. 2.1). -/
def IsJacobiField (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (u : ℝ → TangentBundle I M)
    (J : (s : ℝ) → TangentSpace I (u s).proj) : Prop :=
  IsGeodesicVelocityCurve I u ∧ SatisfiesJacobiEquation I u J

/-- Times `a` and `b` are conjugate along the geodesic velocity curve `u`: `u` is a geodesic,
`a ≠ b`, and some Jacobi field vanishes at `a` and `b` but not identically (do Carmo Ch. 5
Def. 3.1; Lee Ch. 10). Thus `γ(a)` and `γ(b)` are conjugate along `γ`; times may be negative
and in either order. -/
def AreConjugateAlong (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (u : ℝ → TangentBundle I M) (a b : ℝ) : Prop :=
  IsGeodesicVelocityCurve I u ∧ a ≠ b ∧
    ∃ J : (s : ℝ) → TangentSpace I (u s).proj,
      SatisfiesJacobiEquation I u J ∧ J a = 0 ∧ J b = 0 ∧ ∃ s : ℝ, J s ≠ 0

/-- `M` has no conjugate points: no geodesic velocity curve has conjugate times. The hypothesis
"without conjugate points" of Burns-Matveev (ETDS 41 (2021)) Section 7, characterized in
Section 4 as "a (non trivial) Jacobi field can vanish at most once" (`hasNoConjugatePoints_iff`).
NOT defined as "every geodesic is minimizing" (equivalent only on complete simply connected
manifolds). Geodesics are defined on all of `ℝ`, so on a complete boundaryless manifold this is
the textbook notion, elsewhere it only tests geodesics defined on `ℝ`. -/
def HasNoConjugatePoints (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (u : ℝ → TangentBundle I M) (a b : ℝ), ¬ AreConjugateAlong I u a b

/-- Burns-Matveev Section 4 characterization: no conjugate points iff every Jacobi field along a
geodesic that vanishes at two distinct times is identically zero. -/
theorem hasNoConjugatePoints_iff (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] :
    HasNoConjugatePoints I M ↔
      ∀ (u : ℝ → TangentBundle I M) (J : (s : ℝ) → TangentSpace I (u s).proj)
        (a b : ℝ), IsGeodesicVelocityCurve I u → SatisfiesJacobiEquation I u J →
        a ≠ b → J a = 0 → J b = 0 → ∀ s : ℝ, J s = 0 := by
  constructor
  · intro h u J a b hgeo hJ hab ha hb s
    by_contra hs
    exact h u a b ⟨hgeo, hab, J, hJ, ha, hb, s, hs⟩
  · intro h u a b hconj
    obtain ⟨hgeo, hab, J, hJ, ha, hb, s, hs⟩ := hconj
    exact hs (h u J a b hgeo hJ hab ha hb s)

end Manifold
