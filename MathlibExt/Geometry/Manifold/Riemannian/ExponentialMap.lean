/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow
public import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Riemannian exponential map, injectivity radius and injectivity domain

Let `M` be a manifold modeled on `I : ModelWithCorners ℝ E H` with `E` finite-dimensional,
endowed with a Riemannian metric given by the installed instance
`RiemannianBundle (fun x : M ↦ TangentSpace I x)`. We define the Riemannian exponential map
predicate and the injectivity radius and domain. References: do Carmo, *Riemannian Geometry*,
Ch. 3; Lee, *Introduction to Riemannian Manifolds* (2nd ed.), Ch. 5 and Ch. 6;
Figalli-Gallouet-Rifford, SIAM J. Math. Anal. 47 (2015) (injectivity domain);
Villani, Oberwolfach Report 31/2008 (tangent injectivity locus).

* `Manifold.IsRiemannianExp I exp`: `exp` is the Riemannian exponential map.
* `Manifold.injectivityRadiusAt I exp x`: injectivity radius at `x`.
* `Manifold.injectivityRadius I exp`: the global injectivity radius.
* `Manifold.injectivityDomain I exp x`: the injectivity domain at `x`.

## Implementation notes

The exponential map is characterized, not constructed: `IsRiemannianExp` quantifies over every
base point, tangent vector and real time of each ray, using `Manifold.IsGeodesicVelocityCurve`.
The radius and domain take the map `exp` as an explicit argument. Classical existence and
uniqueness of geodesics and the exponential map are NOT formalized; consumers assume smooth
boundaryless complete manifolds, where exactly one map satisfies the predicate.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)

/-- `exp` is the Riemannian exponential map: `exp_x v = γ_v (1)` and `t ↦ exp_x (t • v)` is the
geodesic with initial velocity `v` (do Carmo Ch. 3; Lee Ch. 5). Characterized, not constructed:
no choice, no fallback map. For a smooth metric on a boundaryless manifold, geodesics with given
initial velocity are unique and extend to `ℝ` iff the manifold is complete, and then exactly one
map satisfies this predicate; on an incomplete manifold, or one with nonempty boundary, none does,
so `∀ exp, IsRiemannianExp I exp → P exp` is vacuous there and consumers assume smooth
boundaryless complete manifolds. For a `C^1` metric geodesics need not be unique, hence the
smooth context. -/
def IsRiemannianExp [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] (exp : (x : M) → TangentSpace I x → M) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), ∃ u : ℝ → TangentBundle I M,
    IsGeodesicVelocityCurve I u ∧ u 0 = ⟨x, v⟩ ∧ ∀ t : ℝ, exp x (t • v) = (u t).proj

/-- The exponential map sends `0` to the base point: if `IsRiemannianExp I exp` then `exp x 0 = x`
for every `x`. This is a forced consequence of the ray clause (the zero ray is constant). -/
theorem IsRiemannianExp.apply_zero [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] {exp : (x : M) → TangentSpace I x → M}
    (h : IsRiemannianExp I exp) (x : M) : exp x 0 = x := by
  obtain ⟨u, _, hu0, hray⟩ := h x (0 : TangentSpace I x)
  have h0 : exp x ((0 : ℝ) • (0 : TangentSpace I x)) = (u 0).proj := hray 0
  rw [smul_zero] at h0
  rw [hu0] at h0
  simpa using h0

/-- The injectivity radius at `x` (Lee Ch. 6): the supremum of the radii `a` such that `exp_x`
is a diffeomorphism from the open ball of radius `a` in `T_x M` onto its image. This is
implemented as injective plus a smooth local diffeomorphism on the ball, equivalent on an open
set. `⊤` is allowed (Euclidean space); meaningful for `exp` with `IsRiemannianExp I exp`. -/
def injectivityRadiusAt [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (exp : (x : M) → TangentSpace I x → M) (x : M) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | Set.InjOn (exp x) (Metric.eball 0 a) ∧
    IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace I x) I ∞ (exp x) (Metric.eball 0 a)}

/-- The injectivity radius of `M` (Lee Ch. 6): `inj(M) = inf_x inj(x)`, the infimum over `x : M`
of `injectivityRadiusAt I exp x`. -/
def injectivityRadius [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (exp : (x : M) → TangentSpace I x → M) : ℝ≥0∞ :=
  ⨅ x : M, injectivityRadiusAt I exp x

/-- The injectivity domain `I(x)` at `x` (Figalli-Gallouet-Rifford, SIAM J. Math. Anal. 47
(2015), introduction): `v` with `∃ t > 1, d(x, exp_x (t • v)) = ‖t • v‖`, `d` the Riemannian
distance of the installed metric. Villani calls these sets "tangent injectivity loci"
(Oberwolfach Report 31/2008). -/
def injectivityDomain [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (exp : (x : M) → TangentSpace I x → M) (x : M) : Set (TangentSpace I x) :=
  {v | ∃ t : ℝ, 1 < t ∧ riemannianEDist I x (exp x (t • v)) = ENNReal.ofReal ‖t • v‖}

/-- `0` lies in the injectivity domain at `x` whenever `IsRiemannianExp I exp` holds. -/
theorem zero_mem_injectivityDomain [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [FiniteDimensional ℝ E] {exp : (x : M) → TangentSpace I x → M}
    (h : IsRiemannianExp I exp) (x : M) :
    (0 : TangentSpace I x) ∈ injectivityDomain I exp x := by
  have hexp : exp x 0 = x := IsRiemannianExp.apply_zero I h x
  refine ⟨(2 : ℝ), one_lt_two, ?_⟩
  have hsmul : (2 : ℝ) • (0 : TangentSpace I x) = 0 := smul_zero 2
  rw [hsmul, hexp, riemannianEDist_self, norm_zero, ENNReal.ofReal_zero]

end Manifold
