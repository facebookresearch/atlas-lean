/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Sets with smooth boundary in boundaryless manifolds

A set `Ω` of a manifold `M`, charted on the model space of a boundaryless model with corners
`I`, has smooth boundary if `Ω` is open and every frontier point `p` admits a local defining
function: a real-valued function `ρ`, smooth in the manifold sense on an open neighborhood `U`
of `p`, with `ρ p = 0` and nonzero manifold differential at `p`, such that `Ω ∩ U` is exactly
the strict sublevel set `{ρ < 0}` in `U`. Near each boundary point, `Ω` is thus the strict
sublevel set of a local smooth function with regular value `0`.

The model must be boundaryless (`[I.Boundaryless]`, as for the submersion results in
`MathlibExt.Geometry.Manifold.SubmersionComp`). On a model with boundary or corners, a
nonzero manifold differential is not a regularity condition at points of the model's
boundary. On the closed half-plane `EuclideanHalfSpace 2`, the set `Ω = {0}ᶜ` is open and
equals `{ρ < 0}` for the smooth function `ρ x = -(x₀ + x₁²)`, which vanishes at `0` with
differential `-dx₀ ≠ 0` there, yet the frontier of `Ω` is the single point `0`, not a
hypersurface. For a boundaryless model the chart images are open, so the condition is the
usual regular-value condition.

## Main declarations

* `Manifold.IsLocalDefiningFunction I Ω p U ρ`: `ρ` defines `Ω` near `p` on `U`.
* `Manifold.HasSmoothBoundary I Ω`: `Ω` is open with a local defining function at every
  frontier point.
* `Manifold.HasSmoothBoundary.intro`, `Manifold.HasSmoothBoundary.isOpen` and
  `Manifold.HasSmoothBoundary.exists_isLocalDefiningFunction`: introduction and elimination.
* `Manifold.HasSmoothBoundary.of_isClopen`, `Manifold.hasSmoothBoundary_empty` and
  `Manifold.hasSmoothBoundary_univ`: sets with empty frontier.

Sources and relation to the literature:
- Lamboley–Sicbaldi (arXiv:1907.08159), on regularity of Faber–Krahn minimizers in a compact
  Riemannian manifold without boundary: the regular part of the boundary "is a smooth
  hypersurface in M (C∞ if M is C∞, analytic if M is analytic)". The predicate here is this
  notion of smooth boundary for domains on manifolds.
- The repository's Euclidean precedent `EuclideanGeometry.IsLocalDefiningFunction`:
  a local defining function with nonzero differential, of class `C²`, describing a
  hypersurface as a zero set. The new predicate lives in manifolds rather than in a
  normed space, requires `C^∞` rather than `C²`, and describes a domain as a strict
  sublevel set rather than a hypersurface as a zero set.
- No equivalence with other characterizations (local graphs, regular domains, or a
  manifold-with-boundary structure on the closure) is proved here.
-/

@[expose] public section

open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `ρ` is a local defining function of `Ω` at `p` on `U`: `U` is an open neighborhood of `p`
on which `ρ` is manifold-smooth, `ρ p = 0`, the manifold differential of `ρ` at `p` is nonzero,
and a point of `U` lies in `Ω` exactly when `ρ` is negative there. -/
structure IsLocalDefiningFunction (I : ModelWithCorners ℝ E H) [I.Boundaryless] (Ω : Set M)
    (p : M) (U : Set M) (ρ : M → ℝ) : Prop where
  /-- The domain of the defining function is open. -/
  isOpen : IsOpen U
  /-- The domain contains the base point. -/
  mem : p ∈ U
  /-- The defining function is smooth on its domain. -/
  contMDiffOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ U
  /-- The defining function vanishes at the base point. -/
  apply_eq_zero : ρ p = 0
  /-- The manifold differential at the base point is nonzero. -/
  mfderiv_ne_zero : mfderiv I 𝓘(ℝ, ℝ) ρ p ≠ 0
  /-- On the domain, `Ω` is the strict sublevel set `{ρ < 0}`. -/
  mem_iff : ∀ x ∈ U, x ∈ Ω ↔ ρ x < 0

/-- A set `Ω` of a manifold `M` modeled on a boundaryless model `I` has smooth boundary if
`Ω` is open and every frontier point `p` has a local defining function: near `p`, `Ω` is the
strict sublevel set `{ρ < 0}` of a manifold-smooth real function `ρ` with `ρ p = 0` and
nonzero manifold differential at `p`. -/
def HasSmoothBoundary (I : ModelWithCorners ℝ E H) [I.Boundaryless] (Ω : Set M) : Prop :=
  IsOpen Ω ∧ ∀ p ∈ frontier Ω, ∃ (U : Set M) (ρ : M → ℝ), IsLocalDefiningFunction I Ω p U ρ

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless] {Ω : Set M}

namespace HasSmoothBoundary

/-- An open set with a local defining function at every frontier point has smooth boundary. -/
theorem intro (hΩ : IsOpen Ω)
    (hρ : ∀ p ∈ frontier Ω, ∃ (U : Set M) (ρ : M → ℝ), IsLocalDefiningFunction I Ω p U ρ) :
    HasSmoothBoundary I Ω :=
  ⟨hΩ, hρ⟩

/-- A set with smooth boundary is open. -/
theorem isOpen (h : HasSmoothBoundary I Ω) : IsOpen Ω :=
  h.1

/-- A set with smooth boundary has a local defining function at each frontier point. -/
theorem exists_isLocalDefiningFunction (h : HasSmoothBoundary I Ω) {p : M}
    (hp : p ∈ frontier Ω) : ∃ (U : Set M) (ρ : M → ℝ), IsLocalDefiningFunction I Ω p U ρ :=
  h.2 p hp

/-- A clopen set has empty frontier, so it has smooth boundary. -/
theorem of_isClopen (hΩ : IsClopen Ω) : HasSmoothBoundary I Ω :=
  intro hΩ.isOpen fun p hp => by
    rw [hΩ.frontier_eq] at hp
    exact absurd hp (Set.notMem_empty p)

end HasSmoothBoundary

/-- The empty set has smooth boundary. -/
theorem hasSmoothBoundary_empty : HasSmoothBoundary I (∅ : Set M) :=
  HasSmoothBoundary.of_isClopen isClopen_empty

/-- The whole manifold has smooth boundary. -/
theorem hasSmoothBoundary_univ : HasSmoothBoundary I (Set.univ : Set M) :=
  HasSmoothBoundary.of_isClopen isClopen_univ

end Manifold
