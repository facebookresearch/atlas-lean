/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Circumscribing polygons of disjoint segments (Mirzaian; Ghosh-Goswami Conjecture 16)

S. K. Ghosh and P. P. Goswami, Unsolved problems in visibility graphs of points, segments and
polygons, Conjecture 16 (Mirzaian): every segment visibility graph `G` contains a Hamiltonian cycle
`C` that corresponds to the boundary of a circumscribing polygon in the embedded segment visibility
graph `G'`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import WantedExt.Geometry.SegmentVisibilityShared

@[expose] public section

namespace MathlibExt.Geometry.CircumscribingPolygonAMR131Problem0014Wanted

/-!
Source: S. K. Ghosh and P. P. Goswami, Unsolved problems in visibility graphs of points, segments
and polygons, ACM Comput. Surv. 46 (2013), arXiv:1012.5187, Conjecture 16 (A. Mirzaian).
UnsolvedMath record UM-00800545 (`AMR-131-0014`), dataset ulamai/UnsolvedMath v1.8.0.

Segments are given by an endpoint family `e : Fin (2m) → ℝ × ℝ`, segment `k` joining `e (2k)` and `e
(2k + 1)`; they are nondegenerate and pairwise disjoint (closed segments). Two endpoints are
adjacent when they bound the same segment or the open segment joining them meets no segment, which
is the source's visibility (no passing through another endpoint, no grazing along a segment). A
Hamiltonian cycle is a cyclic order `π` of the `2m` endpoints with consecutive endpoints adjacent;
the definitions repeat those of the round-1 OpenConjectures entries for the same list
(`AMR131Problem15`, `AMR131Problem36`). The hypothesis that the segments are not all collinear is
Hoffmann and Tóth's: for collinear segments the visibility graph is a path, with no Hamiltonian
cycle, so the source's literal 'every segment visibility graph' fails for them (and for a single
segment). A circumscribing polygon (Mirzaian; the source's Section 3) is a Hamiltonian polygon `Q`
such that no segment lies to the exterior of `Q`: each segment is an edge of `Q` or an internal
chord, i.e. its relative interior lies in the interior of the region of `Q`. With the hypothesis the
refuted claim is weaker than the literal one, so the refutation stated here is stronger; without it
a single segment would refute the claim trivially.
-/

open MathlibExt.Geometry.SegmentVisibilityShared

/-- The polygon `e ∘ π` through all endpoints is circumscribing: no segment lies outside it, i.e.
every segment `k` is either an edge of the polygon or an internal chord (its relative interior lies
in the interior of the polygon's region `K`). -/
def IsCircumscribing {m : ℕ} (e : Fin (2 * m) → ℝ × ℝ) (π : Equiv.Perm (Fin (2 * m))) : Prop :=
  ∃ K : Set (ℝ × ℝ), IsRegion (e ∘ π) K ∧ ∀ k : Fin m,
    (∃ t, ({π t, π (finRotate (2 * m) t)} : Set (Fin (2 * m))) =
        {⟨2 * k.val, by omega⟩, ⟨2 * k.val + 1, by omega⟩}) ∨
      openSegment ℝ (e ⟨2 * k.val, by omega⟩) (e ⟨2 * k.val + 1, by omega⟩) ⊆ interior K

/-- Mirzaian's conjecture (Ghosh–Goswami, Conjecture 16) for segments that are not all collinear:
the segment visibility graph of `m` pairwise disjoint nondegenerate segments, not all on one line,
has a Hamiltonian cycle whose drawing is the boundary of a circumscribing polygon. -/
def circumscribingPolygonExists : Prop :=
  ∀ (m : ℕ) (e : Fin (2 * m) → ℝ × ℝ), IsDisjointSegmentFamily e → ¬ Collinear ℝ (Set.range e) →
    ∃ π : Equiv.Perm (Fin (2 * m)), (∀ t, SegAdj e (π t) (π (finRotate (2 * m) t))) ∧
      IsSimplePolygon (e ∘ π) ∧ IsCircumscribing e π

/--
Resolved false: Urabe and Watanabe gave a set of disjoint segments in the plane (not all collinear)
whose segment visibility graph has no Hamiltonian cycle bounding a circumscribing polygon, as the
problem list records. Source: S. K. Ghosh and P. P. Goswami, Unsolved problems in visibility graphs
of points, segments and polygons, ACM Comput. Surv. 46 (2013), arXiv:1012.5187, Conjecture 16 (A.
Mirzaian); resolution: M. Urabe and M. Watanabe, On a counterexample to a conjecture of Mirzaian,
Comput. Geom. 2 (1992), 51-53, doi:10.1016/0925-7721(92)90020-S, the problem list (Section 3):
'Urabe and Watanabe gave a counter-example to Conjecture 16'; a set of disjoint segments admitting
no circumscribing polygon, https://doi.org/10.1016/0925-7721(92)90020-S.
-/
public theorem_wanted circumscribingPolygonExists_refuted : ¬ circumscribingPolygonExists

end MathlibExt.Geometry.CircumscribingPolygonAMR131Problem0014Wanted
