/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Segment visibility graphs have Hamiltonian cycles (Mirzaian; Ghosh-Goswami Conjecture 14)

S. K. Ghosh and P. P. Goswami, Unsolved problems in visibility graphs of points, segments and
polygons, Conjecture 14 (Mirzaian): every segment visibility graph `G` contains a Hamiltonian cycle
`C`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import WantedExt.Geometry.SegmentVisibilityShared

@[expose] public section

namespace MathlibExt.Geometry.SegmentVisibilityHamiltonianCycleAMR131Problem0012Wanted

/-!
Source: S. K. Ghosh and P. P. Goswami, Unsolved problems in visibility graphs of points, segments
and polygons, ACM Comput. Surv. 46 (2013), arXiv:1012.5187, Conjecture 14 (A. Mirzaian).
UnsolvedMath record UM-00800543 (`AMR-131-0012`), dataset ulamai/UnsolvedMath v1.8.0.

Segments are given by an endpoint family `e : Fin (2m) → ℝ × ℝ`, segment `k` joining `e (2k)` and `e
(2k + 1)`; they are nondegenerate and pairwise disjoint (closed segments). Two endpoints are
adjacent when they bound the same segment or the open segment joining them meets no segment, which
is the source's visibility (no passing through another endpoint, no grazing along a segment). A
Hamiltonian cycle is a cyclic order `π` of the `2m` endpoints with consecutive endpoints adjacent;
the definitions repeat those of the round-1 OpenConjectures entries for the same list
(`AMR131Problem15`, `AMR131Problem36`). The hypothesis that the segments are not all collinear is
Hoffmann and Tóth's: for collinear segments the visibility graph is a path, with no Hamiltonian
cycle, so the source's literal 'every segment visibility graph' fails for them (and for a single
segment).
-/

open MathlibExt.Geometry.SegmentVisibilityShared

/-- Mirzaian's conjecture (Ghosh–Goswami, Conjecture 14) for segments that are not all collinear:
the segment visibility graph of `m` pairwise disjoint nondegenerate segments, not all on one line,
has a Hamiltonian cycle, listed as a cyclic order `π` of the `2m` endpoints with consecutive
endpoints adjacent. -/
def segmentVisibilityHamiltonianCycle : Prop :=
  ∀ (m : ℕ) (e : Fin (2 * m) → ℝ × ℝ), IsDisjointSegmentFamily e → ¬ Collinear ℝ (Set.range e) →
    ∃ π : Equiv.Perm (Fin (2 * m)), ∀ t, SegAdj e (π t) (π (finRotate (2 * m) t))

/--
Resolved true for segments that are not all collinear: Hoffmann and Tóth proved that the segment
endpoint visibility graph then admits a simple Hamiltonian polygon (Conjecture 15), and the problem
list notes that Conjecture 15 implies Conjecture 14. Source: S. K. Ghosh and P. P. Goswami, Unsolved
problems in visibility graphs of points, segments and polygons, ACM Comput. Surv. 46 (2013),
arXiv:1012.5187, Conjecture 14 (A. Mirzaian); resolution: M. Hoffmann and Cs. D. Tóth, Segment
endpoint visibility graphs are Hamiltonian, Comput. Geom. 26 (2003), 47-68,
doi:10.1016/S0925-7721(02)00172-4, Abstract: the segment endpoint visibility graph of any finite set
of disjoint line segments in the plane admits a simple Hamiltonian polygon, if not all segments are
collinear, proving Mirzaian's conjecture; the problem list (Section 3) records that Conjecture 15
was proved for all segment sets by Hoffmann and Tóth and that 'since Conjecture 15 is true,
Conjecture 14 is also true', https://doi.org/10.1016/S0925-7721(02)00172-4.
-/
public theorem_wanted segmentVisibilityHamiltonianCycle_holds : segmentVisibilityHamiltonianCycle

end MathlibExt.Geometry.SegmentVisibilityHamiltonianCycleAMR131Problem0012Wanted
