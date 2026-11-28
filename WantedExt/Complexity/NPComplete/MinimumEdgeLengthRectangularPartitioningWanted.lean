/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EDGE LENGTH RECTANGULAR PARTITIONING is NP-complete

Source:
A. Lingas, R. Y. Pinter, R. L. Rivest and A. Shamir, "Minimum edge length partitioning of
rectilinear polygons", Proceedings of the 20th Annual Allerton Conference on Communication,
Control, and Computing (1982), 53-63 (Section 2: rectilinear figures with holes and rectangular
partitions; Section 3, Lemma 1: minimum partitions lie on the induced grid; Section 4,
Theorem 3: "MELRP is strongly NP-complete").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumEdgeLengthRectangularPartitioningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEdgeLengthRectangularPartitioning

/-!
# MINIMUM EDGE LENGTH RECTANGULAR PARTITIONING is NP-complete

INSTANCE: a rectilinear figure `P` (rectilinear polygons with rectilinear holes, integer
coordinates) and a number `k`.
QUESTION: is there a rectangular partitioning of `P` whose edge length does not exceed `k`?

Lingas, Pinter, Rivest and Shamir (Section 2): a rectilinear figure is a set of rectilinear
boundaries, each of which may contain non-overlapping rectilinear holes; "A rectangular partition
of a figure is a set of line segments ... lying within its boundary and not crossing any holes, so
that when drawn into the figure the area not enclosed by holes is partitioned into rectangles",
the segments are its edges, and minimizing their total length "is equivalent to requiring that
the total of all perimeters of the resulting rectangles be minimized". Section 4 defines MELRP
as the question above and proves it strongly NP-complete (Theorem 3, by a reduction from planar
3-satisfiability: "`k` and the dimensions of the figure are polynomially related to the size" of
the formula); the figures built there have non-degenerate holes, which Theorem 4 then replaces by
points. Without holes the problem is polynomial (their Section 3).

A figure with integer coordinates is the union of the unit cells `[a, a + 1] × [b, b + 1]` that
it covers, so it is given as the list of these cells `(a, b) ∈ ℕ × ℕ`; holes and the outside are
the cells not listed. A finite set of cells is the region of such a figure (boundaries and holes
pairwise disjoint simple rectilinear polygons) exactly when no two of its cells meet only at a
corner: no `2 × 2` block of cells contains two diagonally opposite cells of the set without one
of the other two (`NoCornerContact`); then the boundary of the union consists of disjoint simple
closed rectilinear curves, and the boundaries of a figure, being simple and disjoint, never pinch
at a corner. As the problem is strongly NP-complete, listing the cells (whose number is
polynomial in the dimensions) keeps it NP-complete. Rectangles are unions of whole cells: by the
argument of Lemma 1 (sliding a maximal partitioning segment perpendicular to itself changes the
total length linearly until it meets a line of the induced grid), some minimum partition has all
edges on the lines through the corners of the figure, which here have integer coordinates. A
rectangle `(x, y, w, h)` covers the cells `[x, x + w) × [y, y + h)` (`inRect`); the partition is a
list of rectangles inside `P`, pairwise without common cells, covering `P` (`IsRectPartition`).
Its edges are then the unit segments between two cells of `P` that lie in different rectangles:
`edgeLength` counts the cells of `P` whose right neighbor, and those whose upper neighbor, is a
cell of `P` in a different rectangle. Membership in NP: a partition into cell rectangles has at
most one rectangle per cell.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM EDGE LENGTH RECTANGULAR PARTITIONING is NP-complete.** Source: Lingas, Pinter,
Rivest and Shamir (1982), Theorem 3. -/
public theorem_wanted minimumEdgeLengthRectangularPartitioning_npComplete :
    minimumEdgeLengthRectangularPartitioningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumEdgeLengthRectangularPartitioningDec

end MetaMathlibExt.Complexity.NPComplete.MinimumEdgeLengthRectangularPartitioning
