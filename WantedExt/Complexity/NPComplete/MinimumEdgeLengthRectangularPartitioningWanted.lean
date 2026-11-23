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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

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

/-- An instance: the list of cells `(a, b)` of the figure and the bound `k`. -/
abbrev MinimumEdgeLengthRectangularPartitioningInstance := List (ℕ × ℕ) × ℕ

/-- No two cells of `P` meet only at a corner: whenever two diagonally opposite cells of a `2 × 2`
block are in `P`, so is one of the other two. -/
def NoCornerContact (P : List (ℕ × ℕ)) : Prop :=
  ∀ a b : ℕ, ((a, b) ∈ P ∧ (a + 1, b + 1) ∈ P → (a + 1, b) ∈ P ∨ (a, b + 1) ∈ P) ∧
    ((a + 1, b) ∈ P ∧ (a, b + 1) ∈ P → (a, b) ∈ P ∨ (a + 1, b + 1) ∈ P)

/-- Well-formedness of an instance: no cell is listed twice, and the cells form the region of a
rectilinear figure (no two cells meet only at a corner). -/
def WellFormed (i : MinimumEdgeLengthRectangularPartitioningInstance) : Prop :=
  i.1.Nodup ∧ NoCornerContact i.1

/-- The rectangle `r = (x, y, w, h)` covers the cell `c`: `c ∈ [x, x + w) × [y, y + h)`. -/
def inRect (r : ℕ × ℕ × ℕ × ℕ) (c : ℕ × ℕ) : Bool :=
  r.1 ≤ c.1 && c.1 < r.1 + r.2.2.1 && r.2.1 ≤ c.2 && c.2 < r.2.1 + r.2.2.2

/-- Two rectangles have no common cell. -/
def RectDisjoint (r r' : ℕ × ℕ × ℕ × ℕ) : Prop :=
  ∀ c, ¬ (inRect r c ∧ inRect r' c)

/-- The rectangles `rs` partition the figure `P`: every cell of a rectangle is a cell of `P`, two
rectangles of the list have no common cell, and every cell of `P` lies in a rectangle. -/
def IsRectPartition (P : List (ℕ × ℕ)) (rs : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  (∀ r ∈ rs, ∀ c, inRect r c → c ∈ P) ∧ rs.Pairwise RectDisjoint ∧ ∀ c ∈ P, ∃ r ∈ rs, inRect r c

/-- The edge length of the partition `rs` of `P`: the number of unit segments between a cell of `P`
and its right or upper neighbor in `P` when no rectangle contains both. -/
def edgeLength (P : List (ℕ × ℕ)) (rs : List (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  (P.filter fun c => decide ((c.1 + 1, c.2) ∈ P) &&
    !rs.any fun r => inRect r c && inRect r (c.1 + 1, c.2)).length +
  (P.filter fun c => decide ((c.1, c.2 + 1) ∈ P) &&
    !rs.any fun r => inRect r c && inRect r (c.1, c.2 + 1)).length

/-- Some rectangular partition of the figure has edge length at most `k`. -/
def MinimumEdgeLengthRectangularPartitioningFeasible
    (i : MinimumEdgeLengthRectangularPartitioningInstance) : Prop :=
  ∃ rs : List (ℕ × ℕ × ℕ × ℕ), IsRectPartition i.1 rs ∧ edgeLength i.1 rs ≤ i.2

open Classical in
/-- MINIMUM EDGE LENGTH RECTANGULAR PARTITIONING as a decision problem over bitstrings. -/
noncomputable def minimumEdgeLengthRectangularPartitioningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumEdgeLengthRectangularPartitioningInstance) x with
  | some i => decide (WellFormed i ∧ MinimumEdgeLengthRectangularPartitioningFeasible i)
  | none => false

/-- **MINIMUM EDGE LENGTH RECTANGULAR PARTITIONING is NP-complete.** Source: Lingas, Pinter,
Rivest and Shamir (1982), Theorem 3. -/
public theorem_wanted minimumEdgeLengthRectangularPartitioning_npComplete :
    minimumEdgeLengthRectangularPartitioningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumEdgeLengthRectangularPartitioningDec

end MetaMathlibExt.Complexity.NPComplete.MinimumEdgeLengthRectangularPartitioning
