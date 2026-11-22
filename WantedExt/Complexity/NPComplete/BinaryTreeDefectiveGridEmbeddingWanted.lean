/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EMBEDDING BINARY TREES IN A DEFECTIVE GRID is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, update to MINIMUM AREA EMBEDDING OF PLANAR GRAPHS (reference:
P. J. Varman and D. S. Fussell, "Realizing fault-tolerant binary trees in VLSI", Proc. 20th Ann.
Allerton Conf. on Communication, Control, and Computing (1982), 1008-1017);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 89-99,
doi:10.1016/0196-6774(82)90011-6, problem [6] MINIMUM AREA EMBEDDING OF PLANAR GRAPHS (definition
of a grid embedding).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Cslib.Foundations.Data.List.IsChainFromTo
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card
public import WantedExt.Complexity.NPComplete.UnitLengthTreeGridEmbeddingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryTreeDefectiveGridEmbedding

open MetaMathlibExt.Complexity.NPComplete.UnitLengthTreeGridEmbedding
  (UnitLengthTreeGridEmbeddingInstance Graph)

/-!
# EMBEDDING BINARY TREES IN A DEFECTIVE GRID is NP-complete

INSTANCE: a binary tree `T` (every vertex of degree `1` or `3`) and a rectangular grid in which
certain grid points and grid segments are faulty (unusable).
QUESTION: is there a grid embedding of `T` into the non-faulty part of the grid in which the
paths representing distinct edges do not cross?

Johnson's March 1982 column (problem [6]) defines: "A grid embedding is a function `f` that sends
vertices of `G` to distinct grid points (points with integer coordinates), and edges to
non-intersecting paths made up of grid segments (line segments between pairs of grid points that
are adjacent either horizontally or vertically)." His tenth column adds: "If the grid into which
the graph is to be embedded is defective (certain grid segments and points are unusable), then
the problem of determining whether any embedding is possible becomes relevant, but is
NP-complete even for paths, no matter whether crossings are allowed or not, [...]. If crossings
are not allowed, it is also NP-complete for binary trees (trees in which all vertices have
degree 1 or 3)", citing Varman and Fussell (1982), whose paper was not available; the column
records the result and its attribution. Membership in NP: the embedding (a grid point per vertex
and a simple grid path per edge, each of at most `h · w` points) is a certificate.

The tree is an instance of `UnitLengthTreeGridEmbeddingWanted` (vertex count `m`, vertices
`Fin m`, a simple edge list whose graph `UnitLengthTreeGridEmbedding.Graph` is a Mathlib
`SimpleGraph.IsTree`, `UnitLengthTreeGridEmbedding.WellFormed`), and every vertex has exactly `1`
or `3` neighbors. The grid is finite and given explicitly: a list of `h ≥ 1` rows of equal length
`w ≥ 1`, whose entry in row `r` and column `c` is `true` when the grid point `(r, c)` is faulty,
and a list of faulty grid segments, each listed once as the pair of its two points `(p, q)` with
`q` the right or lower neighbor of `p`. Grid points are `Fin h × Fin w`, and grid segments are the
edges of the grid graph `pathGraph h □ pathGraph w`. A step `p → q` is usable when `p` and `q`
are adjacent in the grid, neither is faulty, and the segment between them is not faulty.

An embedding is a map `φ` from the tree vertices to grid points and, for the `j`-th listed edge
`(u, v)`, a vertex list `π j` that is a `List.IsChainFromTo` chain of usable steps from `φ u` to
`φ v` without repeated points. It is a grid embedding without crossings when `φ` is one-to-one,
no path passes through the image of a tree vertex other than its own two ends, and the paths of
two distinct edges meet only at images of tree vertices; so they share at most a common end. Every
tree vertex is the end of some edge, so the images of the vertices are non-faulty points.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tree (vertex count and edge list), the rows of faulty-point flags (`true`:
faulty), and the faulty segments as pairs of grid points `((r, c), (r', c'))`. -/
abbrev BinaryTreeDefectiveGridEmbeddingInstance :=
  UnitLengthTreeGridEmbeddingInstance × List (List Bool) × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- The number `h` of grid rows. -/
abbrev rows (i : BinaryTreeDefectiveGridEmbeddingInstance) : ℕ := i.2.1.length

/-- The number `w` of grid columns, the length of the first row. -/
abbrev cols (i : BinaryTreeDefectiveGridEmbeddingInstance) : ℕ := (i.2.1.headD []).length

/-- The grid point `p` (row `p.1`, column `p.2`) is faulty. -/
def FaultyPoint (i : BinaryTreeDefectiveGridEmbeddingInstance)
    (p : Fin (rows i) × Fin (cols i)) : Prop :=
  (i.2.1.getD p.1 []).getD p.2 false = true

/-- The grid segment between the points `p` and `q` is faulty (listed in either order). -/
def FaultySegment (i : BinaryTreeDefectiveGridEmbeddingInstance)
    (p q : Fin (rows i) × Fin (cols i)) : Prop :=
  (((p.1 : ℕ), (p.2 : ℕ)), ((q.1 : ℕ), (q.2 : ℕ))) ∈ i.2.2 ∨
    (((q.1 : ℕ), (q.2 : ℕ)), ((p.1 : ℕ), (p.2 : ℕ))) ∈ i.2.2

/-- A usable step from `p` to `q`: adjacent grid points (a grid segment of
`pathGraph h □ pathGraph w`), neither faulty, joined by a non-faulty segment. -/
def UsableStep (i : BinaryTreeDefectiveGridEmbeddingInstance)
    (p q : Fin (rows i) × Fin (cols i)) : Prop :=
  (SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)).Adj p q ∧
    ¬ FaultyPoint i p ∧ ¬ FaultyPoint i q ∧ ¬ FaultySegment i p q

/-- Well-formedness of an instance: the tree is a well-formed instance of
`UnitLengthTreeGridEmbeddingWanted` (a simple edge list whose graph is a tree) in which every
vertex has exactly `1` or `3` neighbors; the grid has `h ≥ 1` rows, all of the same length
`w ≥ 1`; and the faulty segments are distinct, each a pair `(p, q)` of grid points with `q` the
right or lower neighbor of `p`. -/
def WellFormed (i : BinaryTreeDefectiveGridEmbeddingInstance) : Prop :=
  UnitLengthTreeGridEmbedding.WellFormed i.1 ∧
    (∀ v : Fin i.1.1, ((Graph i.1).neighborSet v).ncard = 1 ∨
      ((Graph i.1).neighborSet v).ncard = 3) ∧
    0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2.1, row.length = cols i) ∧
    i.2.2.Nodup ∧
    ∀ s ∈ i.2.2, s.2.1 < rows i ∧ s.2.2 < cols i ∧
      (s.2 = (s.1.1, s.1.2 + 1) ∨ s.2 = (s.1.1 + 1, s.1.2))

/-- The tree has a grid embedding without crossings into the non-faulty part of the grid: a
one-to-one map `φ` of the vertices to grid points and, for the `j`-th listed edge `(u, v)`, a
path `π j` of usable steps from `φ u` to `φ v` without repeated points, such that no path passes
through the image of a tree vertex other than its two ends, and paths of distinct edges meet only
at images of tree vertices. -/
def BinaryTreeDefectiveGridEmbeddingFeasible (i : BinaryTreeDefectiveGridEmbeddingInstance) :
    Prop :=
  ∃ φ : Fin i.1.1 → Fin (rows i) × Fin (cols i),
    ∃ π : Fin i.1.2.length → List (Fin (rows i) × Fin (cols i)),
      Function.Injective φ ∧
      (∀ j (u v : Fin i.1.1), ((u : ℕ), (v : ℕ)) = i.1.2.get j →
        (π j).IsChainFromTo (UsableStep i) (φ u) (φ v)) ∧
      (∀ j, (π j).Nodup) ∧
      (∀ j, ∀ x ∈ π j, ∀ v, x = φ v → (v : ℕ) = (i.1.2.get j).1 ∨ (v : ℕ) = (i.1.2.get j).2) ∧
      ∀ j k, j ≠ k → ∀ x ∈ π j, x ∈ π k → ∃ v, x = φ v

open Classical in
/-- EMBEDDING BINARY TREES IN A DEFECTIVE GRID as a decision problem over bitstrings. -/
noncomputable def binaryTreeDefectiveGridEmbeddingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BinaryTreeDefectiveGridEmbeddingInstance) x with
  | some i => decide (WellFormed i ∧ BinaryTreeDefectiveGridEmbeddingFeasible i)
  | none => false

/-- **EMBEDDING BINARY TREES IN A DEFECTIVE GRID is NP-complete.** Source: Johnson, NP-completeness
column (1984), update to MINIMUM AREA EMBEDDING OF PLANAR GRAPHS (Varman and Fussell 1982). -/
public theorem_wanted binaryTreeDefectiveGridEmbedding_npComplete :
    binaryTreeDefectiveGridEmbeddingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L binaryTreeDefectiveGridEmbeddingDec

end MetaMathlibExt.Complexity.NPComplete.BinaryTreeDefectiveGridEmbedding
