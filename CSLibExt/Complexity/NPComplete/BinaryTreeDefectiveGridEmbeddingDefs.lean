/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EMBEDDING BINARY TREES IN A DEFECTIVE GRID: definitions

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

public import Cslib.Foundations.Data.List.IsChainFromTo
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card
public import CSLibExt.Complexity.NPComplete.UnitLengthTreeGridEmbeddingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryTreeDefectiveGridEmbedding

open MetaMathlibExt.Complexity.NPComplete.UnitLengthTreeGridEmbedding
  (UnitLengthTreeGridEmbeddingInstance Graph)

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

end MetaMathlibExt.Complexity.NPComplete.BinaryTreeDefectiveGridEmbedding
