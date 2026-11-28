/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EDGE LENGTH RECTANGULAR PARTITIONING: definitions

Source:
A. Lingas, R. Y. Pinter, R. L. Rivest and A. Shamir, "Minimum edge length partitioning of
rectilinear polygons", Proceedings of the 20th Annual Allerton Conference on Communication,
Control, and Computing (1982), 53-63 (Section 2: rectilinear figures with holes and rectangular
partitions; Section 3, Lemma 1: minimum partitions lie on the induced grid; Section 4,
Theorem 3: "MELRP is strongly NP-complete").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEdgeLengthRectangularPartitioning

/-- An instance: the list of cells `(a, b)` of the figure and the bound `k`. -/
abbrev MinimumEdgeLengthRectangularPartitioningInstance := List (ℕ × ℕ) × ℕ

/-- No `2 × 2` block contains exactly two cells of `P` on opposite corners: whenever two
diagonally opposite cells of a `2 × 2` block are in `P`, so is one of the other two. -/
def NoCornerContact (P : List (ℕ × ℕ)) : Prop :=
  ∀ a b : ℕ, ((a, b) ∈ P ∧ (a + 1, b + 1) ∈ P → (a + 1, b) ∈ P ∨ (a, b + 1) ∈ P) ∧
    ((a + 1, b) ∈ P ∧ (a, b + 1) ∈ P → (a, b) ∈ P ∨ (a + 1, b + 1) ∈ P)

/-- Well-formedness of an instance: no cell is listed twice, and the cells form the region of a
rectilinear figure (no `2 × 2` block contains exactly two cells, on opposite corners). -/
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

/-- The edge length of the partition `rs` of `P`: the number of occurrences in the list `P` of a
cell whose right neighbor is in `P` with no rectangle of `rs` containing both, plus the same
count for upper neighbors. A cell listed twice counts twice; for a duplicate-free `P`, as
well-formedness requires, this is the number of unit segments between neighboring cells that no
rectangle contains together. -/
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

end MetaMathlibExt.Complexity.NPComplete.MinimumEdgeLengthRectangularPartitioning
