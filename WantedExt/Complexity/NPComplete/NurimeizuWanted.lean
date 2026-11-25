/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NURIMEIZU is NP-complete

Source:
C. Iwamoto and T. Ide, "Moon-or-Sun, Nagareru, and Nurimeizu are NP-complete", IEICE
Transactions on Fundamentals of Electronics, Communications and Computer Sciences E105-A
(2022), 1187-1194, doi:10.1587/transfun.2021DMP0006;
rules as restated by D. Miyahara, P. Lafourcade and M. Puys, "Card-based ZKP protocols for
connectivity-based puzzles: extending to tree structures with application to Nurimeizu",
FUN 2026, LIPIcs 366, 35, doi:10.4230/LIPIcs.FUN.2026.35, Section 2.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nurimeizu

/-!
# NURIMEIZU is NP-complete

Nurimeizu is one of Nikoli's pencil puzzles; Iwamoto and Ide (2022) show that deciding whether a
given instance has a solution is NP-complete. Its rules, as restated by Miyahara, Lafourcade and
Puys (FUN 2026, Section 2.1, citing Iwamoto and Ide for NP-completeness): "Given an `m × n`
grid, the goal of Nurimeizu is to color certain cells based on the following rules: Create a
maze from the start (S) to the goal (G) across only white cells. Room: All cells within a room
(enclosed by bold lines) have to be either colored or left white. Tree: The set of all white
cells must form a tree structure (i.e., they must be connected and contain no cycles). Shortest
Path: There must exist a shortest path between S and G through white cells. The shortest path
include all ⃝-cells (circle) and no △-cell (triangle). In addition, rooms with S, G, ⃝, and △
are left white. Square of 2 × 2: No 2 × 2 area of cells can be entirely of the same color."
Their footnote: the word "shortest" can be omitted, because the white cells form a tree, in
which the path between two cells is unique.

The rooms are given by a grid of room labels, row by row (every row has the length of the first
row); a room is the set of cells with one label and must be connected (a region enclosed by bold
lines). S, G, the circles and the triangles are distinct cells. Cells are adjacent when they
share a side: the grid graph is the box product of two path graphs. A solution is the set `B` of
colored cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid of room labels (a list of rows), the start cell `S`, the goal cell
`G`, the circle cells and the triangle cells, each cell given as `(row, column)`. -/
abbrev NurimeizuInstance :=
  List (List ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- The number of rows. -/
abbrev rows (i : NurimeizuInstance) : ℕ := i.1.length

/-- The number of columns: the length of the first row. -/
abbrev cols (i : NurimeizuInstance) : ℕ := (i.1.headD []).length

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : NurimeizuInstance) := Fin (rows i) × Fin (cols i)

/-- The coordinates of a cell. -/
def coords {i : NurimeizuInstance} (p : Cell i) : ℕ × ℕ := ((p.1 : ℕ), (p.2 : ℕ))

/-- The room label of a cell. -/
def room (i : NurimeizuInstance) (p : Cell i) : ℕ := (i.1.getD p.1 []).getD p.2 0

/-- Orthogonal adjacency of cells: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : NurimeizuInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness of an instance: the grid is rectangular, every room is connected, and the
start, the goal, the circles and the triangles are distinct cells of the grid. -/
def WellFormed (i : NurimeizuInstance) : Prop :=
  (∀ r ∈ i.1, r.length = cols i) ∧
    (∀ p q : Cell i, ∀ h : room i q = room i p,
      ((gridGraph i).induce {c | room i c = room i p}).Reachable ⟨p, rfl⟩ ⟨q, h⟩) ∧
    (∀ c ∈ i.2.1 :: i.2.2.1 :: (i.2.2.2.1 ++ i.2.2.2.2), c.1 < rows i ∧ c.2 < cols i) ∧
    (i.2.1 :: i.2.2.1 :: (i.2.2.2.1 ++ i.2.2.2.2)).Nodup

/-- The instance has a solution: a set `B` of colored cells satisfying the rules. -/
def NurimeizuFeasible (i : NurimeizuInstance) : Prop :=
  ∃ B : Set (Cell i),
    -- Room: a room is entirely colored or entirely white
    (∀ p q : Cell i, room i p = room i q → (p ∈ B ↔ q ∈ B)) ∧
    -- the cells (hence rooms) with S, G, circles and triangles are white
    (∀ p : Cell i, coords p ∈ i.2.1 :: i.2.2.1 :: (i.2.2.2.1 ++ i.2.2.2.2) → p ∉ B) ∧
    -- Tree: the white cells form a tree
    ((gridGraph i).induce Bᶜ).IsTree ∧
    -- the path between S and G through white cells contains every circle and no triangle
    (∃ (s g : Cell i) (hs : s ∈ Bᶜ) (hg : g ∈ Bᶜ), coords s = i.2.1 ∧ coords g = i.2.2.1 ∧
      ∃ W : ((gridGraph i).induce Bᶜ).Walk ⟨s, hs⟩ ⟨g, hg⟩, W.IsPath ∧
        (∀ c ∈ i.2.2.2.1, ∃ v ∈ W.support, coords v.1 = c) ∧
        ∀ c ∈ i.2.2.2.2, ∀ v ∈ W.support, coords v.1 ≠ c) ∧
    -- Square of 2 × 2: no 2 × 2 area is entirely colored or entirely white
    ∀ p q : Cell i, (q.1 : ℕ) = p.1 + 1 → (q.2 : ℕ) = p.2 + 1 →
      ¬ ((p ∈ B ∧ (p.1, q.2) ∈ B ∧ (q.1, p.2) ∈ B ∧ q ∈ B) ∨
        (p ∉ B ∧ (p.1, q.2) ∉ B ∧ (q.1, p.2) ∉ B ∧ q ∉ B))

open Classical in
/-- NURIMEIZU as a decision problem over bitstrings. -/
noncomputable def nurimeizuDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NurimeizuInstance) x with
  | some i => decide (WellFormed i ∧ NurimeizuFeasible i)
  | none => false

/-- **NURIMEIZU is NP-complete.** Source: Iwamoto and Ide (2022); rules as restated by
Miyahara, Lafourcade and Puys (2026). -/
public theorem_wanted nurimeizu_npComplete :
    nurimeizuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nurimeizuDec

end MetaMathlibExt.Complexity.NPComplete.Nurimeizu
