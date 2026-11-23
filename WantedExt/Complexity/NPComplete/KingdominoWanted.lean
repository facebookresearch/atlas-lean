/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KINGDOMINO (K-TILING) is NP-complete

Source:
V.-H. Nguyen, K. Perrot and M. Vallet, "NP-completeness of the game Kingdomino",
Theoretical Computer Science 822 (2020), 23-35, doi:10.1016/j.tcs.2020.04.007
(arXiv:1909.02849), Section 3 (K-tiling problem) and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kingdomino

/-!
# KINGDOMINO (K-TILING) is NP-complete

The one-player model of Kingdomino of Nguyen, Perrot and Vallet. A domino is a `2 × 1`
rectangle with a color and a number of crowns on each of its two cells. The board is `ℤ²`, with
a special cell, the tower, at `(0, 0)`. Given a sequence `τ` of dominoes, a K-tiling by `τ` is
built by placing the dominoes in the order of `τ`: a domino can be placed on a pair of adjacent
free positions if and only if at least one of its two cells is adjacent to an already placed
cell of the same color, or is adjacent to the tower; it is lost (not placed) if and only if it
can be placed nowhere. The score of a K-tiling is the sum, over its regions (the
monochromatic connected components of placed cells), of the number of cells of the region times
the number of crowns it contains.

INSTANCE: a sequence `τ` of dominoes and an integer `s`.
QUESTION: is there a K-tiling by `τ` with score at least `s`?

A placement of the `k`-th domino is `some (u, v)`, its first cell at `u` and its second at `v`
(all four rotations arise this way), or `none` when the domino is lost. Cells are adjacent when
they are adjacent in Mathlib's grid graph `hasse ℤ □ hasse ℤ` on `ℤ × ℤ`. The paper drops the
official bounding box (`5 × 5` or `7 × 7`) of the game, and so does this statement.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A domino: the color and the number of crowns of its first cell, then of its second cell. -/
abbrev Domino := (ℕ × ℕ) × (ℕ × ℕ)

/-- An instance: the sequence `τ` of dominoes and the score bound `s`. -/
abbrev KingdominoInstance := List Domino × ℕ

/-- The board graph on `ℤ × ℤ`: positions are adjacent when they share a side. -/
abbrev boardGraph : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ

/-- The tower. -/
def tower : ℤ × ℤ := (0, 0)

/-- A placed cell: its position, and its color and number of crowns. -/
abbrev PlacedCell := (ℤ × ℤ) × (ℕ × ℕ)

/-- The cells placed by the first `k` dominoes of `τ` under the placements `pl`. -/
def placedCells (τ : List Domino) (pl : List (Option ((ℤ × ℤ) × (ℤ × ℤ)))) (k : ℕ) :
    List PlacedCell :=
  ((τ.zip pl).take k).flatMap fun x =>
    match x.2 with
    | some uv => [(uv.1, x.1.1), (uv.2, x.1.2)]
    | none => []

/-- A domino cell of color `col` at position `u` touches the board `B`: `u` is adjacent to the
tower or to a placed cell of color `col`. -/
def Touches (B : List PlacedCell) (u : ℤ × ℤ) (col : ℕ) : Prop :=
  boardGraph.Adj u tower ∨ ∃ c ∈ B, boardGraph.Adj u c.1 ∧ c.2.1 = col

/-- Domino `d` can be placed on board `B` with its first cell at `u` and its second at `v`: the
positions are adjacent and free (neither the tower nor a placed cell), and one of the two cells
touches the board with its own color. -/
def CanPlace (B : List PlacedCell) (d : Domino) (u v : ℤ × ℤ) : Prop :=
  boardGraph.Adj u v ∧ u ≠ tower ∧ v ≠ tower ∧ (∀ c ∈ B, c.1 ≠ u ∧ c.1 ≠ v) ∧
    (Touches B u d.1.1 ∨ Touches B v d.2.1)

/-- The placements `pl` form a K-tiling by `τ`: one placement per domino; the `k`-th domino is
placed only where it can be placed on the board left by the first `k` dominoes, and it is lost
only if it can be placed nowhere. -/
def IsKTiling (τ : List Domino) (pl : List (Option ((ℤ × ℤ) × (ℤ × ℤ)))) : Prop :=
  pl.length = τ.length ∧ ∀ k < τ.length,
    (∀ u v, pl.getD k none = some (u, v) →
      CanPlace (placedCells τ pl k) (τ.getD k ((0, 0), (0, 0))) u v) ∧
    (pl.getD k none = none →
      ∀ u v, ¬ CanPlace (placedCells τ pl k) (τ.getD k ((0, 0), (0, 0))) u v)

/-- The region graph of a board: placed cells (by index) are adjacent when their positions are
adjacent and their colors are equal. Its connected components are the regions. -/
def regionGraph (B : List PlacedCell) : SimpleGraph (Fin B.length) :=
  boardGraph.comap (fun j => (B.get j).1) ⊓
    SimpleGraph.fromRel fun a b => (B.get a).2.1 = (B.get b).2.1

open Classical in
/-- The score of a board: the sum over its regions of the number of cells of the region times
the number of crowns it contains. -/
noncomputable def score (B : List PlacedCell) : ℕ :=
  ∑ C : (regionGraph B).ConnectedComponent,
    C.supp.ncard * ∑ j ∈ Finset.univ.filter (· ∈ C.supp), (B.get j).2.2

/-- Well-formedness of an instance: every sequence of dominoes and every bound is an instance. -/
def WellFormed (_ : KingdominoInstance) : Prop := True

/-- Some K-tiling by `τ` has score at least `s`. -/
def KingdominoFeasible (i : KingdominoInstance) : Prop :=
  ∃ pl : List (Option ((ℤ × ℤ) × (ℤ × ℤ))), IsKTiling i.1 pl ∧
    i.2 ≤ score (placedCells i.1 pl i.1.length)

open Classical in
/-- KINGDOMINO (K-TILING) as a decision problem over bitstrings. -/
noncomputable def kingdominoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KingdominoInstance) x with
  | some i => decide (WellFormed i ∧ KingdominoFeasible i)
  | none => false

/-- **KINGDOMINO (K-TILING) is NP-complete.** Source: Nguyen, Perrot and Vallet (2020),
Section 3 and Theorem 1. -/
public theorem_wanted kingdomino_npComplete :
    kingdominoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kingdominoDec

end MetaMathlibExt.Complexity.NPComplete.Kingdomino
