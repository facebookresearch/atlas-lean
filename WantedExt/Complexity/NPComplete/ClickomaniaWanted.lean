/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLICKOMANIA (SAMEGAME) is NP-complete

Source:
T. C. Biedl, E. D. Demaine, M. L. Demaine, R. Fleischer, L. Jacobsen and J. I. Munro, "The
complexity of Clickomania", in R. J. Nowakowski (ed.), *More Games of No Chance*, MSRI
Publications 42, Cambridge University Press (2002), 389-404, doi:10.1017/9781316135167.029,
arXiv:cs/0107031.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Clickomania

/-!
# CLICKOMANIA (SAMEGAME) is NP-complete

INSTANCE: a rectangular board initially full of square blocks, each colored one of finitely many
colors. QUESTION: is the puzzle solvable, i.e., can all blocks be removed by moves, where a move
selects (clicks) any group of size at least two (a group is a maximal connected monochromatic
polyomino), the blocks of the group disappear, any blocks stacked above them fall straight down as
far as they can, and every column that becomes empty of blocks is removed, bringing its two sides
closer to each other?

These are the rules of Biedl et al., Section 1. A board is the list of its columns from left to
right, each the list of the colors of its blocks from the bottom up; after settling no column has a
hole and after column shifting no column is empty, so this list describes every position reached.
Block `(c, r)` is the `r`-th block from the bottom of the `c`-th column; two blocks share an edge
when they are consecutive in one column, or in the same row of consecutive columns. The group of a
block is the set of blocks reached from it through edge-adjacent blocks of its color. Colors are
natural numbers; the number of colors is the number of distinct colors on the board.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A board: its columns from left to right, each the list of the colors of its blocks from the
bottom up. -/
abbrev Board := List (List ℕ)

/-- The color of the block in column `p.1` and row `p.2` (rows counted from the bottom), if there
is a block there. -/
def colorAt (B : Board) (p : ℕ × ℕ) : Option ℕ := (B.getD p.1 [])[p.2]?

/-- `p` and `q` are blocks of the same color that share an edge. -/
def SameColorAdj (B : Board) (p q : ℕ × ℕ) : Prop :=
  (colorAt B p).isSome ∧ colorAt B p = colorAt B q ∧
    ((p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
      (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)))

/-- `q` lies in the group of the block `p`, the maximal connected monochromatic polyomino
containing `p`: it is reached from `p` through edge-adjacent blocks of the same color. -/
def InGroup (B : Board) (p q : ℕ × ℕ) : Prop :=
  Relation.ReflTransGen (SameColorAdj B) p q

open Classical in
/-- The board after the group of `p` is removed: in every column the remaining blocks settle
(fall straight down, keeping their order), and every column left without blocks is removed,
bringing its two sides together. -/
noncomputable def click (B : Board) (p : ℕ × ℕ) : Board :=
  ((List.range B.length).map fun c =>
    ((List.range (B.getD c []).length).filter fun r => decide (¬ InGroup B p (c, r))).map
      fun r => (B.getD c []).getD r 0).filter fun col => !col.isEmpty

/-- One move: select (click) a group of size at least two, i.e. a block `p` whose group contains
another block, and remove it. -/
def Move (B B' : Board) : Prop := ∃ p,
  (colorAt B p).isSome ∧ (∃ q, q ≠ p ∧ InGroup B p q) ∧ B' = click B p

/-- Well-formedness of an instance: the board is a full rectangle with at least one block, i.e.,
it has a column and every column has the same positive number of blocks. -/
def WellFormed (B : Board) : Prop :=
  B ≠ [] ∧ ∀ col ∈ B, col ≠ [] ∧ col.length = (B.headD []).length

/-- The puzzle is solvable: some sequence of moves removes all blocks. -/
def ClickomaniaFeasible (B : Board) : Prop :=
  Relation.ReflTransGen Move B []

open Classical in
/-- CLICKOMANIA as a decision problem over bitstrings. -/
noncomputable def clickomaniaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := Board) x with
  | some i => decide (WellFormed i ∧ ClickomaniaFeasible i)
  | none => false

/-- **CLICKOMANIA (SAMEGAME) is NP-complete.** Source: Biedl, Demaine, Demaine, Fleischer,
Jacobsen and Munro (2002). -/
public theorem_wanted clickomania_npComplete :
    clickomaniaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L clickomaniaDec

end MetaMathlibExt.Complexity.NPComplete.Clickomania
