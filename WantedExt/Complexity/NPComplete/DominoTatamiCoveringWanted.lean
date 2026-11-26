/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINO TATAMI COVERING is NP-complete

Source:
A. Erickson and F. Ruskey, "Domino tatami covering is NP-complete", Combinatorial Algorithms
(IWOCA 2013), Lecture Notes in Computer Science 8288 (2013), 140-149,
doi:10.1007/978-3-642-45278-9_13 (arXiv:1305.6669), Definition 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominoTatamiCovering

/-!
# DOMINO TATAMI COVERING is NP-complete

INSTANCE: a rectilinear region `R` on the integer lattice, that is, a polyomino which may have
holes.
QUESTION: can `R` be covered by dominoes such that no four of them meet at any one point?

A polyomino is a finite nonempty set of unit cells of the square lattice that is connected
through cells sharing a side. A cell is given by its lattice coordinates `(x, y)`; coordinates
are natural numbers, since covering is invariant under translation and every finite region
translates into the quadrant `x, y ≥ 0`. Connectivity is that of Mathlib's grid graph
`hasse ℕ □ hasse ℕ` on `ℕ × ℕ` (cells are adjacent when they share a side), pulled back to the
listed cells. A domino covers two cells sharing a side: `(x, y)` and `(x + 1, y)` when
horizontal, `(x, y)` and `(x, y + 1)` when vertical. A covering is a list of dominoes whose cells,
counted with multiplicity, are exactly the cells of `R`.

Four dominoes of a covering meet at a lattice point exactly when the four cells around that
point all lie in `R` and belong to four different dominoes; a domino touching that point covers
one of those four cells, and a domino that covers two of them leaves room for at most three
dominoes there. So the tatami condition says: whenever the `2 × 2` block of cells `(x, y)`,
`(x + 1, y)`, `(x, y + 1)`, `(x + 1, y + 1)` lies in `R`, some domino of the covering lies inside
the block.

Erickson and Ruskey represent the region "say, as `n` line segments joining the corners of the
polygon"; here the region is given by the list of its cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a list of cells `(x, y)` of the region, possibly with repeats; distinct cells
forming a polyomino are checked by `WellFormed`. -/
abbrev DominoTatamiCoveringInstance := List (ℕ × ℕ)

/-- The grid graph on `ℕ × ℕ`: cells are adjacent when they share a side. -/
abbrev latticeGraph : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ

/-- Well-formedness of an instance: the cells are distinct and form a polyomino, i.e. the grid
graph pulled back to the listed cells is connected (in particular there is at least one cell).
-/
def WellFormed (i : DominoTatamiCoveringInstance) : Prop :=
  i.Nodup ∧ (latticeGraph.comap i.get).Connected

/-- The two cells of the domino with lower left cell `d.1`: horizontal when `d.2 = true`,
vertical when `d.2 = false`. -/
def dominoCells (d : (ℕ × ℕ) × Bool) : List (ℕ × ℕ) :=
  if d.2 then [d.1, (d.1.1 + 1, d.1.2)] else [d.1, (d.1.1, d.1.2 + 1)]

/-- The four cells of the `2 × 2` block whose lower left cell is `p`. -/
def blockCells (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  [p, (p.1 + 1, p.2), (p.1, p.2 + 1), (p.1 + 1, p.2 + 1)]

/-- The region has a domino tatami covering: the flattened cells of some list of dominoes are a
permutation of the instance list, and every `2 × 2` block of cells of the region contains a
whole domino of the covering, so no four dominoes meet at a point. -/
def DominoTatamiCoveringFeasible (i : DominoTatamiCoveringInstance) : Prop :=
  ∃ dominoes : List ((ℕ × ℕ) × Bool), (dominoes.flatMap dominoCells).Perm i ∧
    ∀ p : ℕ × ℕ, (∀ c ∈ blockCells p, c ∈ i) →
      ∃ d ∈ dominoes, ∀ c ∈ dominoCells d, c ∈ blockCells p

open Classical in
/-- DOMINO TATAMI COVERING as a decision problem over bitstrings. -/
noncomputable def dominoTatamiCoveringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominoTatamiCoveringInstance) x with
  | some i => decide (WellFormed i ∧ DominoTatamiCoveringFeasible i)
  | none => false

/-- **DOMINO TATAMI COVERING is NP-complete.** Source: Erickson and Ruskey (2013). -/
public theorem_wanted dominoTatamiCovering_npComplete :
    dominoTatamiCoveringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominoTatamiCoveringDec

end MetaMathlibExt.Complexity.NPComplete.DominoTatamiCovering
