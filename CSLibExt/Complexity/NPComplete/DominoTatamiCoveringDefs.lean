/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINO TATAMI COVERING: definitions

Source:
A. Erickson and F. Ruskey, "Domino tatami covering is NP-complete", Combinatorial Algorithms
(IWOCA 2013), Lecture Notes in Computer Science 8288 (2013), 140-149,
doi:10.1007/978-3-642-45278-9_13 (arXiv:1305.6669), Definition 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominoTatamiCovering

/-- An instance: the cells `(x, y)` of the region. -/
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

/-- The region has a domino tatami covering: some list of dominoes covers every cell of the
region exactly once and nothing else, and every `2 × 2` block of cells of the region contains a
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

end MetaMathlibExt.Complexity.NPComplete.DominoTatamiCovering
