/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIKUDO: definitions

Source:
V.-H. Nguyen and K. Perrot, "Rikudo is NP-complete", Theoretical Computer Science 910 (2022),
34-47, doi:10.1016/j.tcs.2022.01.034 (arXiv:2101.09332).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Function
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Rikudo

/-- A cell of the hexagonal grid, in non-negative axial coordinates `(q, r)`. -/
abbrev HexCell := ℕ × ℕ

/-- Two cells share an edge: their axial coordinates differ by one of the six offsets
`(±1, 0)`, `(0, ±1)`, `(1, -1)`, `(-1, 1)`. -/
def HexAdj (c d : HexCell) : Prop :=
  ((d.1 : ℤ) - c.1, (d.2 : ℤ) - c.2) ∈
    ([(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)] : List (ℤ × ℤ))

/-- The adjacency graph of the hexagonal grid. -/
def hexGraph : SimpleGraph HexCell := SimpleGraph.fromRel HexAdj

/-- An instance: the cells of `τ`, the placed numbers `m` as `(cell, number)` pairs, and the
given adjacencies `p` as pairs of cells. -/
abbrev RikudoInstance := List HexCell × List (HexCell × ℕ) × List (HexCell × HexCell)

/-- Well-formedness of an instance: `τ` is a duplicate-free list of cells forming a connected
graph `G_τ`; `m` is a partial injective map from `τ` to `{1, ..., n}`; every given adjacency
joins two cells of `τ` that share an edge. -/
def WellFormed (i : RikudoInstance) : Prop :=
  i.1.Nodup ∧ (hexGraph.induce {c | c ∈ i.1}).Connected ∧
    (∀ e ∈ i.2.1, e.1 ∈ i.1 ∧ 1 ≤ e.2 ∧ e.2 ≤ i.1.length) ∧
    (i.2.1.map Prod.fst).Nodup ∧ (i.2.1.map Prod.snd).Nodup ∧
    ∀ e ∈ i.2.2, e.1 ∈ i.1 ∧ e.2 ∈ i.1 ∧ HexAdj e.1 e.2

/-- The game admits a solution `s`. -/
def RikudoFeasible (i : RikudoInstance) : Prop :=
  ∃ s : HexCell → ℕ, Set.BijOn s {c | c ∈ i.1} (Set.Icc 1 i.1.length) ∧
    -- `↔_s` is contained in the adjacency relation
    (∀ c ∈ i.1, ∀ d ∈ i.1, s c + 1 = s d → HexAdj c d) ∧
    -- respect given numbers
    (∀ e ∈ i.2.1, s e.1 = e.2) ∧
    -- respect given adjacencies
    ∀ e ∈ i.2.2, s e.1 + 1 = s e.2 ∨ s e.2 + 1 = s e.1

open Classical in
/-- RIKUDO as a decision problem over bitstrings. -/
noncomputable def rikudoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RikudoInstance) x with
  | some i => decide (WellFormed i ∧ RikudoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Rikudo
