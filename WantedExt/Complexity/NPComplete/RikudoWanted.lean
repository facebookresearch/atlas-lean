/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIKUDO is NP-complete

Source:
V.-H. Nguyen and K. Perrot, "Rikudo is NP-complete", Theoretical Computer Science 910 (2022),
34-47, doi:10.1016/j.tcs.2022.01.034 (arXiv:2101.09332).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Function
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Rikudo

/-!
# RIKUDO is NP-complete

Nguyen and Perrot (2022), Section 2: "Let us consider the hexagonal grid with pointy orientation,
and denote `C` the set of cells. Given a subset `τ ⊂ C`, we associate the loopless graph `G_τ`
on vertex set `τ` with adjacency relation corresponding to pairs of cells sharing an edge. We
say that `τ` is connected whenever `G_τ` is connected. A Rikudo game is a connected finite
subset of cells `τ` and, with `n = |τ|` and `[n] = {1, ..., n}`,
* a partial injective map `m : τ → [n]` (numbers already placed),
* a subset of the adjacency relation `p` (given adjacencies).
A solution is a bijective map `s : τ → [n]` such that, with symmetric binary relation `↔_s` on
`C` defined as `c ↔_s c' ⟺ |s(c) − s(c')| = 1`,
* `↔_s` is contained in the adjacency relation (the sequence of numbers forms a Hamiltonian
  path in `G_τ`),
* `s(c) = m(c)` for all cells `c` in the domain of `m` (respect given numbers),
* `p ⊆ ↔_s` (respect given adjacencies)."
RIKUDO asks whether a game admits a solution; Theorem 1 shows it NP-hard ("both problems are
trivially in NP").

Cells are given in axial coordinates of the pointy hexagonal grid: in `ℤ²`, cell `(q, r)` shares
an edge with exactly the six cells `(q ± 1, r)`, `(q, r ± 1)`, `(q + 1, r - 1)` and
`(q - 1, r + 1)`. Every finite instance can be translated into non-negative coordinates, which
preserves adjacency, so cells are pairs of natural numbers and `HexAdj` compares them in `ℤ²`.
The map `s` is a function on cells whose restriction to `τ` is a bijection onto `{1, ..., n}`;
`↔_s ⊆` adjacency is stated as: cells of `τ` with consecutive numbers share an edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **RIKUDO is NP-complete.** Source: Nguyen and Perrot (2022), Theorem 1. -/
public theorem_wanted rikudo_npComplete :
    rikudoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rikudoDec

end MetaMathlibExt.Complexity.NPComplete.Rikudo
