/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIREFIGHTER on trees of maximum degree three: definitions

Source:
S. Finbow, A. King, G. MacGillivray and R. Rizzi, "The firefighter problem for graphs of
maximum degree three", Discrete Mathematics 307 (2007), 2094-2105,
doi:10.1016/j.disc.2005.12.053.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FirefighterMaxDegreeThreeTree

/-- An instance: vertex count `n`, edge list, root `r`, bound `k`. -/
abbrev FirefighterInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : FirefighterInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- `Burning G r d t v`: under the defence list `d`, vertex `v` is on fire at time `t`. At time
`0` only `r` burns; at time `t + 1` the firefighter has defended `d[0], …, d[t]`, and the fire
spreads from every vertex burning at time `t` to each neighbour not defended. -/
def Burning {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n) (d : List (Fin n)) :
    ℕ → Fin n → Prop
  | 0, v => v = r
  | t + 1, v => Burning G r d t v ∨ (v ∉ d.take (t + 1) ∧ ∃ u, Burning G r d t u ∧ G.Adj u v)

open Classical in
/-- Well-formedness of an instance: a simple edge list, the graph is a tree with every vertex of
degree at most `3`, the root is a vertex, and `0 < k`. -/
def WellFormed (i : FirefighterInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsTree ∧ (∀ v, (Graph i).degree v ≤ 3) ∧ i.2.2.1 < i.1 ∧ 0 < i.2.2.2

open Classical in
/-- There is a strategy, defending at each time a vertex not on fire and running until the fire
can no longer spread, under which at most `k` vertices burn. -/
def FirefighterFeasible (i : FirefighterInstance) : Prop :=
  ∃ h : i.2.2.1 < i.1, ∃ d : List (Fin i.1),
    (∀ t (ht : t < d.length), ¬ Burning (Graph i) ⟨i.2.2.1, h⟩ d t d[t]) ∧
    (∀ u v, Burning (Graph i) ⟨i.2.2.1, h⟩ d d.length u → (Graph i).Adj u v →
      Burning (Graph i) ⟨i.2.2.1, h⟩ d d.length v ∨ v ∈ d) ∧
    (Finset.univ.filter fun v => Burning (Graph i) ⟨i.2.2.1, h⟩ d d.length v).card ≤ i.2.2.2

open Classical in
/-- FIREFIGHTER on trees of maximum degree three as a decision problem over bitstrings. -/
noncomputable def firefighterMaxDegreeThreeTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FirefighterInstance) x with
  | some i => decide (WellFormed i ∧ FirefighterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FirefighterMaxDegreeThreeTree
