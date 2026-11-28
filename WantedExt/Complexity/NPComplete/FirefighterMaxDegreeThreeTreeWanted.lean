/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIREFIGHTER on trees of maximum degree three is NP-complete

Source:
S. Finbow, A. King, G. MacGillivray and R. Rizzi, "The firefighter problem for graphs of
maximum degree three", Discrete Mathematics 307 (2007), 2094-2105,
doi:10.1016/j.disc.2005.12.053.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FirefighterMaxDegreeThreeTree

/-!
# FIREFIGHTER on trees of maximum degree three is NP-complete

The firefighter process on a rooted graph `(G, r)` (Hartnell 1995): at time `0` a fire breaks
out at `r`. At each subsequent time step the firefighter defends some vertex which is not on
fire, and then the fire spreads to all undefended neighbours of each burning vertex. Once
defended, a vertex remains so. The process ends when the fire can no longer spread.

INSTANCE (Finbow, King, MacGillivray and Rizzi, problem 3T-FIRE): a triple `(T, r, k)`, where
`(T, r)` is a rooted tree with maximum degree at most `3` and `k` is a positive integer.
QUESTION: when the fire begins at `r`, is there a strategy such that at most `k` vertices burn?

A strategy is the list `d` of defended vertices, `d[s]` being defended at time `s + 1`.
`Burning T r d t v` says that `v` is on fire at time `t`: only `r` at time `0`, and at time
`t + 1` the vertices burning at time `t` together with every neighbour of one of them that is
not among `d[0], …, d[t]`. The strategy defends at each time a vertex that is not on fire, and
it runs until the fire can no longer spread: after `|d|` steps every neighbour of a burning
vertex is burning or defended. The vertices that burn are those burning at that time.

The tree is given by its vertex count `n` (vertices `0, …, n - 1`) and an edge list, as a
`SimpleGraph (Fin n)` through `Cslib.Complexity.Karp.edgeGraph`; trees and degrees are Mathlib's
`SimpleGraph.IsTree` and `SimpleGraph.degree`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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
/-- The root `r` is a vertex (`r < n`), and, with the fire starting at `r`, there is a strategy,
defending at each time a vertex not on fire and running until the fire can no longer spread,
under which at most `k` vertices burn. -/
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

/-- **FIREFIGHTER on trees of maximum degree three is NP-complete.** Source: Finbow, King,
MacGillivray and Rizzi (2007). -/
public theorem_wanted firefighterMaxDegreeThreeTree_npComplete :
    firefighterMaxDegreeThreeTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L firefighterMaxDegreeThreeTreeDec

end MetaMathlibExt.Complexity.NPComplete.FirefighterMaxDegreeThreeTree
