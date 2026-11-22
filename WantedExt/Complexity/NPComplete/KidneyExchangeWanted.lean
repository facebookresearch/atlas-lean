/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KIDNEY EXCHANGE (perfect cycle cover with cycles of length at most L) is NP-complete

Source:
D. J. Abraham, A. Blum and T. Sandholm, "Clearing algorithms for barter exchange markets:
enabling nationwide kidney exchanges", Proceedings of the 8th ACM Conference on Electronic
Commerce (EC 2007), 295-304, doi:10.1145/1250910.1250954, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KidneyExchange

/-!
# KIDNEY EXCHANGE (perfect cycle cover with cycles of length at most L) is NP-complete

A barter exchange market is a directed graph `G = (V, E)` with one vertex per agent and an
edge from an agent `vᵢ` to another agent `vⱼ` when `vᵢ` wants the item of `vⱼ`; an exchange is
a collection of disjoint (directed) cycles. Abraham, Blum and Sandholm (2007), Theorem 1:
given a graph `G = (V, E)` and an integer `L ≥ 3`, deciding whether `G` admits a perfect cycle
cover containing cycles of length at most `L` is NP-complete.

A perfect cycle cover, a collection of vertex-disjoint directed cycles that together contain
every vertex, is the same thing as a permutation `σ` of `V` with an edge `v → σ v` at every
vertex `v`: given the cover, let `σ v` be the successor of `v` on its cycle; conversely, the
cycles of `σ` are directed cycles of `G` (there are no loops, so `σ` has no fixed points), and
they are disjoint and cover `V`. The cycle of `σ` through `v` has length
`Function.minimalPeriod σ v`, the least `k > 0` with `σ^[k] v = v`.
`KidneyExchangeFeasible` states the question in this permutation form, as in the sibling
`PartitionIntoHamiltonianSubgraphsWanted`. The directed graph is Mathlib's `Digraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (a pair `(u, v)` is the
edge `u → v`), and the cycle-length bound `L`. -/
abbrev KidneyExchangeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph of the instance, with an edge `u → v` for each pair `(u, v)` of the
edge list. -/
def Graph (i : KidneyExchangeInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: no repeated edges, endpoints in range, no loops (an edge
goes from one agent to another), and `L ≥ 3`. Opposite edges `u → v` and `v → u` may both
occur. -/
def WellFormed (i : KidneyExchangeInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧ 3 ≤ i.2.2

/-- `G` admits a perfect cycle cover containing cycles of length at most `L`: there is a
permutation `σ` of the vertices with an edge from every vertex `v` to `σ v` and with every
cycle of length at most `L`. -/
def KidneyExchangeFeasible (i : KidneyExchangeInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1), ∀ v, (Graph i).Adj v (σ v) ∧ Function.minimalPeriod σ v ≤ i.2.2

open Classical in
/-- KIDNEY EXCHANGE as a decision problem over bitstrings. -/
noncomputable def kidneyExchangeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KidneyExchangeInstance) x with
  | some i => decide (WellFormed i ∧ KidneyExchangeFeasible i)
  | none => false

/-- **KIDNEY EXCHANGE (perfect cycle cover with cycles of length at most L) is NP-complete.**
Source: Abraham, Blum and Sandholm (2007), Theorem 1. -/
public theorem_wanted kidneyExchange_npComplete :
    kidneyExchangeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kidneyExchangeDec

end MetaMathlibExt.Complexity.NPComplete.KidneyExchange
