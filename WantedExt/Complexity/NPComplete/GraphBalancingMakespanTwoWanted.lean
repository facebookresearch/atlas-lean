/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH BALANCING (makespan 2, weights 1 and 2) is NP-complete

Source:
T. Ebenlendr, M. Krčál, and J. Sgall, "Graph balancing: a special case of scheduling unrelated
parallel machines", Algorithmica 68 (2014), 62-80, doi:10.1007/s00453-012-9668-9 (the problem);
Y. Asahiro, E. Miyano, and H. Ono, "Graph classes and the complexity of the graph orientation
minimizing the maximum weighted outdegree", Discrete Applied Mathematics 159 (2011), 498-508,
doi:10.1016/j.dam.2010.11.003, Theorem 13 with `k = 2`.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphBalancingMakespanTwo

/-!
# GRAPH BALANCING (makespan 2, weights 1 and 2) is NP-complete

INSTANCE: an undirected multigraph `G = (V, E)` (parallel edges and loops allowed) with a weight
`w(e) ∈ {1, 2}` on each edge. QUESTION: can the edges be oriented so that the load of every
vertex, the total weight of the edges oriented toward it, is at most `2`?

This is the decision version, at makespan `2`, of GRAPH BALANCING of Ebenlendr, Krčál, and
Sgall: scheduling with restricted assignment where every job (edge) can run on one of at most
two machines (its endpoints; a loop is a job fixed to one machine), with weights `1` and `2`.
Ebenlendr et al. record that approximating GRAPH BALANCING within a ratio below `3/2` is
NP-hard. Asahiro, Miyano, and Ono (2011, Theorem 13 with `k = 2`) prove the decision problem
itself strongly NP-hard: deciding whether a simple planar bipartite graph with edge weights in
`{1, 2}` has an orientation of maximum weighted outdegree at most `2`. Reversing every edge
turns outdegree into load, and simple graphs are multigraphs. The bound `2` is part of the
problem.

Vertices are `0, …, n - 1`. An edge is an entry `(u, v, w)` of the edge list: endpoints `u` and
`v` (`u = v` for a loop) and weight `w`; repeated entries are parallel edges. An orientation
chooses one endpoint of each entry, its head.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n` and the edge list (an entry `(u, v, w)` is an edge with
endpoints `u`, `v` and weight `w`). -/
abbrev GraphBalancingMakespanTwoInstance := ℕ × List (ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: every edge has endpoints below `n` and weight `1` or `2`. -/
def WellFormed (i : GraphBalancingMakespanTwoInstance) : Prop :=
  ∀ e ∈ i.2, e.1 < i.1 ∧ e.2.1 < i.1 ∧ (e.2.2 = 1 ∨ e.2.2 = 2)

/-- The head of edge `e` under the choice `b`: its second endpoint when `b = true`, its first
endpoint when `b = false`. -/
def head (e : ℕ × ℕ × ℕ) (b : Bool) : ℕ :=
  if b then e.2.1 else e.1

/-- The load of vertex `v` under the orientation `o`: the total weight of the edges whose head
is `v`. -/
def load (i : GraphBalancingMakespanTwoInstance) (o : Fin i.2.length → Bool) (v : ℕ) : ℕ :=
  ∑ j : Fin i.2.length, if head (i.2.get j) (o j) = v then (i.2.get j).2.2 else 0

/-- Some orientation gives every vertex load at most `2`. -/
def GraphBalancingMakespanTwoFeasible (i : GraphBalancingMakespanTwoInstance) : Prop :=
  ∃ o : Fin i.2.length → Bool, ∀ v < i.1, load i o v ≤ 2

open Classical in
/-- GRAPH BALANCING (makespan 2, weights 1 and 2) as a decision problem over bitstrings. -/
noncomputable def graphBalancingMakespanTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphBalancingMakespanTwoInstance) x with
  | some i => decide (WellFormed i ∧ GraphBalancingMakespanTwoFeasible i)
  | none => false

/-- **GRAPH BALANCING (makespan 2, weights 1 and 2) is NP-complete.** Source: Ebenlendr, Krčál,
and Sgall (2014); Asahiro, Miyano, and Ono (2011), Theorem 13. -/
public theorem_wanted graphBalancingMakespanTwo_npComplete :
    graphBalancingMakespanTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphBalancingMakespanTwoDec

end MetaMathlibExt.Complexity.NPComplete.GraphBalancingMakespanTwo
