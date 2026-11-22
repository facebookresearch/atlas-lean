/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET for hereditary sat graphs is NP-complete

Source:
I. E. Zverovich, "Satgraphs and independent domination. Part 1", Theoretical Computer Science
352(1-3) (2006), 47-56, doi:10.1016/j.tcs.2005.08.038;
ISGCI, Information System on Graph Classes and their Inclusions, class hereditary sat (gc_1218,
https://www.graphclasses.org/classes/gc_1218.html), problem Independent dominating set;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import WantedExt.Complexity.NPComplete.IndependentDominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetHereditarySat

/-!
# INDEPENDENT DOMINATING SET for hereditary sat graphs is NP-complete

INSTANCE: a hereditary sat graph `G = (V, E)` and a positive integer `K ≤ |V|`. ISGCI: "A graph
`G` is a hereditary sat if its vertex set can be partitioned into two sets `A` and `B` (both
possibly empty), such that `G[A]` is a clique, every vertex in `G[B]` has degree at most 1 and in
`G` there is no triangle with one vertex in `A` and two in `B`."
QUESTION: does `G` contain a set `S` of pairwise non-adjacent vertices with `|S| ≤ K` such that
every vertex of `G` is in `S` or adjacent to a vertex of `S`?

This is the restriction of INDEPENDENT DOMINATING SET (`IndependentDominatingSetWanted`) to
hereditary sat graphs. The instance type, the graph and the question are the parent's
(`IndependentDominatingSet.IndependentDominatingSetInstance`, `IndependentDominatingSet.Graph`,
`IndependentDominatingSet.IndependentDominatingSetFeasible`); `WellFormed` is the parent's plus
the restriction and the dominating-set bounds `0 < K ≤ |V|` of Garey and Johnson's [GT2].
`IsHereditarySat` takes `A` as a `Finset` and `B` as its complement: `A` is a clique (Mathlib's
`SimpleGraph.IsClique`), each vertex of `B` has at most one neighbour in `B`, and no vertex of
`A` is adjacent to both ends of an edge inside `B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is a hereditary sat graph: for some set `A` with complement `B`, `A` is a clique, every
vertex of `B` has at most one neighbour in `B`, and there is no triangle with one vertex in `A`
and two in `B`. -/
def IsHereditarySat {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A : Finset (Fin n), G.IsClique (A : Set (Fin n)) ∧
    (∀ v w₁ w₂, v ∉ A → w₁ ∉ A → w₂ ∉ A → G.Adj v w₁ → G.Adj v w₂ → w₁ = w₂) ∧
      ∀ a b c, a ∈ A → b ∉ A → c ∉ A → G.Adj a b → G.Adj a c → ¬ G.Adj b c

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is a
hereditary sat graph, and `0 < K ≤ n`. -/
def WellFormed (i : IndependentDominatingSet.IndependentDominatingSetInstance) : Prop :=
  IndependentDominatingSet.WellFormed i ∧ IsHereditarySat (IndependentDominatingSet.Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT DOMINATING SET for hereditary sat graphs as a decision problem over bitstrings. -/
noncomputable def independentDominatingSetHereditarySatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSet.IndependentDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ IndependentDominatingSet.IndependentDominatingSetFeasible i)
  | none => false

/-- **INDEPENDENT DOMINATING SET for hereditary sat graphs is NP-complete.** Source: Zverovich
(2006); ISGCI (gc_1218). -/
public theorem_wanted independentDominatingSetHereditarySat_npComplete :
    independentDominatingSetHereditarySatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentDominatingSetHereditarySatDec

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetHereditarySat
