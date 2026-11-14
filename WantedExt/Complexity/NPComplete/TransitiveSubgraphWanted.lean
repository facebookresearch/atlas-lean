/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRANSITIVE SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT29] TRANSITIVE SUBGRAPH;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of the 10th
Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355; journal version: M. Yannakakis, "Edge-deletion problems",
SIAM Journal on Computing 10 (1981), 297-309, doi:10.1137/0210021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TransitiveSubgraph

/-!
# TRANSITIVE SUBGRAPH is NP-complete

INSTANCE: a directed graph `G = (V, A)` (no loops, no multiple arcs) and a positive integer
`K ≤ |A|`. QUESTION: is there a subset `A' ⊆ A` with `|A'| ≥ K` such that `G' = (V, A')` is
transitive, i.e., `(u, v) ∈ A'` and `(v, w) ∈ A'` imply `(u, w) ∈ A'`?

The subset `A'` is a subdigraph `H ≤ G` (Mathlib's `Digraph` order), `|A'|` is the number of
ordered pairs `(u, v)` with `H.Adj u v`, and transitivity is Mathlib's `IsTrans` for the arc
relation. Since `G` has no loops, the case `u = w` makes a transitive `A'` contain no pair of
opposite arcs. Under `WellFormed` the arc list has one entry per arc, so its length is `|A|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), arc list (ordered pairs), bound `K`. -/
abbrev TransitiveSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph of the instance: `u → v` is an arc iff `(u, v)` is in the arc list. -/
def Graph (i : TransitiveSubgraphInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list describes a directed graph on `Fin n` (no
duplicate arcs, no loops, endpoints in range; opposite arcs `(u, v)` and `(v, u)` are allowed),
and `0 < K ≤ |A|`, the length of the arc list. -/
def WellFormed (i : TransitiveSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- Some subdigraph `H ≤ G` on the same vertices has at least `K` arcs and a transitive arc
relation. -/
def TransitiveSubgraphFeasible (i : TransitiveSubgraphInstance) : Prop :=
  ∃ H : Digraph (Fin i.1), H ≤ Graph i ∧
    i.2.2 ≤ {a : Fin i.1 × Fin i.1 | H.Adj a.1 a.2}.ncard ∧ IsTrans (Fin i.1) H.Adj

open Classical in
/-- TRANSITIVE SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def transitiveSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TransitiveSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ TransitiveSubgraphFeasible i)
  | none => false

/-- **TRANSITIVE SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT29];
Yannakakis (1978, 1981). -/
public theorem_wanted transitiveSubgraph_npComplete :
    transitiveSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L transitiveSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.TransitiveSubgraph
