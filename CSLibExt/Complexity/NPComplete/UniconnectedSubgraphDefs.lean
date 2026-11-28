/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNICONNECTED SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT30] UNICONNECTED SUBGRAPH;
S. N. Maheshwari, "Traversal marker placement problems are NP-complete", Technical Report
CU-CS-092-76, Department of Computer Science, University of Colorado, Boulder (1976),
Lemma 1, https://scholar.colorado.edu/concern/reports/rb68xc64n.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Batteries.Data.List.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraph

/-- An instance: vertex count `n` (vertices `Fin n`), arc list (ordered pairs), bound `K`. -/
abbrev UniconnectedSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph of the instance: `u → v` is an arc iff `(u, v)` is in the arc list. -/
def Graph (i : UniconnectedSubgraphInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list describes a directed graph on `Fin n` (no
duplicate arcs, no loops, endpoints in range; opposite arcs `(u, v)` and `(v, u)` are allowed),
and `0 < K ≤ |A|`, the length of the arc list. -/
def WellFormed (i : UniconnectedSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- `p` is a directed path of `H`: a nonempty list of distinct vertices in which each vertex is
joined to the next one by an arc of `H`. -/
def IsDirectedPath {V : Type*} (H : Digraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain H.Adj

/-- Some subdigraph `H ≤ G` on the same vertices has at least `K` arcs and at most one directed
path from any vertex to any vertex. -/
def UniconnectedSubgraphFeasible (i : UniconnectedSubgraphInstance) : Prop :=
  ∃ H : Digraph (Fin i.1), H ≤ Graph i ∧
    i.2.2 ≤ {a : Fin i.1 × Fin i.1 | H.Adj a.1 a.2}.ncard ∧
    ∀ p q : List (Fin i.1), IsDirectedPath H p → IsDirectedPath H q →
      p.head? = q.head? → p.getLast? = q.getLast? → p = q

open Classical in
/-- UNICONNECTED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def uniconnectedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniconnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ UniconnectedSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraph
