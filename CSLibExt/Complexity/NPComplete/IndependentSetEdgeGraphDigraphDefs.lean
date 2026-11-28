/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on edge graphs of directed graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, comment:
"Remains NP-complete … for edge graphs of directed graphs [Gavril, 1977a]";
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th Conference on
Information Sciences and Systems, Johns Hopkins University, Baltimore (1977), 91-95 (not
available; the result and its attribution are those recorded by Garey and Johnson);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetEdgeGraphDigraph

/-- The edge graph of a digraph `D`: its vertices are the arcs `(u, v)` of `D`, and two distinct
arcs are adjacent when the head of one is the tail of the other. -/
def digraphEdgeGraph {V : Type*} (D : Digraph V) :
    SimpleGraph {a : V × V // D.Adj a.1 a.2} :=
  SimpleGraph.fromRel fun a b => a.1.2 = b.1.1

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSetEdgeGraphDigraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetEdgeGraphDigraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is isomorphic to the edge graph of a digraph `D` (on vertices `Fin m`), and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetEdgeGraphDigraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∃ (m : ℕ) (D : Digraph (Fin m)), Nonempty (Graph i ≃g digraphEdgeGraph D)) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetEdgeGraphDigraphFeasible
    (i : IndependentSetEdgeGraphDigraphInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on edge graphs of directed graphs as a decision problem over bitstrings. -/
noncomputable def independentSetEdgeGraphDigraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetEdgeGraphDigraphInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetEdgeGraphDigraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetEdgeGraphDigraph
