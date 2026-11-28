/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL EDGE-COLORABILITY OF BIPARTITE GRAPHS: definitions

Source:
S. V. Sevast'janov, "Interval colorability of the edges of a bipartite graph", Metody
Diskretnogo Analiza 50 (1990), 61-72 (in Russian; not available);
C. J. Casselgren and P. A. Petrosyan, "Improper interval edge colorings of graphs", Discrete
Applied Mathematics 305 (2021), 164-178, doi:10.1016/j.dam.2021.08.038 (Section 1: the definition
of an interval coloring, and "it is an NP-complete problem to determine whether a bipartite graph
has an interval coloring", citing Sevast'janov);
A. S. Asratian and R. R. Kamalian, "Investigation on interval edge-colorings of graphs", Journal
of Combinatorial Theory, Series B 62 (1994), 34-43, doi:10.1006/jctb.1994.1053 (the notion of an
interval edge coloring).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Fin.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalEdgeColorabilityBipartite

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev IntervalEdgeColorabilityBipartiteInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntervalEdgeColorabilityBipartiteInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and the graph is
bipartite. -/
def WellFormed (i : IntervalEdgeColorabilityBipartiteInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsBipartite

/-- The proper edge coloring `c` of `G` with the colors `Fin t` is an interval `t`-coloring:
every color is used, and at every vertex `v` the colors of the edges incident to `v` form a set
of consecutive integers. -/
def IsIntervalColoring {V : Type*} (G : SimpleGraph V) {t : ℕ} (c : G.lineGraph.Coloring (Fin t)) :
    Prop :=
  Function.Surjective c ∧
    ∀ v : V, Set.OrdConnected {k : Fin t | ∃ e : G.edgeSet, v ∈ (e : Sym2 V) ∧ c e = k}

/-- The graph of the instance has an interval `t`-coloring for some `t ≥ 1`. -/
def IntervalEdgeColorabilityBipartiteFeasible
    (i : IntervalEdgeColorabilityBipartiteInstance) : Prop :=
  ∃ t : ℕ, 0 < t ∧ ∃ c : (Graph i).lineGraph.Coloring (Fin t), IsIntervalColoring (Graph i) c

open Classical in
/-- INTERVAL EDGE-COLORABILITY OF BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def intervalEdgeColorabilityBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalEdgeColorabilityBipartiteInstance) x with
  | some i => decide (WellFormed i ∧ IntervalEdgeColorabilityBipartiteFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntervalEdgeColorabilityBipartite
