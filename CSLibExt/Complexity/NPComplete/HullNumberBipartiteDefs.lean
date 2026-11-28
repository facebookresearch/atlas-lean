/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HULL NUMBER OF BIPARTITE GRAPHS: definitions

Source:
J. Araujo, V. Campos, F. Giroire, L. Sampaio and R. Soares, "On the hull number of some graph
classes", Electronic Notes in Discrete Mathematics 38 (2011), 49-55,
doi:10.1016/j.endm.2011.09.009;
M. C. Dourado, J. G. Gimbel, J. Kratochvíl, F. Protti and J. L. Szwarcfiter, "On the computation
of the hull number of a graph", Discrete Mathematics 309 (2009), 5668-5674,
doi:10.1016/j.disc.2008.04.020 (general graphs).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HullNumberBipartite

/-- An instance: vertex count `n`, edge list, bound `K`. -/
abbrev HullNumberBipartiteInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HullNumberBipartiteInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- A set of vertices is convex in the geodetic convexity: it contains every vertex of every
shortest path between two of its vertices. -/
def IsGeodeticallyConvex {V : Type*} (G : SimpleGraph V) (C : Set V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, ∀ p : G.Walk u v, p.length = G.dist u v → ∀ w ∈ p.support, w ∈ C

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
bipartite, and `K` is positive. -/
def WellFormed (i : HullNumberBipartiteInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsBipartite ∧ 0 < i.2.2

/-- Some hull set has at most `K` vertices: a set `S` with `|S| ≤ K` such that every
geodetically convex set containing `S` is all of `V`. -/
def HullNumberBipartiteFeasible (i : HullNumberBipartiteInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ∀ C : Set (Fin i.1), ↑S ⊆ C → IsGeodeticallyConvex (Graph i) C → C = Set.univ

open Classical in
/-- HULL NUMBER OF BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def hullNumberBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HullNumberBipartiteInstance) x with
  | some i => decide (WellFormed i ∧ HullNumberBipartiteFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HullNumberBipartite
