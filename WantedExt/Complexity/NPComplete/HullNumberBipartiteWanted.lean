/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HULL NUMBER OF BIPARTITE GRAPHS is NP-complete

Source:
J. Araujo, V. Campos, F. Giroire, L. Sampaio and R. Soares, "On the hull number of some graph
classes", Electronic Notes in Discrete Mathematics 38 (2011), 49-55,
doi:10.1016/j.endm.2011.09.009;
M. C. Dourado, J. G. Gimbel, J. Kratochvíl, F. Protti and J. L. Szwarcfiter, "On the computation
of the hull number of a graph", Discrete Mathematics 309 (2009), 5668-5674,
doi:10.1016/j.disc.2008.04.020 (general graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HullNumberBipartite

/-!
# HULL NUMBER OF BIPARTITE GRAPHS is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` (finite, simple, undirected) and a positive integer `K`.
QUESTION: is the hull number of `G` at most `K`, that is, is there a set `S ⊆ V` with `|S| ≤ K`
whose convex hull, in the geodetic convexity, is `V`?

Araujo, Campos, Giroire, Sampaio and Soares (abstract): "Given a graph `G = (V, E)`, the closed
interval of a pair of vertices `u, v ∈ V`, denoted by `I[u, v]`, is the set of vertices that
belongs to some shortest `(u, v)`-path. For a given `S ⊆ V`, let `I[S] = ⋃_{u,v∈S} I[u, v]`. We say
that `S ⊆ V` is a convex set if `I[S] = S`. The convex hull `I_h[S]` of a subset `S ⊆ V` is the
smallest convex set that contains `S`. We say that `S` is a hull set if `I_h[S] = V`. … We show
that deciding if `hn(G) ⩽ k` is an NP-complete problem, even if `G` is bipartite." Dourado et
al. had proved NP-completeness for general graphs.

The graph is given by its vertex count and a simple edge list (`Cslib.Complexity.Karp.edgeGraph`).
A shortest `(u, v)`-path is a walk `p : G.Walk u v` of length `G.dist u v` (Mathlib), so `w` lies
in `I[u, v]` when it is on the support of such a walk. Since `S ⊆ I[S]` always (`I[u, u] = {u}`),
`S` is convex exactly when `I[S] ⊆ S`. The convex hull of `S` is `V` exactly when the only
convex set containing `S` is `V`, which is how the question states it. Bipartiteness is Mathlib's
`SimpleGraph.IsBipartite` (2-colorability). The source's graphs need not be connected; for two
vertices in different components there is no `(u, v)`-path and `I[u, v]` adds nothing.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **HULL NUMBER is NP-complete on bipartite graphs.** Source: Araujo, Campos, Giroire,
Sampaio and Soares (2011); Dourado, Gimbel, Kratochvíl, Protti and Szwarcfiter (2009). -/
public theorem_wanted hullNumberBipartite_npComplete :
    hullNumberBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hullNumberBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.HullNumberBipartite
