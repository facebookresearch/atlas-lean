/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICLUSTER EDITING is NP-complete

Source:
N. Amit, "The bicluster graph editing problem", M.Sc. thesis, Tel Aviv University (2004),
supervised by R. Shamir (Section 1.4: the definitions of bicluster graphs, bicluster editing
sets and BICLUSTER GRAPH EDITING; Chapter 2, Theorem: "Bicluster Graph Editing is NP-complete",
by a reduction from exact cover by 3-sets).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Sum

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BiclusterEditing

/-!
# BICLUSTER EDITING is NP-complete

INSTANCE: a bipartite graph `G = (U, V, E)` and a nonnegative integer `K`.
QUESTION: is there a set `F ⊆ U × V` with `|F| ≤ K` such that `(U, V, E Δ F)` is a bicluster
graph, that is, every connected component of it is a biclique?

Amit (Section 1.4): "A bipartite graph `G = (U, V, E)` is called a bicluster graph if every
connected component of `G` is a biclique (a complete bipartite subgraph). Define
`E Δ F = (E \ F) ∪ (F \ E)`. If `G` is any bipartite graph and `F ⊂ U × V` is such that
`G' = (U, V, E Δ F)` is a bicluster graph, then `F` is called a bicluster editing set for `G`.
Bicluster Graph Editing: Given a bipartite graph `G` and an integer `k`, determine if `G` has a
bicluster editing set of size at most `k`." Single vertices are allowed as components ("a
singleton bicluster corresponds to a row or a column that does not intersect with any
submatrix"). Edits are pairs of `U × V` only, so the edited graph keeps the sides `U` and `V`.

The sides are `U = Fin p` and `V = Fin q`; the edge list holds pairs `(u, v)` with `u < p`,
`v < q`. Edge sets are `Finset (Fin p × Fin q)`, `E Δ F` is Mathlib's `symmDiff`, and
`bipartiteGraph F` is the graph on `Fin p ⊕ Fin q` with an edge between `u ∈ U` and `v ∈ V`
exactly when `(u, v) ∈ F`. As the sides of the edited graph are fixed, a connected component `C`
is a biclique exactly when every `u ∈ C ∩ U` is adjacent to every `v ∈ C ∩ V`: two vertices
`u ∈ U`, `v ∈ V` joined by a path (Mathlib's `Reachable`) are adjacent (`IsBiclusterGraph`).
Membership in NP: deleting all edges is a bicluster editing set of size `|E|`, so the answer is
yes when `K ≥ |E|`, and otherwise `F` has fewer than `|E|` pairs and is a certificate of size
polynomial in the input, although `p` and `q` are written in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the side sizes `p = |U|` and `q = |V|`, the edge list of pairs `(u, v)` with
`u ∈ U`, `v ∈ V`, and the bound `K`. -/
abbrev BiclusterEditingInstance := ℕ × ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: no repeated edge, and every edge `(u, v)` has `u < p` and
`v < q`. -/
def WellFormed (i : BiclusterEditingInstance) : Prop :=
  i.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2 < i.2.1

/-- The edge set `E ⊆ U × V` of the instance. -/
def edges (i : BiclusterEditingInstance) : Finset (Fin i.1 × Fin i.2.1) :=
  Finset.univ.filter fun e => ((e.1 : ℕ), (e.2 : ℕ)) ∈ i.2.2.1

/-- The bipartite graph on `U ⊕ V` with edge set `F ⊆ U × V`. -/
def bipartiteGraph {p q : ℕ} (F : Finset (Fin p × Fin q)) : SimpleGraph (Fin p ⊕ Fin q) :=
  SimpleGraph.fromRel fun a b => ∃ u v, a = Sum.inl u ∧ b = Sum.inr v ∧ (u, v) ∈ F

/-- `(U, V, F)` is a bicluster graph: every connected component is a biclique, i.e. any
`u ∈ U` and `v ∈ V` in the same connected component are adjacent. -/
def IsBiclusterGraph {p q : ℕ} (F : Finset (Fin p × Fin q)) : Prop :=
  ∀ u v, (bipartiteGraph F).Reachable (Sum.inl u) (Sum.inr v) → (u, v) ∈ F

/-- Some bicluster editing set `F ⊆ U × V` has at most `K` pairs: `(U, V, E Δ F)` is a
bicluster graph. -/
def BiclusterEditingFeasible (i : BiclusterEditingInstance) : Prop :=
  ∃ F : Finset (Fin i.1 × Fin i.2.1), F.card ≤ i.2.2.2 ∧ IsBiclusterGraph (symmDiff (edges i) F)

open Classical in
/-- BICLUSTER EDITING as a decision problem over bitstrings. -/
noncomputable def biclusterEditingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BiclusterEditingInstance) x with
  | some i => decide (WellFormed i ∧ BiclusterEditingFeasible i)
  | none => false

/-- **BICLUSTER EDITING is NP-complete.** Source: Amit (2004), Chapter 2. -/
public theorem_wanted biclusterEditing_npComplete :
    biclusterEditingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L biclusterEditingDec

end MetaMathlibExt.Complexity.NPComplete.BiclusterEditing
