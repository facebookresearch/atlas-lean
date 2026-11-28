/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BICLUSTER EDITING: definitions

Source:
N. Amit, "The bicluster graph editing problem", M.Sc. thesis, Tel Aviv University (2004),
supervised by R. Shamir (Section 1.4: the definitions of bicluster graphs, bicluster editing
sets and BICLUSTER GRAPH EDITING; Chapter 2, Theorem: "Bicluster Graph Editing is NP-complete",
by a reduction from exact cover by 3-sets).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Sum

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BiclusterEditing

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

end MetaMathlibExt.Complexity.NPComplete.BiclusterEditing
