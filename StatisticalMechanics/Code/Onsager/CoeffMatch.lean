/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Ising.EvenSubgraphDecomp
import Code.Onsager.HighTemp

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Onsager

open StatMech.Ising

section CoeffMatch



variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]








theorem ons_X_eq_sum_evenSubgraphs (x : ℝ) :
    ons_X G x = ∑ F ∈ evenSubgraphs G, x ^ F.card := by
  unfold ons_X evenSubgraphs
  rfl










theorem evenSubgraph_walk_decomp (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G) :
    ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V)
      (W : (i : ι) → G.Walk (w i) (w i)),
      F = s.biUnion (fun i => (W i).edges.toFinset) ∧
      (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) :=
  evenSubgraphWalkDecomp G F hF











theorem evenSubgraph_weight_factor (x : ℝ) (F : Finset (Sym2 V))
    (hF : F ∈ evenSubgraphs G) :
    ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V)
      (W : (i : ι) → G.Walk (w i) (w i)),
      F = s.biUnion (fun i => (W i).edges.toFinset) ∧
      (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) ∧
      x ^ F.card = ∏ i ∈ s, x ^ (W i).edges.toFinset.card := by
  obtain ⟨ι, hdec, s, w, W, hcov, hdisj⟩ := evenSubgraphWalkDecomp G F hF
  refine ⟨ι, hdec, s, w, W, hcov, hdisj, ?_⟩
  have hcard : F.card = ∑ i ∈ s, (W i).edges.toFinset.card := by
    rw [hcov]
    exact Finset.card_biUnion
      (fun i hi j hj hij => hdisj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hij)
  rw [hcard, Finset.prod_pow_eq_pow_sum]













theorem ons_X_eq_sum_prod_over_loops (x : ℝ) :
    ∃ f : Finset (Sym2 V) → ℝ,
      (∀ F ∈ evenSubgraphs G, ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι)
          (w : ι → V) (W : (i : ι) → G.Walk (w i) (w i)),
        F = s.biUnion (fun i => (W i).edges.toFinset) ∧
        (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) ∧
        f F = ∏ i ∈ s, x ^ (W i).edges.toFinset.card) ∧
      ons_X G x = ∑ F ∈ evenSubgraphs G, f F := by
  refine ⟨fun F => x ^ F.card, ?_, ons_X_eq_sum_evenSubgraphs G x⟩
  intro F hF
  exact evenSubgraph_weight_factor G x F hF






theorem incCount_le_degree (F : Finset (Sym2 V)) (hFsub : F ⊆ G.edgeFinset) (v : V) :
    incCount F v ≤ G.degree v := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  unfold incCount
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he
  rw [SimpleGraph.mem_incidenceFinset]
  refine ⟨?_, he.2⟩
  have : e ∈ G.edgeFinset := hFsub he.1
  rw [SimpleGraph.mem_edgeFinset] at this
  exact this









theorem incCount_eq_zero_or_two_of_trivalent (hdeg : ∀ v, G.degree v ≤ 3)
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G) (v : V) :
    incCount F v = 0 ∨ incCount F v = 2 := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hF
  obtain ⟨hFsub, hFev⟩ := hF
  have hle : incCount F v ≤ 3 := (incCount_le_degree G F hFsub v).trans (hdeg v)
  have hev : Even (incCount F v) := hFev v
  rw [Nat.even_iff] at hev
  omega

end CoeffMatch

end Onsager

end StatMech
