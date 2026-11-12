/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.KWSelfDuality

/-!
# Even subgraphs under graph isomorphisms

Even subgraphs form a group under symmetric difference and are transported by graph isomorphisms.

## i. Overview

Even subgraphs contain `∅` and are closed under symmetric difference. A graph isomorphism `Gp ≃g Gd`
maps the even subgraphs of `Gp` bijectively onto those of `Gd`, preserving size, so the
high-temperature sums of the two graphs agree. This gives the duality of partition functions for a
self-dual pair under a scalar identity.

## ii. Key results

- `StatMech.Ising.isEvenSubgraph_symmDiff` : symmetric differences of even subgraphs are even
- `StatMech.Ising.transportEdges` : edge sets transported by a vertex equivalence
- `StatMech.Ising.selfDual_evenSubgraph_tanh_sum_eq` : isomorphic graphs have equal even-subgraph
  sums
- `StatMech.Ising.isingZ_self_dual_of_cycleSpace` : duality for isomorphic graphs under a scalar
  identity

## iii. Table of contents

- A. The cycle space
- B. Transport along isomorphisms

## iv. References

- H. A. Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys.
  Rev. 60 (1941) 252–262
-/

@[expose] public section

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising

section CycleSpace

variable {V : Type*} [DecidableEq V]

lemma incCount_symmDiff_mod_two (A B : Finset (Sym2 V)) (v : V) :
    incCount (symmDiff A B) v % 2 = (incCount A v + incCount B v) % 2 := by
  unfold incCount
  have hf : (symmDiff A B).filter (fun e => v ∈ e)
      = symmDiff (A.filter (fun e => v ∈ e)) (B.filter (fun e => v ∈ e)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  set FA := A.filter (fun e => v ∈ e)
  set FB := B.filter (fun e => v ∈ e)
  rw [symmDiff_def, Finset.sup_eq_union,
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 := Finset.card_inter_add_card_sdiff FA FB
  have h2 := Finset.card_inter_add_card_sdiff FB FA
  rw [Finset.inter_comm] at h2
  omega

/-! ## A. The cycle space -/

lemma isEvenSubgraph_empty : IsEvenSubgraph (∅ : Finset (Sym2 V)) := by
  intro v; simp [incCount]

lemma isEvenSubgraph_symmDiff {A B : Finset (Sym2 V)}
    (hA : IsEvenSubgraph A) (hB : IsEvenSubgraph B) :
    IsEvenSubgraph (symmDiff A B) := by
  intro v
  rw [Nat.even_iff, incCount_symmDiff_mod_two]
  have ha := (Nat.even_iff).mp (hA v)
  have hb := (Nat.even_iff).mp (hB v)
  omega

end CycleSpace

section Transport

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
lemma sym2map_injective (e : V ≃ W) : Function.Injective (Sym2.map e) := by
  intro x y h
  have h2 : Sym2.map e.symm (Sym2.map e x) = Sym2.map e.symm (Sym2.map e y) := by rw [h]
  rw [Sym2.map_map, Sym2.map_map, Equiv.symm_comp_self] at h2
  simpa using h2

/-! ## B. Transport along isomorphisms -/

/-- The image of an edge set under a vertex equivalence `V ≃ W`. -/
def transportEdges (e : V ≃ W) (F : Finset (Sym2 V)) : Finset (Sym2 W) :=
  F.image (Sym2.map e)

omit [DecidableEq V] in
lemma card_transportEdges (e : V ≃ W) (F : Finset (Sym2 V)) :
    (transportEdges e F).card = F.card :=
  Finset.card_image_of_injective F (sym2map_injective e)

lemma incCount_transportEdges (e : V ≃ W) (F : Finset (Sym2 V)) (v : V) :
    incCount (transportEdges e F) (e v) = incCount F v := by
  unfold incCount transportEdges
  rw [Finset.filter_image, Finset.card_image_of_injective _ (sym2map_injective e)]
  congr 1
  apply Finset.filter_congr
  intro s _
  have : (e v ∈ Sym2.map (⇑e) s) ↔ (v ∈ s) := by
    rw [Sym2.mem_map]
    refine ⟨?_, fun h => ⟨v, h, rfl⟩⟩
    rintro ⟨u, _, hfu⟩; rwa [← e.injective hfu]
  simp [this]

lemma isEvenSubgraph_transportEdges (e : V ≃ W) {F : Finset (Sym2 V)}
    (hF : IsEvenSubgraph F) : IsEvenSubgraph (transportEdges e F) := by
  intro w
  have h := incCount_transportEdges e F (e.symm w)
  rw [Equiv.apply_symm_apply] at h
  rw [h]; exact hF _

lemma transportEdges_symm_transportEdges (e : V ≃ W) (F : Finset (Sym2 V)) :
    transportEdges e.symm (transportEdges e F) = F := by
  unfold transportEdges
  rw [Finset.image_image]
  have hid : (Sym2.map e.symm ∘ Sym2.map e) = id := by
    funext s; simp [Function.comp, Sym2.map_map]
  rw [hid, Finset.image_id]

lemma transportEdges_transportEdges_symm (e : V ≃ W) (F : Finset (Sym2 W)) :
    transportEdges e (transportEdges e.symm F) = F := by
  have := transportEdges_symm_transportEdges e.symm F
  rwa [Equiv.symm_symm] at this

end Transport

section GraphIso

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G1 : SimpleGraph V} {G2 : SimpleGraph W} [DecidableRel G1.Adj] [DecidableRel G2.Adj]

omit [DecidableEq V] in
lemma transportEdges_subset_edgeFinset (φ : G1 ≃g G2) {F : Finset (Sym2 V)}
    (hF : F ⊆ G1.edgeFinset) :
    transportEdges φ.toEquiv F ⊆ G2.edgeFinset := by
  intro e he
  unfold transportEdges at he
  rw [Finset.mem_image] at he
  obtain ⟨s, hs, rfl⟩ := he
  have hsE : s ∈ G1.edgeSet := by rw [← SimpleGraph.mem_edgeFinset]; exact hF hs
  rw [SimpleGraph.mem_edgeFinset]
  induction s using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
    rw [SimpleGraph.mem_edgeSet] at hsE
    exact (Iso.map_adj_iff φ).mpr hsE

lemma transportEdges_mem_evenPowerset (φ : G1 ≃g G2)
    {F : Finset (Sym2 V)} (hF : F ∈ G1.edgeFinset.powerset.filter IsEvenSubgraph) :
    transportEdges φ.toEquiv F ∈ G2.edgeFinset.powerset.filter IsEvenSubgraph := by
  rw [Finset.mem_filter, Finset.mem_powerset] at hF ⊢
  exact ⟨transportEdges_subset_edgeFinset φ hF.1,
    isEvenSubgraph_transportEdges φ.toEquiv hF.2⟩

lemma evenSubgraph_tanh_sum_eq (φ : G1 ≃g G2) (t : ℝ) :
    (∑ F ∈ G2.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card)
      = ∑ F ∈ G1.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card := by
  symm
  apply Finset.sum_nbij'
    (i := transportEdges φ.toEquiv)
    (j := transportEdges φ.symm.toEquiv)
  · intro F hF
    exact transportEdges_mem_evenPowerset φ hF
  · intro F hF
    have : transportEdges φ.symm.toEquiv F
        ∈ G1.edgeFinset.powerset.filter IsEvenSubgraph := by
      have := transportEdges_mem_evenPowerset φ.symm hF
      simpa using this
    exact this
  · intro F _
    have : φ.symm.toEquiv = φ.toEquiv.symm := rfl
    rw [this]; exact transportEdges_symm_transportEdges φ.toEquiv F
  · intro F _
    have : φ.symm.toEquiv = φ.toEquiv.symm := rfl
    rw [this]; exact transportEdges_transportEdges_symm φ.toEquiv F
  · intro F _
    rw [card_transportEdges]

end GraphIso

section DischargeMatching

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]

lemma dualContourMatching_of_iso (φ : Gp ≃g Gd) (β βstar c : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hscalar : (2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        * ∑ F ∈ Gp.edgeFinset.powerset.filter IsEvenSubgraph,
            (Real.tanh βstar) ^ F.card
      = c * isingZ Gp β 0) :
    DualContourMatching Gp Gd β βstar c := by
  refine ⟨htemp, ?_⟩
  rw [evenSubgraph_tanh_sum_eq φ (Real.tanh βstar)]
  exact hscalar

lemma isingZ_self_dual_of_cycleSpace (φ : Gp ≃g Gd) (β βstar c : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hscalar : (2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        * ∑ F ∈ Gp.edgeFinset.powerset.filter IsEvenSubgraph,
            (Real.tanh βstar) ^ F.card
      = c * isingZ Gp β 0) :
    isingZ Gd βstar 0 = c * isingZ Gp β 0 :=
  isingZ_self_dual Gp Gd β βstar c
    (dualContourMatching_of_iso φ β βstar c htemp hscalar)

end DischargeMatching

section PlanarDual

open StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]

lemma selfDual_evenSubgraph_tanh_sum_eq (φ : Gp ≃g Gd) (t : ℝ) :
    (∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card)
      = ∑ F ∈ Gp.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card :=
  evenSubgraph_tanh_sum_eq φ t

end PlanarDual

end Ising

end StatMech
