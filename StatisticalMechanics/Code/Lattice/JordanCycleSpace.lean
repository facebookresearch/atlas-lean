/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.Lattice.EulerGeneral
import Code.Lattice.CrossingParity
import Code.Lattice.JordanContour
import Code.Lattice.JordanCoresUnify

open SimpleGraph Set List Function

namespace StatMech

namespace Lattice













theorem jcs_support_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) : c.support.toFinset.card = c.length := by
  have h3 := hc.three_le_length
  have hslen : c.support.length = c.length + 1 := Walk.length_support c
  have hsupp : c.support = v :: c.support.tail := (Walk.cons_tail_support c).symm
  have htlen : c.support.tail.length = c.length := by
    have h' : (v :: c.support.tail).length = c.length + 1 := hsupp ▸ hslen
    simp only [List.length_cons] at h'; omega
  have hvtail : v ∈ c.support.tail := by
    have hgl : c.support.getLast? = some v := by
      rw [List.getLast?_eq_some_getLast (Walk.support_ne_nil c), c.getLast_support]
    have : c.support.tail.getLast? = some v := by
      rw [List.getLast?_tail, if_neg (by omega), hgl]
    exact List.mem_of_getLast? this
  rw [hsupp, List.toFinset_cons, Finset.insert_eq_self.mpr (by simp [hvtail]),
    List.toFinset_card_of_nodup hc.support_nodup, htlen]



theorem jcs_coe_mem {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) (e : Sym2 H.verts)
    (he : e ∈ H.coe.edgeSet) : Sym2.map Subtype.val e ∈ H.edgeSet := by
  rw [Subgraph.edgeSet_coe] at he; exact he



theorem jcs_coe_mem' {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) (e : Sym2 H.verts)
    (he : Sym2.map Subtype.val e ∈ H.edgeSet) : e ∈ H.coe.edgeSet := by
  rw [Subgraph.edgeSet_coe]; exact he





theorem jcs_coe_edge_card {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) :
    Nat.card H.coe.edgeSet = Nat.card H.edgeSet := by
  apply Nat.card_eq_of_bijective (fun e => ⟨Sym2.map Subtype.val e.1, jcs_coe_mem H e.1 e.2⟩)
  refine ⟨?_, ?_⟩
  · rintro ⟨e, he⟩ ⟨e', he'⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact Sym2.map.injective Subtype.val_injective h
  · rintro ⟨e, he⟩
    induction e with
    | h a b =>
      have ha : a ∈ H.verts := H.mem_verts_of_mem_edge he (by simp)
      have hb : b ∈ H.verts := H.mem_verts_of_mem_edge he (by simp)
      exact ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), jcs_coe_mem' H _ (by simpa using he)⟩,
        by simp only [Subtype.mk.injEq]; rfl⟩



theorem jcs_walk_edgeSet_ncard {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) : c.edgeSet.ncard = c.length := by
  classical
  have : c.edgeSet = (↑c.edges.toFinset : Set (Sym2 V)) := by ext e; simp [Walk.edgeSet]
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hc.edges_nodup, Walk.length_edges]


instance jcs_verts_finite {V : Type*} {G : SimpleGraph V} {u w : V} (c : G.Walk u w) :
    Finite ↑c.toSubgraph.verts := by
  rw [c.verts_toSubgraph]; exact (c.support.finite_toSet).to_subtype








theorem jcs_cycle_nullity_eq_one {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    nullity c.toSubgraph.coe = 1 := by
  classical
  haveI : DecidableEq V := Classical.decEq V
  haveI : Finite ↑c.toSubgraph.verts := jcs_verts_finite c
  have hvcard : Nat.card ↑c.toSubgraph.verts = c.length := by
    rw [c.verts_toSubgraph,
      show {x | x ∈ c.support} = (↑c.support.toFinset : Set V) by ext x; simp,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, jcs_support_card c hc]
  have hecard : c.toSubgraph.coe.edgeSet.ncard = c.length := by
    rw [← Nat.card_coe_set_eq, jcs_coe_edge_card c.toSubgraph,
      c.edgeSet_toSubgraph, Nat.card_coe_set_eq, jcs_walk_edgeSet_ncard c hc]
  have hccard : Nat.card c.toSubgraph.coe.ConnectedComponent = 1 :=
    card_components_eq_one_of_connected (Subgraph.connected_iff'.mp c.toSubgraph_connected)
  have h3 := hc.three_le_length
  unfold nullity
  rw [hccard, hecard, hvcard]
  omega








theorem jcs_cycle_faceCount_eq_two {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 := by
  unfold faceCount; rw [jcs_cycle_nullity_eq_one c hc]






theorem jcs_cycle_euler {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    (Nat.card ↑c.toSubgraph.verts : ℤ) - c.toSubgraph.coe.edgeSet.ncard + 2
      = 1 + Nat.card c.toSubgraph.coe.ConnectedComponent := by
  classical
  haveI : DecidableEq ↑c.toSubgraph.verts := Classical.decEq _
  have h := euler_general c.toSubgraph.coe
  rw [jcs_cycle_faceCount_eq_two c hc] at h
  exact_mod_cast h
























theorem jcs_two_components_of_sides (S : Set (Site 2)) {x y : Site 2} (hx : x ∈ S) (hy : y ∉ S)
    (hin : ∀ a b : Site 2, a ∈ S → b ∈ S → (latticeMinusBarrier S).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ S → b ∉ S → (latticeMinusBarrier S).Reachable a b) :
    Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
  classical
  set L := latticeMinusBarrier S with hL
  let f : L.ConnectedComponent → Bool :=
    ConnectedComponent.lift (fun a => decide (a ∈ S)) (by
      intro a b p _
      have : (a ∈ S ↔ b ∈ S) := barrier_sameSide_of_reachable S ⟨p⟩
      simp only [decide_eq_decide]; exact this)
  have hf_mk : ∀ a : Site 2, f (L.connectedComponentMk a) = decide (a ∈ S) := fun _ => rfl
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · refine ConnectedComponent.ind₂ ?_
      intro a b hab
      rw [hf_mk, hf_mk, decide_eq_decide] at hab
      rw [ConnectedComponent.eq]
      by_cases haS : a ∈ S
      · exact hin a b haS (hab.mp haS)
      · exact hout a b haS (fun hbS => haS (hab.mpr hbS))
    · intro c
      cases c with
      | true => exact ⟨L.connectedComponentMk x, by rw [hf_mk]; simp [hx]⟩
      | false => exact ⟨L.connectedComponentMk y, by rw [hf_mk]; simp [hy]⟩
  rw [Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_bool]


















def jcs_JordanRegion (S : Set (Site 2)) : Prop :=
  (∃ x, x ∈ S) ∧ (∃ y, y ∉ S) ∧
    (∀ a b : Site 2, a ∈ S → b ∈ S → (latticeMinusBarrier S).Reachable a b) ∧
    (∀ a b : Site 2, a ∉ S → b ∉ S → (latticeMinusBarrier S).Reachable a b)




theorem jcs_two_components_of_region {S : Set (Site 2)} (h : jcs_JordanRegion S) :
    Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hin, hout⟩ := h
  exact jcs_two_components_of_sides S hx hy hin hout










theorem jcs_separatingSide {D B inside outside : Set (Site 2)} (S : Set (Site 2))
    (hin : ∀ z ∈ inside, z ∈ S) (hout : ∀ z ∈ outside, z ∉ S)
    (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B)) :
    jcu_HasSeparatingSide D B inside outside :=
  ⟨S, hin, hout, hbd⟩







theorem jcs_separatingSide_forces_cross {D B inside outside : Set (Site 2)} (S : Set (Site 2))
    (hinS : ∀ z ∈ inside, z ∈ S) (houtS : ∀ z ∈ outside, z ∉ S)
    (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B))
    {x y : Site 2} (hx : x ∈ inside) (hy : y ∈ outside)
    (w : (hypercubicLattice 2).Walk x y) (hwD : ∀ z ∈ w.support, z ∈ D) :
    ∃ z ∈ w.support, z ∈ B :=
  jcu_separatingSide_forces_cross (jcs_separatingSide S hinS houtS hbd) hx hy w hwD

























def jcs_GeometricBridge (S : Set (Site 2)) : Prop := jcs_JordanRegion S













theorem jcs_cycle_two_components {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) (S : Set (Site 2)) (hbridge : jcs_GeometricBridge S) :
    faceCount c.toSubgraph.coe = 2 ∧
      Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 :=
  ⟨jcs_cycle_faceCount_eq_two c hc, jcs_two_components_of_region hbridge⟩










theorem jcs_separatingSide_of_bridge {D B inside outside : Set (Site 2)} (S : Set (Site 2))
    (hbridge : jcs_GeometricBridge S)
    (hinS : ∀ z ∈ inside, z ∈ S) (houtS : ∀ z ∈ outside, z ∉ S)
    (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B)) :
    jcu_HasSeparatingSide D B inside outside ∧
      Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 :=
  ⟨jcs_separatingSide S hinS houtS hbd, jcs_two_components_of_region hbridge⟩







































end Lattice

end StatMech
