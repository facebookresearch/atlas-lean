/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Lattice.EulerFaces2

open SimpleGraph Set



set_option linter.unusedSectionVars false

namespace StatMech.Lattice

variable {V : Type*} [Finite V] [DecidableEq V]








theorem isBridge_iff_not_reachable_deleteEdges (G : SimpleGraph V) {a b : V}
    (he : s(a, b) ∈ G.edgeSet) :
    G.IsBridge s(a, b) ↔ ¬ (G.deleteEdges {s(a, b)}).Reachable a b := by
  rw [isBridge_iff]
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  simp [hadj]











theorem faceCount_deleteEdges_of_not_isBridge (G : SimpleGraph V) {a b : V}
    (he : s(a, b) ∈ G.edgeSet) (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
    faceCount (G.deleteEdges {s(a, b)}) + 1 = faceCount G ∧
      Nat.card (G.deleteEdges {s(a, b)}).ConnectedComponent
        = Nat.card G.ConnectedComponent := by
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b he
  have hadjG : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  have hne_ab : a ≠ b := G.ne_of_adj hadjG
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  refine ⟨?_, ?_⟩
  · rw [hGeq]; exact (faceCount_sup_edge_of_reachable G' hne_ab hadj' hr).symm
  · rw [hGeq]; exact (card_components_sup_edge_of_reachable G' a b hr).symm








theorem faceCount_deleteEdges_of_isBridge (G : SimpleGraph V) {a b : V}
    (he : s(a, b) ∈ G.edgeSet) (hr : ¬ (G.deleteEdges {s(a, b)}).Reachable a b) :
    faceCount (G.deleteEdges {s(a, b)}) = faceCount G ∧
      Nat.card (G.deleteEdges {s(a, b)}).ConnectedComponent
        = Nat.card G.ConnectedComponent + 1 := by
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b he
  have hadjG : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  have hne_ab : a ≠ b := G.ne_of_adj hadjG
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  refine ⟨?_, ?_⟩
  · rw [hGeq]; exact (faceCount_sup_edge_of_not_reachable G' hne_ab hadj' hr).symm
  · 
    have h := card_components_sup_edge_of_not_reachable G' a b hr
    rw [hGeq]; omega




















theorem euler_general (G : SimpleGraph V) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G
      = 1 + Nat.card G.ConnectedComponent := by
  classical
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · 
      subst hz
      have hempty : G.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite G.edgeSet)).mp hn
      have hbot : G = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      have hfc : faceCount (⊥ : SimpleGraph V) = 1 := by
        unfold faceCount nullity; rw [card_components_bot]; simp [edgeSet_bot]
      rw [hfc, card_components_bot]; push_cast; ring
    · 
      have hnonempty : G.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hnonempty
      obtain ⟨a, b⟩ := e
      set G' := G.deleteEdges {s(a, b)} with hG'
      have hdrop : G'.edgeSet.ncard + 1 = G.edgeSet.ncard :=
        card_edgeSet_deleteEdges_add_one G a b he
      have hn' : G'.edgeSet.ncard = n - 1 := by omega
      
      have ihG' : (Nat.card V : ℤ) - G'.edgeSet.ncard + faceCount G'
          = 1 + Nat.card G'.ConnectedComponent := by
        have := ih (n - 1) (by omega) G' hn'; rwa [hn']
      have hncast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      rw [hn', hncast] at ihG'
      by_cases hr : G'.Reachable a b
      · 
        obtain ⟨hface, hcomp⟩ := faceCount_deleteEdges_of_not_isBridge G he hr
        have hface' : (faceCount G' : ℤ) + 1 = faceCount G := by exact_mod_cast hface
        have hcomp' : (Nat.card G'.ConnectedComponent : ℤ)
            = Nat.card G.ConnectedComponent := by exact_mod_cast hcomp
        linarith
      · 
        obtain ⟨hface, hcomp⟩ := faceCount_deleteEdges_of_isBridge G he hr
        have hface' : (faceCount G' : ℤ) = faceCount G := by exact_mod_cast hface
        have hcomp' : (Nat.card G'.ConnectedComponent : ℤ)
            = Nat.card G.ConnectedComponent + 1 := by exact_mod_cast hcomp
        linarith



theorem euler_general_nat (G : SimpleGraph V) :
    Nat.card V + faceCount G = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  have h := euler_general G
  have hcast : (Nat.card V : ℤ) + (faceCount G : ℤ)
      = (G.edgeSet.ncard : ℤ) + (Nat.card G.ConnectedComponent : ℤ) + 1 := by linarith
  exact_mod_cast hcast





theorem euler_general_connected {G : SimpleGraph V} (hG : G.Connected) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 := by
  have h := euler_general G
  rw [card_components_eq_one_of_connected hG] at h
  push_cast at h ⊢; linarith





theorem euler_general_disconnected_components (G : SimpleGraph V) :
    (Nat.card G.ConnectedComponent : ℤ)
      = (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G - 1 := by
  have h := euler_general G; linarith







theorem euler_general_eq_euler_relation_sub (G : SimpleGraph V) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G
      = Nat.card G.ConnectedComponent + 1 := by
  have h := euler_general G; linarith

























end StatMech.Lattice
