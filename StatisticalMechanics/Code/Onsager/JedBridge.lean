/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.Onsager.InsideClimb
import Code.Lattice.JordanEnclosureDuality

namespace StatMech.Onsager.JedBridge

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity StatMech.Onsager.InsideClimb
open StatMech.Lattice
open SimpleGraph




def posSite {m : ℕ} (d : Fin (m + 3) → Fin 4) (i : Fin (m + 3)) : Site 2 :=
  ![(pos d i).1, (pos d i).2]

@[simp] theorem posSite_zero {m : ℕ} (d : Fin (m + 3) → Fin 4) (i : Fin (m + 3)) :
    (posSite d i) 0 = (pos d i).1 := rfl

@[simp] theorem posSite_one {m : ℕ} (d : Fin (m + 3) → Fin 4) (i : Fin (m + 3)) :
    (posSite d i) 1 = (pos d i).2 := rfl


theorem posSite_injective {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hsimple : Function.Injective (pos d)) : Function.Injective (posSite d) := by
  intro i j h
  have h0 : (posSite d i) 0 = (posSite d j) 0 := by rw [h]
  have h1 : (posSite d i) 1 = (posSite d j) 1 := by rw [h]
  rw [posSite_zero, posSite_zero] at h0
  rw [posSite_one, posSite_one] at h1
  exact hsimple (Prod.ext h0 h1)


theorem stepOf_natAbs_sum (w : Fin 4) :
    (stepOf w).1.natAbs + (stepOf w).2.natAbs = 1 := by
  fin_cases w <;> rfl



theorem walk_isSub {m : ℕ} (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    ⦃i j : Fin (m + 3)⦄ (hadj : (cycleGraph (m + 3)).Adj i j) :
    (hypercubicLattice 2).Adj (posSite d i) (posSite d j) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  rw [cycleGraph_adj] at hadj
  rcases hadj with h | h
  · 
    have hij : j + 1 = i := (add_comm j 1).trans (sub_eq_iff_eq_add.mp h).symm
    have hs := pos_succ d hclosed j
    rw [hij] at hs
    have e0 : (posSite d i) 0 - (posSite d j) 0 = (stepOf (d j)).1 := by
      rw [posSite_zero, posSite_zero, hs, Prod.fst_add]; ring
    have e1 : (posSite d i) 1 - (posSite d j) 1 = (stepOf (d j)).2 := by
      rw [posSite_one, posSite_one, hs, Prod.snd_add]; ring
    rw [e0, e1]; exact stepOf_natAbs_sum (d j)
  · 
    have hji : i + 1 = j := (add_comm i 1).trans (sub_eq_iff_eq_add.mp h).symm
    have hs := pos_succ d hclosed i
    rw [hji] at hs
    have e0 : (posSite d i) 0 - (posSite d j) 0 = -(stepOf (d i)).1 := by
      rw [posSite_zero, posSite_zero, hs, Prod.fst_add]; ring
    have e1 : (posSite d i) 1 - (posSite d j) 1 = -(stepOf (d i)).2 := by
      rw [posSite_one, posSite_one, hs, Prod.snd_add]; ring
    rw [e0, e1, Int.natAbs_neg, Int.natAbs_neg]; exact stepOf_natAbs_sum (d i)



noncomputable def walkSubgraph {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    PlanarZ2Subgraph where
  V := Fin (m + 3)
  finV := inferInstance
  decV := inferInstance
  G := cycleGraph (m + 3)
  emb := ⟨posSite d, posSite_injective d hsimple⟩
  isSub := walk_isSub d hclosed




theorem cycleGraph_card_components_one (m : ℕ) :
    Nat.card (cycleGraph (m + 3)).ConnectedComponent = 1 := by
  have hconn : (cycleGraph (m + 3)).Connected := cycleGraph_connected
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun c c' => ?_⟩, ⟨(cycleGraph (m + 3)).connectedComponentMk 0⟩⟩
  induction c using ConnectedComponent.ind with
  | _ u =>
    induction c' using ConnectedComponent.ind with
    | _ v => exact ConnectedComponent.sound (hconn.preconnected u v)


theorem cycleGraph_card_edges (m : ℕ) :
    (cycleGraph (m + 3)).edgeSet.ncard = m + 3 := by
  have hsum : ∑ v : Fin (m + 3), (cycleGraph (m + 3)).degree v
      = 2 * (cycleGraph (m + 3)).edgeFinset.card :=
    (cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : Fin (m + 3), (cycleGraph (m + 3)).degree v = 2 :=
    fun v => cycleGraph_degree_three_le
  rw [Finset.sum_congr rfl (fun v _ => hdeg v), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  have hcard : (cycleGraph (m + 3)).edgeFinset.card = m + 3 := by omega
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard]



theorem cycle_nullity_one (m : ℕ) : nullity (cycleGraph (m + 3)) = 1 := by
  unfold nullity
  rw [cycleGraph_card_edges m, cycleGraph_card_components_one m,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  omega


theorem walkSubgraph_nullity_one {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    nullity (walkSubgraph d hclosed hsimple).G = 1 := by
  show nullity (cycleGraph (m + 3)) = 1
  exact cycle_nullity_one m








theorem walk_one_bounded_region {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    Nat.card {c : (whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).ConnectedComponent
      // c.supp.Finite} = 1 := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan (walkSubgraph d hclosed hsimple)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin,
    walkSubgraph_nullity_one d hclosed hsimple]



theorem walk_faithfulRegionCount_one {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    whc_faithfulRegionCount (walkSubgraph d hclosed hsimple) = 1 :=
  walk_one_bounded_region d hclosed hsimple













def BridgeParityMembership {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) : Prop :=
  ∀ a b : ℤ, rayParity d a b = 1 ↔
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).connectedComponentMk
      ![a, b]).supp.Finite






def BridgeAdjacencyClimb {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) : Prop :=
  ∀ a b : ℤ,
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).Adj ![a, b] ![a + 1, b] ↔
      (∀ k : Fin (m + 3), isVertEdge (d k) → (pos d k).1 = a + 1 →
        ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧
           b < max ((pos d k).2) ((pos d (k + 1)).2)))) ∧
    ((whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).Adj ![a, b] ![a, b + 1] ↔
      (∀ k : Fin (m + 3), isHorizEdge (d k) →
        min ((pos d k).1) ((pos d (k + 1)).1) = a → (pos d k).2 ≠ b + 1))

end StatMech.Onsager.JedBridge
