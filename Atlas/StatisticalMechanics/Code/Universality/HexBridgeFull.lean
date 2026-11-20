/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexBridgeDecomp

namespace StatMech.Universality

open List
open HexWalk










def hxb_rungTurns (γ : List (ℕ × ℤ)) : List ℤ := γ.map Prod.snd

@[simp]
theorem hxb_rungTurns_nil : hxb_rungTurns [] = [] := rfl



@[simp]
theorem hxb_rungTurns_append (γ δ : List (ℕ × ℤ)) :
    hxb_rungTurns (γ ++ δ) = hxb_rungTurns γ ++ hxb_rungTurns δ := by
  simp [hxb_rungTurns]



@[simp]
theorem hxb_rungTurns_rungs (b : HexBridge) : hxb_rungTurns b.rungs = b.content := by
  simp [hxb_rungTurns, HexBridge.rungs, List.map_map]





noncomputable def hxb_walkOf (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) : HexWalk :=
  ofTurns a h0 (hxb_rungTurns γ)

@[simp]
theorem hxb_walkOf_turns (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) :
    (hxb_walkOf a h0 γ).turns = hxb_rungTurns γ := rfl

@[simp]
theorem hxb_walkOf_startMid (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) :
    (hxb_walkOf a h0 γ).startMid = a := rfl

@[simp]
theorem hxb_walkOf_h0 (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) :
    (hxb_walkOf a h0 γ).h0 = h0 := rfl




@[simp]
theorem hxb_walkOf_numVertices (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) :
    (hxb_walkOf a h0 γ).numVertices = γ.length + 1 := by
  simp [hxb_walkOf, hxb_rungTurns, numVertices]



theorem hxb_walkOf_turning (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) :
    (hxb_walkOf a h0 γ).turning = (Real.pi / 3) * ((hxb_rungTurns γ).sum : ℝ) := by
  simp [hxb_walkOf, hxb_rungTurns, turning, turnCount]











noncomputable def hxb_walkOfBridges (a : ℂ) (h0 : ℤ) (bs : List HexBridge) : HexWalk :=
  hxb_walkOf a h0 (bridgeRecompose bs)

@[simp]
theorem hxb_walkOfBridges_startMid (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).startMid = a := rfl

@[simp]
theorem hxb_walkOfBridges_h0 (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).h0 = h0 := rfl





theorem hxb_walkOfBridges_turns (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).turns = (bs.map HexBridge.content).flatten := by
  unfold hxb_walkOfBridges hxb_walkOf hxb_rungTurns bridgeRecompose
  simp only [ofTurns_turns]
  rw [List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  simp [HexBridge.rungs, List.map_map]



@[simp]
theorem hxb_walkOfBridges_nil (a : ℂ) (h0 : ℤ) :
    hxb_walkOfBridges a h0 [] = trivialWalk a h0 := by
  unfold hxb_walkOfBridges hxb_walkOf hxb_rungTurns
  simp [bridgeRecompose, trivialWalk, ofTurns]



@[simp]
theorem hxb_walkOfBridges_numVertices (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).numVertices = (bridgeRecompose bs).length + 1 := by
  rw [hxb_walkOfBridges, hxb_walkOf_numVertices]





theorem hxb_walkOfBridges_turning_cons (a : ℂ) (h0 : ℤ) (b : HexBridge) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 (b :: bs)).turning
      = (Real.pi / 3) * ((b.content).sum : ℝ)
        + (hxb_walkOfBridges a h0 bs).turning := by
  simp only [hxb_walkOfBridges, hxb_walkOf, hxb_rungTurns, turning, turnCount, ofTurns_turns,
    bridgeRecompose_cons, List.map_append, List.sum_append]
  have hb : (b.rungs.map Prod.snd).sum = b.content.sum := by
    simp [HexBridge.rungs, List.map_map]
  rw [hb]
  push_cast
  ring









def hxb_LegalRungs (γ : List (ℕ × ℤ)) : Prop := ∀ p ∈ γ, p.2 = 1 ∨ p.2 = -1




def hxb_LegalContents (bs : List HexBridge) : Prop :=
  ∀ b ∈ bs, ∀ t ∈ b.content, t = 1 ∨ t = -1



theorem hxb_walkOf_legalTurns_of_legalRungs (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ))
    (h : hxb_LegalRungs γ) : (hxb_walkOf a h0 γ).LegalTurns := by
  intro t ht
  simp only [hxb_walkOf, hxb_rungTurns, ofTurns_turns, List.mem_map] at ht
  obtain ⟨p, hp, rfl⟩ := ht
  exact h p hp



theorem hxb_legalRungs_recompose (bs : List HexBridge) (h : hxb_LegalContents bs) :
    hxb_LegalRungs (bridgeRecompose bs) := by
  intro p hp
  simp only [bridgeRecompose, List.mem_flatten, List.mem_map] at hp
  obtain ⟨_, ⟨c, hc, rfl⟩, hpc⟩ := hp
  simp only [HexBridge.rungs, List.mem_map] at hpc
  obtain ⟨t, ht, rfl⟩ := hpc
  exact h c hc t ht




theorem hxb_walkOfBridges_legalTurns (a : ℂ) (h0 : ℤ) (bs : List HexBridge)
    (h : hxb_LegalContents bs) : (hxb_walkOfBridges a h0 bs).LegalTurns :=
  hxb_walkOf_legalTurns_of_legalRungs a h0 (bridgeRecompose bs)
    (hxb_legalRungs_recompose bs h)













theorem hxb_walkOfBridges_nil_isLegalSAW (a : ℂ) (h0 : ℤ) :
    (hxb_walkOfBridges a h0 []).IsLegalSAW := by
  rw [hxb_walkOfBridges_nil]
  exact trivialWalk_isLegalSAW a h0


theorem hxb_walkOf_nil_isLegalSAW (a : ℂ) (h0 : ℤ) :
    (hxb_walkOf a h0 []).IsLegalSAW := by
  have : hxb_walkOf a h0 ([] : List (ℕ × ℤ)) = trivialWalk a h0 := by
    unfold hxb_walkOf hxb_rungTurns; simp [trivialWalk, ofTurns]
  rw [this]; exact trivialWalk_isLegalSAW a h0












theorem hxb_walkOf_isLegalSAW_of (a : ℂ) (h0 : ℤ) (bs : List HexBridge)
    (hlegal : hxb_LegalContents bs) (hsaw : (hxb_walkOfBridges a h0 bs).IsSAW) :
    (hxb_walkOfBridges a h0 bs).IsLegalSAW :=
  ⟨hxb_walkOfBridges_legalTurns a h0 bs hlegal, hsaw⟩














theorem hxb_walkOf_bridge_decomp (bs : {bs : List HexBridge // StrictDecreasingWidths bs})
    (a : ℂ) (h0 : ℤ) :
    hxb_walkOf a h0 (hexHW_bridge_decomp bs : List (ℕ × ℤ))
      = hxb_walkOfBridges a h0 bs.1 := by
  rw [hexHW_bridge_decomp_apply]
  rfl






theorem hxb_walkOf_valid_eq_bridges (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ))
    (hv : hexHW_IsValidWalk γ) :
    ∃ bs, StrictDecreasingWidths bs ∧ hxb_walkOf a h0 γ = hxb_walkOfBridges a h0 bs := by
  obtain ⟨bs, hbs, hrec⟩ := hv
  exact ⟨bs, hbs, by rw [hxb_walkOfBridges, hrec]⟩

end StatMech.Universality
