/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib
import Code.Lattice.EulerFaces2
import Code.Onsager.Torus

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice (card_components_bot card_components_eq_one_of_connected)
open StatMech.Onsager


def torusQuarterTurn (L : ℕ) : (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun v := (v.2, -v.1)
  invFun v := (-v.2, v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

@[simp] theorem torusQuarterTurn_apply (L : ℕ) (v : ZMod L × ZMod L) :
    torusQuarterTurn L v = (v.2, -v.1) := rfl


theorem torusQuarterTurn_adj_iff (L : ℕ) [Fact (2 < L)]
    (u v : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusQuarterTurn L u) (torusQuarterTurn L v) ↔
      (onsTorusGraph L).Adj u v := by
  simp only [onsTorusGraph, onsTorusAdj, torusQuarterTurn_apply]
  constructor
  · rintro (⟨h, h' | h'⟩ | ⟨h, h' | h'⟩)
    · exact Or.inr ⟨h, Or.inr (by linear_combination -h')⟩
    · exact Or.inr ⟨h, Or.inl (by linear_combination -h')⟩
    · exact Or.inl ⟨by linear_combination -h, Or.inl h'⟩
    · exact Or.inl ⟨by linear_combination -h, Or.inr h'⟩
  · rintro (⟨h, h' | h'⟩ | ⟨h, h' | h'⟩)
    · exact Or.inr ⟨by linear_combination -h, Or.inl h'⟩
    · exact Or.inr ⟨by linear_combination -h, Or.inr h'⟩
    · exact Or.inl ⟨h, Or.inr (by linear_combination -h')⟩
    · exact Or.inl ⟨h, Or.inl (by linear_combination -h')⟩



def torusDualCutGraph (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : SimpleGraph (ZMod L × ZMod L) where
  Adj f g := (onsTorusGraph L).Adj f g ∧
    ¬ G.Adj (torusQuarterTurn L f) (torusQuarterTurn L g)
  symm := by
    rintro f g ⟨hfg, hwall⟩
    exact ⟨hfg.symm, fun h => hwall h.symm⟩
  loopless := ⟨fun f h => (onsTorusGraph L).irrefl h.1⟩

@[simp] theorem torusDualCutGraph_adj (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) (f g : ZMod L × ZMod L) :
    (torusDualCutGraph L G).Adj f g ↔
      (onsTorusGraph L).Adj f g ∧
        ¬ G.Adj (torusQuarterTurn L f) (torusQuarterTurn L g) := Iff.rfl


noncomputable def torusGeometricFaceCount (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℕ :=
  Nat.card (torusDualCutGraph L G).ConnectedComponent



noncomputable def torusGeometricDefect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℤ :=
  (G.edgeSet.ncard : ℤ) - Nat.card (ZMod L × ZMod L) +
    Nat.card G.ConnectedComponent + 1 - torusGeometricFaceCount L G


theorem geometric_euler_torus (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusGeometricFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - torusGeometricDefect L G := by
  unfold torusGeometricDefect
  ring


theorem geometric_euler_torus_of_defect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) (δ : ℕ)
    (hδ : torusGeometricDefect L G = δ) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusGeometricFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - δ := by
  rw [geometric_euler_torus L G, hδ]


theorem torusDualCutGraph_le (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    torusDualCutGraph L G ≤ onsTorusGraph L := fun _ _ h => h.1


theorem torusDualCutGraph_anti (L : ℕ) [Fact (2 < L)]
    {G H : SimpleGraph (ZMod L × ZMod L)} (hGH : G ≤ H) :
    torusDualCutGraph L H ≤ torusDualCutGraph L G := by
  rintro f g ⟨hfg, hclosed⟩
  exact ⟨hfg, fun hopen => hclosed (hGH hopen)⟩


theorem torusGeometricFaceCount_mono (L : ℕ) [Fact (2 < L)]
    {G H : SimpleGraph (ZMod L × ZMod L)} (hGH : G ≤ H) :
    torusGeometricFaceCount L G ≤ torusGeometricFaceCount L H := by
  unfold torusGeometricFaceCount
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le
    (torusDualCutGraph_anti L hGH)


@[simp] theorem torusDualCutGraph_bot (L : ℕ) [Fact (2 < L)] :
    torusDualCutGraph L (⊥ : SimpleGraph (ZMod L × ZMod L)) = onsTorusGraph L := by
  ext f g
  simp [torusDualCutGraph]


theorem torusDualCutGraph_full (L : ℕ) [Fact (2 < L)] :
    torusDualCutGraph L (onsTorusGraph L) = ⊥ := by
  ext f g
  simp only [torusDualCutGraph_adj, bot_adj, iff_false]
  rintro ⟨hfg, hclosed⟩
  exact hclosed ((torusQuarterTurn_adj_iff L f g).2 hfg)


theorem torusGeometricFaceCount_full (L : ℕ) [Fact (2 < L)] :
    torusGeometricFaceCount L (onsTorusGraph L) = L ^ 2 := by
  unfold torusGeometricFaceCount
  rw [torusDualCutGraph_full, card_components_bot]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  ring



theorem torusGeometricFaceCount_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricFaceCount L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 1 := by
  unfold torusGeometricFaceCount
  rw [torusDualCutGraph_bot, card_components_eq_one_of_connected hconn]



theorem torusGeometricDefect_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricDefect L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 0 := by
  have h := geometric_euler_torus L (⊥ : SimpleGraph (ZMod L × ZMod L))
  rw [torusGeometricFaceCount_bot L hconn, card_components_bot] at h
  simp only [SimpleGraph.edgeSet_bot, Set.ncard_empty, Nat.cast_zero, sub_zero] at h
  norm_num at h
  linarith



theorem torusGeometricDefect_full (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricDefect L (onsTorusGraph L) = 2 := by
  have hedge : (onsTorusGraph L).edgeSet.ncard = 2 * L ^ 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact onsTorus_card_edges L
  unfold torusGeometricDefect
  rw [hedge, card_components_eq_one_of_connected hconn, torusGeometricFaceCount_full]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  push_cast
  ring

end StatMech.BeffaraDC
