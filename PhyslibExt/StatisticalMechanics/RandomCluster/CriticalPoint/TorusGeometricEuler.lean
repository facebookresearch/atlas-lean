/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleRank
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.Torus

/-!
# Geometric Euler relation on the torus

The quarter-turn dual cut graph of a spanning subgraph of the torus, its face count and the
geometric defect.

## i. Overview

`torusDualCutGraph L G` puts the quarter-turn image of every torus edge absent from `G`. Its
component count is the geometric face count, and `torusGeometricDefect` is the failure of Euler's
formula. The face count is monotone in `G`; its values at the empty and full graphs are computed.
All results are unconditional, except those at the empty and full graphs, which take connectivity of
the torus as a hypothesis.

## ii. Key results

- `geometric_euler_torus`: `V - E + F = c - defect`.
- `torusGeometricDefect_full`: the full torus has defect `2`.

## iii. Table of contents

- A. Quarter turn
- B. Dual cut graph and face count
- C. Euler relation

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice (card_components_bot card_components_eq_one_of_connected)
open StatMech.Onsager

/-! ## A. Quarter turn -/

/-- The quarter turn `(x, y) ↦ (y, -x)` of the torus. -/
def torusQuarterTurn (L : ℕ) : (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun v := (v.2, -v.1)
  invFun v := (-v.2, v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

@[simp] lemma torusQuarterTurn_apply (L : ℕ) (v : ZMod L × ZMod L) :
    torusQuarterTurn L v = (v.2, -v.1) := rfl

lemma torusQuarterTurn_adj_iff (L : ℕ) [Fact (2 < L)]
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

/-! ## B. Dual cut graph and face count -/

/-- The dual cut graph: the quarter-turn image of every torus edge not in `G`. -/
def torusDualCutGraph (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : SimpleGraph (ZMod L × ZMod L) where
  Adj f g := (onsTorusGraph L).Adj f g ∧
    ¬ G.Adj (torusQuarterTurn L f) (torusQuarterTurn L g)
  symm := ⟨by
    rintro f g ⟨hfg, hwall⟩
    exact ⟨hfg.symm, fun h => hwall h.symm⟩⟩
  loopless := ⟨fun f h => (onsTorusGraph L).irrefl h.1⟩

@[simp] lemma torusDualCutGraph_adj (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) (f g : ZMod L × ZMod L) :
    (torusDualCutGraph L G).Adj f g ↔
      (onsTorusGraph L).Adj f g ∧
        ¬ G.Adj (torusQuarterTurn L f) (torusQuarterTurn L g) := Iff.rfl

/-- The geometric face count of `G`: the number of components of its dual cut graph. -/
noncomputable def torusGeometricFaceCount (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℕ :=
  Nat.card (torusDualCutGraph L G).ConnectedComponent

/-- The geometric Euler defect `E + c - V - F` of a spanning subgraph of the torus. -/
noncomputable def torusGeometricDefect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) : ℤ :=
  (G.edgeSet.ncard : ℤ) - Nat.card (ZMod L × ZMod L) +
    Nat.card G.ConnectedComponent + 1 - torusGeometricFaceCount L G

/-! ## C. Euler relation -/

lemma geometric_euler_torus (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusGeometricFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - torusGeometricDefect L G := by
  unfold torusGeometricDefect
  ring

lemma geometric_euler_torus_of_defect (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) (δ : ℕ)
    (hδ : torusGeometricDefect L G = δ) :
    (Nat.card (ZMod L × ZMod L) : ℤ) - G.edgeSet.ncard +
        torusGeometricFaceCount L G =
      Nat.card G.ConnectedComponent + 1 - δ := by
  rw [geometric_euler_torus L G, hδ]

lemma torusDualCutGraph_le (L : ℕ) [Fact (2 < L)]
    (G : SimpleGraph (ZMod L × ZMod L)) :
    torusDualCutGraph L G ≤ onsTorusGraph L := fun _ _ h => h.1

lemma torusDualCutGraph_anti (L : ℕ) [Fact (2 < L)]
    {G H : SimpleGraph (ZMod L × ZMod L)} (hGH : G ≤ H) :
    torusDualCutGraph L H ≤ torusDualCutGraph L G := by
  rintro f g ⟨hfg, hclosed⟩
  exact ⟨hfg, fun hopen => hclosed (hGH hopen)⟩

lemma torusGeometricFaceCount_mono (L : ℕ) [Fact (2 < L)]
    {G H : SimpleGraph (ZMod L × ZMod L)} (hGH : G ≤ H) :
    torusGeometricFaceCount L G ≤ torusGeometricFaceCount L H := by
  unfold torusGeometricFaceCount
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le
    (torusDualCutGraph_anti L hGH)

@[simp] lemma torusDualCutGraph_bot (L : ℕ) [Fact (2 < L)] :
    torusDualCutGraph L (⊥ : SimpleGraph (ZMod L × ZMod L)) = onsTorusGraph L := by
  ext f g
  simp [torusDualCutGraph]

lemma torusDualCutGraph_full (L : ℕ) [Fact (2 < L)] :
    torusDualCutGraph L (onsTorusGraph L) = ⊥ := by
  ext f g
  simp only [torusDualCutGraph_adj, bot_adj, iff_false]
  rintro ⟨hfg, hclosed⟩
  exact hclosed ((torusQuarterTurn_adj_iff L f g).2 hfg)

lemma torusGeometricFaceCount_full (L : ℕ) [Fact (2 < L)] :
    torusGeometricFaceCount L (onsTorusGraph L) = L ^ 2 := by
  unfold torusGeometricFaceCount
  rw [torusDualCutGraph_full, card_components_bot]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  ring

lemma torusGeometricFaceCount_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricFaceCount L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 1 := by
  unfold torusGeometricFaceCount
  rw [torusDualCutGraph_bot, card_components_eq_one_of_connected hconn]

lemma torusGeometricDefect_bot (L : ℕ) [Fact (2 < L)]
    (hconn : (onsTorusGraph L).Connected) :
    torusGeometricDefect L (⊥ : SimpleGraph (ZMod L × ZMod L)) = 0 := by
  have h := geometric_euler_torus L (⊥ : SimpleGraph (ZMod L × ZMod L))
  rw [torusGeometricFaceCount_bot L hconn, card_components_bot] at h
  simp only [SimpleGraph.edgeSet_bot, Set.ncard_empty, Nat.cast_zero, sub_zero] at h
  norm_num at h
  linarith

lemma torusGeometricDefect_full (L : ℕ) [Fact (2 < L)]
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
