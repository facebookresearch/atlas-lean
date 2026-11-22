/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.DecorationFormalEval

/-!

# From the formal identity to the spin Kac-Ward identities

The formal Kac-Ward identity on the decorated torus implies the edge-weighted root identity, hence
the spin Kac-Ward identities.

## i. Overview

Evaluating the formal Kac-Ward identity at decorated weights that are `1` on internal edges and
equal to the torus edge weights on external edges identifies the walk-series square root of the
edge-weighted twisted Kac-Ward determinant with the edge-weighted character sum. This is the
edge-weighted root identity, which gives the spin Kac-Ward identities for all `β`.

## ii. Key results

- `ons_weightedRootIdentity_of_decoratedFormal` : the formal identity implies the root identity
- `ons_spinKacWardIdentities_of_decoratedFormal` : the formal identity implies the spin Kac-Ward
  identities

## iii. Table of contents

- A. Assembly

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

namespace StatMech.Onsager

open BigOperators StatMech.Ising

/-! ## A. Assembly -/

lemma ons_weightedRootIdentity_of_decoratedFormal
    (L : ℕ) [Fact (2 < L)]
    (hformal : ons_decoratedFormalKacWardIdentity L) :
    ons_weightedRootIdentity L := by
  intro a b weight q hq hweight hsmall
  have hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1 :=
    ons_card_mul_lt_one_of_Sherman_small q hsmall
  have hcardPos : 0 < Fintype.card (ons_Dart L) := Fintype.card_pos
  have hcardOne : (1 : ℝ) ≤ Fintype.card (ons_Dart L) := by
    exact_mod_cast hcardPos
  have hqOne : q ≤ 1 := by
    have hqCard : q ≤ (Fintype.card (ons_Dart L) : ℝ) * q := by
      nlinarith
    exact le_of_lt (hqCard.trans_lt hcard)
  let decWeight : ons_DecEdge L → ℂ := ons_decSpecializedWeight weight
  have hall : ∀ edge, ‖decWeight edge‖ ≤ 1 := by
    intro edge
    classical
    unfold decWeight ons_decSpecializedWeight
    split
    · exact (hweight _).trans hqOne
    · simp
  have hext : ∀ d,
      ‖decWeight s(d, ons_dartRev L d)‖ ≤ q := by
    intro d
    simpa only [decWeight, ons_decSpecializedWeight_external] using
      hweight (ons_portEdge L d)
  have hroot :=
    ons_detWalkRoot_eq_decoratedFullWeightedSpinSum_of_formal
      L hformal decWeight a b q hq hall hext hcard
  rw [ons_KWmatDecorationWeightedPhase_specialized,
    ons_decoratedFullWeightedSpinSum_specialized] at hroot
  exact hroot

lemma ons_spinKacWardIdentities_of_decoratedFormal
    (hformal : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_decoratedFormalKacWardIdentity L)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_weightedRoot
  intro L hL
  let : Fact (2 < L) := ⟨hL⟩
  exact ons_weightedRootIdentity_of_decoratedFormal L (hformal L hL)

end StatMech.Onsager
