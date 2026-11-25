/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleRetractionCombinatorics

@[expose] public section

set_option autoImplicit false

open CategoryTheory Simplicial

namespace AlgebraicTopology.EilenbergZilber.Shuffle

open AlgebraicTopology.AlexanderWhitney

theorem frontInclusion_comp_blockShuffle_leftHom (p q : ℕ) :
    frontInclusion p q (p + q) rfl ≫ (blockShuffle p q).leftHom = 𝟙 ⦋p⦌ := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq]
  rw [leftHom_val_eq_card_filter_leftPositions,
    frontInclusion_toOrderHom, leftPositions, Set.powersetCard.val_ofFinEmb,
    Finset.filter_map, Finset.card_map]
  change (Finset.univ.filter fun i : Fin p => i.val < k.val).card = k.val
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt_succ k.isLt)
theorem backInclusion_comp_blockShuffle_rightHom (p q : ℕ) :
    backInclusion p q (p + q) rfl ≫ (blockShuffle p q).rightHom = 𝟙 ⦋q⦌ := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq]
  rw [rightHom_val_eq_card_filter_rightPositions,
    backInclusion_toOrderHom, rightPositions, Set.powersetCard.val_ofFinEmb,
    Finset.filter_map, Finset.card_map]
  change (Finset.univ.filter fun j : Fin q => p + j.val < k.val + p).card = k.val
  rw [Nat.add_comm k.val p]
  simp only [Nat.add_lt_add_iff_left]
  rw [Fin.card_filter_val_lt]
  apply Nat.min_eq_right
  omega
theorem backInclusion_sub_comp_blockShuffle_rightHom (p q : ℕ) :
    backInclusion p (p + q - p) (p + q) (by omega) ≫
        (blockShuffle p q).rightHom =
      eqToHom (congrArg SimplexCategory.mk (Nat.add_sub_cancel_left p q)) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.eqToHom_toOrderHom, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply, Fin.val_cast]
  rw [rightHom_val_eq_card_filter_rightPositions,
    backInclusion_toOrderHom, rightPositions, Set.powersetCard.val_ofFinEmb,
    Finset.filter_map, Finset.card_map]
  change (Finset.univ.filter fun j : Fin q => p + j.val < k.val + p).card = k.val
  rw [Nat.add_comm k.val p]
  simp only [Nat.add_lt_add_iff_left]
  rw [Fin.card_filter_val_lt]
  apply Nat.min_eq_right
  omega
end AlgebraicTopology.EilenbergZilber.Shuffle
