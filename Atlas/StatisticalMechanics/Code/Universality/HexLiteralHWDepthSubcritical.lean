/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Universality.HexLiteralHWDepthAugment
import Code.Universality.HexLiteralHWDepthTagged
import Code.Universality.HexCorrectedStripWindow

namespace StatMech.Universality

open HexWalk

noncomputable section



noncomputable def hlhds_twoHalfData (N : ℕ) :
    HLHDTaggedTwoHalfData hexAWStart 1 N 4 where
  lower := fun d => hlhda_prefixAugment d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  upper := fun d => hlhda_suffixAugment d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  lower_legal := fun d => hlhda_prefixAugment_isLegalSAW d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  upper_legal := fun d => hlhda_suffixAugment_isLegalSAW d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  lower_halfSpace := fun d => hlhda_prefixAugment_halfSpace d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  upper_halfSpace := fun d => hlhda_suffixAugment_halfSpace d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  pair_injective := by
    intro d e hpair
    apply Subtype.ext
    apply hlhda_augmentedPair_injective
      (hhc_Dn_spec hexAWStart 1 N d).1
      (hhc_Dn_spec hexAWStart 1 N e).1
    simpa only [hlhda_augmentedPair] using hpair
  length_add := by
    intro d
    simpa only [hlhda_augmentedPair] using
      hlhda_augmentedPair_length d.1
        (hhc_Dn_spec hexAWStart 1 N d).1


theorem hlhds_hexChiE_lt_one : hexChiE < 1 := by
  unfold hexChiE
  rw [div_lt_one hex_sqrt_pos]
  calc
    (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt (2 + Real.sqrt 2) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      have hs := Real.sqrt_nonneg 2
      linarith




theorem hlhds_summable_of_local
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
    ∀ x, 0 < x → x < hexChiE →
      Summable (fun n => hlc_sawCountR hexAWStart 1 n * x ^ n) := by
  intro x hx hxchi
  apply HLHDTaggedTwoHalfData.summable_of_taggedTwoHalfData
    (fun N => hlhds_twoHalfData N)
    hx (le_of_lt (lt_trans hxchi hlhds_hexChiE_lt_one)) hxchi
  · intro T hT L
    exact hlocal T L hT
  · intro T hT L
    exact hexCS_boundaryWindowLaw T L hT

end

end StatMech.Universality
