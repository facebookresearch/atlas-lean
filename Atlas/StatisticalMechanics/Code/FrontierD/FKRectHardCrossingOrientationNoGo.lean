/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCrossingAlgebra










namespace StatMech.FrontierD




structure FKRectWideCrossingScalarData
    (q hard easy : Real) : Prop where
  hard_nonneg : 0 <= hard
  hard_le_one : hard <= 1
  easy_nonneg : 0 <= easy
  easy_le_one : easy <= 1
  squareSeed : 1 / (1 + q) <= easy
  dualCover : 1 <= easy + q ^ 2 * hard
  sameOrientationQuadratic : hard ^ 2 / (1 + q ^ 2) <= easy



theorem FKRectWideCrossingScalarData.easy_ge_one_div_eight_mul_pow_six
    {q hard easy : Real} (hq : 1 <= q)
    (data : FKRectWideCrossingScalarData q hard easy) :
    1 / (8 * q ^ 6) <= easy :=
  crossing_vertical_ge_one_div_eight_mul_pow_six hq data.easy_nonneg
    data.dualCover data.sameOrientationQuadratic



theorem fkRectWideCrossingScalarData_zero_one
    {q : Real} (hq : 1 <= q) :
    FKRectWideCrossingScalarData q 0 1 := by
  constructor
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hden : 0 < 1 + q := by linarith
    rw [div_le_one hden]
    linarith
  · norm_num
  · norm_num



theorem not_exists_positive_hardFloor_of_wideCrossingScalarData
    {q : Real} (hq : 1 <= q) :
    ¬ (exists floor : Real, 0 < floor /\
      forall hard easy : Real,
        FKRectWideCrossingScalarData q hard easy -> floor <= hard) := by
  rintro ⟨floor, hfloor, hall⟩
  have hle := hall 0 1 (fkRectWideCrossingScalarData_zero_one hq)
  linarith



def FKRectWideCrossingReverseOrientationBridge
    (q hard easy : Real) : Prop :=
  easy ^ 2 / (1 + q ^ 2) <= hard


theorem exists_wideCrossingScalarData_not_reverseOrientationBridge
    {q : Real} (hq : 1 <= q) :
    exists hard easy : Real,
      FKRectWideCrossingScalarData q hard easy /\
        ¬ FKRectWideCrossingReverseOrientationBridge q hard easy := by
  refine ⟨0, 1, fkRectWideCrossingScalarData_zero_one hq, ?_⟩
  unfold FKRectWideCrossingReverseOrientationBridge
  have hden : 0 < 1 + q ^ 2 := by positivity
  rw [not_le, div_pos_iff]
  exact Or.inl ⟨by norm_num, hden⟩



theorem FKRectWideCrossingScalarData.hard_ge_of_reverseOrientationBridge
    {q hard easy : Real} (hq : 1 <= q)
    (data : FKRectWideCrossingScalarData q hard easy)
    (hreverse : FKRectWideCrossingReverseOrientationBridge q hard easy) :
    1 / (8 * q ^ 2) <= hard := by
  exact crossing_hard_ge_one_div_eight_mul_pow_two hq data.hard_nonneg
    data.dualCover hreverse

end StatMech.FrontierD
