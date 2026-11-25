/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproduct
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cofibrations of the genuine Waldhausen coproduct injections

The existing binary-coproduct cocone is derived from the original zero
pushout axiom. Its colimit universal property identifies the square from
zero as a pushout. Cobase-change stability of the original cofibrations
then proves both injections are cofibrations.

No exact structure, biproduct or caller-selected coproduct is needed.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

/-- Both injections of the existing binary-coproduct cocone derived from
Waldhausen zero pushouts are original base cofibrations. -/
theorem binaryCoproductColimitCocone_injections_isCofibration (X Y : C) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone;
    IsCofibration c.inl ∧ IsCofibration c.inr := by
  let c : BinaryCofan X Y := (binaryCoproductColimitCocone C (pair X Y)).cocone
  have hc : IsColimit c := (binaryCoproductColimitCocone C (pair X Y)).isColimit
  have hp' := IsPushout.of_is_coproduct hc (isZero_zero C).isInitial
  have hXmap : (isZero_zero C).isInitial.to X = (isZero_zero C).to_ X :=
    (isZero_zero C).eq_of_src _ _
  have hYmap : (isZero_zero C).isInitial.to Y = (isZero_zero C).to_ Y :=
    (isZero_zero C).eq_of_src _ _
  have hp : IsPushout ((isZero_zero C).to_ X) ((isZero_zero C).to_ Y) c.inl c.inr := by
    rw [hXmap, hYmap] at hp'
    exact hp'
  have hX : IsCofibration ((isZero_zero C).to_ X) :=
    WaldhausenCategory.zero_isCofibration X _
  have hY : IsCofibration ((isZero_zero C).to_ Y) :=
    WaldhausenCategory.zero_isCofibration Y _
  exact ⟨MorphismProperty.IsStableUnderCobaseChange.of_isPushout hp hY,
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hp.flip hX⟩

end CategoryTheory.Waldhausen
