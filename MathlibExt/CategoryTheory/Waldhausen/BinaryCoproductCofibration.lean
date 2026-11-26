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
# Cofibrations of Waldhausen coproduct injections

In a category C with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms, the chosen coproduct
X⊔Y is a pushout of 0 → X and 0 → Y.
Both maps from zero are cofibrations, so the two coproduct injections
X → X⊔Y and Y → X⊔Y are cofibrations.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms.

For the binary coproduct cocone supplied by the zero-source pushout of X and Y, both injections are cofibrations. -/
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
    WaldhausenCategoryWithoutGluing.zero_isCofibration X _
  have hY : IsCofibration ((isZero_zero C).to_ Y) :=
    WaldhausenCategoryWithoutGluing.zero_isCofibration Y _
  exact ⟨MorphismProperty.IsStableUnderCobaseChange.of_isPushout hp hY,
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hp.flip hX⟩

end CategoryTheory.Waldhausen
