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

public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrowPushout

/-!
# Cobase-change stability of genuine cofibration-arrow cofibrations

The existing actual relative pushout presentation supplies the standard
morphism-property stability proof. This is a named proof value, with no
Waldhausen or stability instance installed globally.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Genuine relative cofibrations of cofibration arrows are stable under
every actual cobase change, by the original whole pushout presentation. -/
theorem cofibrationArrowCofibrationsCobaseChange :
    (cofibrationArrowCofibrations C).IsStableUnderCobaseChange :=
  MorphismProperty.IsStableUnderCobaseChange.of_forall_exists_isPullback <| by
    intro X Y Z f g _ hf
    let P := CofibrationArrowPushoutPresentation.ofRelativeCofibration (C := C) f g hf
    exact ⟨P.apex, P.inr, P.inl, P.isPushout.flip, P.inl_relative⟩

end CategoryTheory.Waldhausen
