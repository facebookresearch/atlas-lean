/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Waldhausen.K0.Pushout
public import MathlibExt.CategoryTheory.Waldhausen.CofiberCobaseChange

public section
set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

namespace WaldhausenKTheory.K0.PushoutTests

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

/-- Every actual original pushout retains its same native relation without additive assumptions. -/
theorem original_relation {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z}
    {inY : Y ⟶ P} {inZ : Z ⟶ P} (hP : IsPushout i f inY inZ) (hi : IsCofibration i) :
    (K0.mk P : K0 C) + K0.mk X = K0.mk Y + K0.mk Z :=
  mk_add_mk_eq_of_isPushout hP hi

/-- The original two quotient rows have a common actual Q and the original descent legs. -/
theorem original_shared_quotient {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z}
    {inY : Y ⟶ P} {inZ : Z ⟶ P} (hP : IsPushout i f inY inZ) (hi : IsCofibration i) :
    ∃ (Q : C) (qY : Y ⟶ Q) (qP : P ⟶ Q),
      IsCofibrationSequence i qY ∧ IsCofibrationSequence inZ qP ∧ inY ≫ qP = qY := by
  obtain ⟨Q, _, _, _, qY, qP, _, _, hY, _, hSeqY, hSeqP⟩ :=
    CategoryTheory.exists_common_cofiber_of_isPushout hP hi
  exact ⟨Q, qY, qP, hSeqY, hSeqP, hY⟩

/-- The other original orientation uses the given opposite cofibration and its same pushout. -/
theorem original_other_orientation {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z}
    {inY : Y ⟶ P} {inZ : Z ⟶ P} (hP : IsPushout i f inY inZ) (hf : IsCofibration f) :
    (K0.mk P : K0 C) + K0.mk X = K0.mk Z + K0.mk Y :=
  mk_add_mk_eq_of_isPushout hP.flip hf

end WaldhausenKTheory.K0.PushoutTests

open WaldhausenKTheory WaldhausenKTheory.K0

example {C : Type 0} [Category.{2} C] [HasZeroObject C] [WaldhausenCategory C]
    {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hP : IsPushout i f inY inZ) (hi : IsCofibration i) :
    (K0.mk P : K0 C) + K0.mk X = K0.mk Y + K0.mk Z :=
  mk_add_mk_eq_of_isPushout hP hi

example {C : Type 2} [Category.{0} C] [HasZeroObject C] [WaldhausenCategory C]
    {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hP : IsPushout i f inY inZ) (hi : IsCofibration i) :
    (K0.mk P : K0 C) + K0.mk X = K0.mk Y + K0.mk Z :=
  mk_add_mk_eq_of_isPushout hP hi

end
