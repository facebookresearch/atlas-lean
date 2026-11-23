/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The same cofiber after actual cofibration cobase change

The original quotient of a given cofibration also quotients its actual
pushout inclusion. Both cofiber pushouts retain the original common object,
zero maps and complete original descent equations. No K₀ data is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

/-- The two original rows use the SAME original cofiber, with the original
pushout descent and both exact original leg equations. -/
theorem exists_common_cofiber_of_isPushout
    {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hP : IsPushout i f inY inZ) (hi : IsCofibration i) :
    ∃ (Q : C) (sX : X ⟶ (0 : C)) (sZ : Z ⟶ (0 : C)) (z : (0 : C) ⟶ Q)
      (qY : Y ⟶ Q) (qP : P ⟶ Q),
      IsPushout sX i z qY ∧ IsPushout sZ inZ z qP ∧
      inY ≫ qP = qY ∧ inZ ≫ qP = sZ ≫ z ∧
      IsCofibrationSequence i qY ∧ IsCofibrationSequence inZ qP := by
  obtain ⟨Q, qY, hSeq⟩ := exists_cofiberSequence_of_cofibration i hi
  obtain ⟨_, sX, z, hQ⟩ := hSeq
  let sZ : Z ⟶ (0 : C) := HasZeroObject.zeroIsTerminal.from Z
  have hZero : f ≫ sZ = sX := (isZero_zero C).eq_of_tgt _ _
  have hComm : i ≫ qY = f ≫ (sZ ≫ z) := by
    rw [← Category.assoc, hZero]
    exact hQ.w.symm
  let qP := hP.desc qY (sZ ≫ z) hComm
  have hY : inY ≫ qP = qY := hP.inl_desc qY (sZ ≫ z) hComm
  have hZ : inZ ≫ qP = sZ ≫ z := hP.inr_desc qY (sZ ≫ z) hComm
  have hOuter : IsPushout i (f ≫ sZ) (inY ≫ qP) z := by
    rw [hZero, hY]
    exact hQ.flip
  have hLower : IsPushout inZ sZ qP z := hOuter.of_top hZ hP
  have hInZ : IsCofibration inZ :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP.flip hi
  exact ⟨Q, sX, sZ, z, qY, qP, hQ, hLower.flip, hY, hZ,
    ⟨hi, sX, z, hQ⟩, ⟨hInZ, sZ, z, hLower.flip⟩⟩

end CategoryTheory

end
