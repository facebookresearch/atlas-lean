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

public import MathlibExt.CategoryTheory.Waldhausen.CofiberCokernel
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberPushoutCokernel
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

/-!
# General cofiber row of an actual levelwise pushout

The original cofiber rows supply the cokernel universal properties and the
common quotient epimorphism used by the existing levelwise pushout proof.
If the first assembled arrow is a cofibration, that proof gives the entire
apex cofiber row. The relative-arrow pushout constructor supplies the first
cofibration in the general extension pushout application.

Zero morphisms are derived inside the proof; the public theorem keeps the
original general Waldhausen hypotheses.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original three cofiber rows and the actual first-arrow
cofibration give the full cofiber property of the assembled pushout row. -/
theorem LevelwisePushoutData.isCofiberSequence
    (D : LevelwisePushoutData C)
    (hR : cofiberSequenceProperty C D.R)
    (hS : cofiberSequenceProperty C D.S)
    (hT : cofiberSequenceProperty C D.T)
    (hFirst : IsCofibration D.inducedMap01) :
    cofiberSequenceProperty C D.assembled := by
  let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
  change IsCofiberSequence (D.R.map' 0 1) (D.R.map' 1 2) at hR
  change IsCofiberSequence (D.S.map' 0 1) (D.S.map' 1 2) at hS
  change IsCofiberSequence (D.T.map' 0 1) (D.T.map' 1 2) at hT
  let : Epi (D.R.map' 1 2) := hR.epi
  have wS := hS.comp_eq_zero
  have wT := hT.comp_eq_zero
  let hCokernel := levelwisePushoutShortComplex_isColimit_cokernel C D wS wT
    (isColimitCokernelCoforkOfCofiberSequence hS)
    (isColimitCokernelCoforkOfCofiberSequence hT)
  have hFirst' : IsCofibration (levelwisePushoutShortComplex C D wS wT).f := by
    change IsCofibration D.inducedMap01
    exact hFirst
  have hSeq := isCofiberSequenceOfCofibrationAndCokernel hFirst'
    (levelwisePushoutShortComplex C D wS wT).zero hCokernel
  change IsCofiberSequence D.inducedMap01 D.inducedMap12
  simpa only [levelwisePushoutShortComplex_X₁, levelwisePushoutShortComplex_X₂,
    levelwisePushoutShortComplex_X₃, levelwisePushoutShortComplex_f,
    levelwisePushoutShortComplex_g] using hSeq

end CategoryTheory.Waldhausen.SConstruction
