/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroBaseNaturality
public import Mathlib.CategoryTheory.Whiskering

/-!
# The actual total-source NatIso has the uniform original mapped-zero base

Whisker the SAME original total NatIso to Quillen Q, then transport its
actual source/target base functors by their proved whole constant values.
The whole resulting constant-functor Iso is the canonical original
mapped-zero Iso. Both directions and every completed pair are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private def actualUniformBaseIsoComputed :
    (Functor.const (SInverse (Core C) (Core C))).obj
        ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)) ≅
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : D)⟩ : QuillenQ D) := by
  let ZC := zeroLocalizedFunctor (C := C)
  let YC := localizedForget (0 : C)
  let H := ExtensionCategory.stabilizedFunctorMap F
  let K := completedCoreFunctor F
  let ZD := zeroLocalizedFunctor (C := D)
  let YD := localizedForget (0 : D)
  let P := ExtensionCategory.localizedTarget (C := D)
  let CL := (Functor.const (SInverse (Core C) (Core C))).obj
    ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C))
  let CR := (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : D)⟩ : QuillenQ D)
  let eL : (ZC ⋙ YC ⋙ H) ⋙ P ≅ CL :=
    Functor.associator ZC (YC ⋙ H) P ≪≫
      Functor.isoWhiskerLeft ZC (Functor.associator YC H P) ≪≫
      eqToIso (completedZeroMappedTotalBase_eq_const F)
  let eR : (K ⋙ ZD ⋙ YD) ⋙ P ≅ CR :=
    Functor.associator K (ZD ⋙ YD) P ≪≫
      Functor.isoWhiskerLeft K (Functor.associator ZD YD P) ≪≫
      eqToIso (completedZeroTargetTotalBase_eq_const F)
  exact eL.symm ≪≫ Functor.isoWhiskerRight (completedZeroTotalNaturalityIso F) P ≪≫ eR

/-- The SAME original total NatIso, projected and transported by its actual whole base functor
  values. -/
public def completedZeroUniformBaseIso :
    (Functor.const (SInverse (Core C) (Core C))).obj
        ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)) ≅
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : D)⟩ : QuillenQ D) :=
  actualUniformBaseIsoComputed F

private theorem actualUniformBaseIsoWholeValue :
    completedZeroUniformBaseIso F =
      (Functor.const (SInverse (Core C) (Core C))).mapIso (QuillenQ.zeroComparisonIso F) := by
  apply Iso.ext
  apply NatTrans.ext
  funext a
  exact QuillenQ.hom_eq_of_target_isZero _ _ (isZero_zero D)

/-- The WHOLE projected original comparison is the SAME original canonical mapped-zero constant Iso.
-/
public theorem completedZeroUniformBaseIso_value :
    completedZeroUniformBaseIso F =
      (Functor.const (SInverse (Core C) (Core C))).mapIso (QuillenQ.zeroComparisonIso F) :=
  actualUniformBaseIsoWholeValue F

private theorem actualUniformBaseHomValue (a : SInverse (Core C) (Core C)) :
    (completedZeroUniformBaseIso F).hom.app a = (QuillenQ.zeroComparisonIso F).hom :=
  congrArg (fun e => e.hom.app a) (completedZeroUniformBaseIso_value F)

/-- Every forward base component is the SAME original mapped-zero hom, with no component
  restriction. -/
public theorem completedZeroUniformBaseIso_hom_app (a : SInverse (Core C) (Core C)) :
    (completedZeroUniformBaseIso F).hom.app a = (QuillenQ.zeroComparisonIso F).hom :=
  actualUniformBaseHomValue F a

private theorem actualUniformBaseInvValue (a : SInverse (Core C) (Core C)) :
    (completedZeroUniformBaseIso F).inv.app a = (QuillenQ.zeroComparisonIso F).inv :=
  congrArg (fun e => e.inv.app a) (completedZeroUniformBaseIso_value F)

/-- Every inverse base component retains the SAME original mapped-zero inverse hom. -/
public theorem completedZeroUniformBaseIso_inv_app (a : SInverse (Core C) (Core C)) :
    (completedZeroUniformBaseIso F).inv.app a = (QuillenQ.zeroComparisonIso F).inv :=
  actualUniformBaseInvValue F a

end AlgebraicKTheory.FixedTargetExtension

end
