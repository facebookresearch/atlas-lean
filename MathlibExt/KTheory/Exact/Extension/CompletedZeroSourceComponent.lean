/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroRowIdentityCoordinateNatIso
public import MathlibExt.KTheory.Exact.Extension.StabilizedFunctorTarget
public import MathlibExt.CategoryTheory.Monoidal.CoreAdditiveFunctorMap

/-!
# The original completed-zero source component at the same denominator

The actual completed-Core map and stabilized extension map retain the
literal images of both original coordinates. The identity-coordinate
zero-row isomorphism is included in the original localization at that
same image denominator. The two endpoint transports below are proved
object computations; no source agreement or component isomorphism is
supplied as an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalZeroGivenObject (A : Core C) :
    (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C)).obj A =
      (zeroRow A).toExtension :=
  (givenRowFunctor_obj ((zeroRowFunctor (C := C)).obj A)).trans
    (congrArg (fun E : FixedTargetExtension C (0 : C) => E.toExtension)
      (show (zeroRowFunctor (C := C)).obj A = zeroRow A from rfl))

private theorem originalCompletedZeroSourceObject (a : SInverse (Core C) (Core C)) :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F).obj a =
      (MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)).obj
        ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
          ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2) := by
  let t := (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C)).obj a
  have ht : t.of = ((zeroRow a.of.1).toExtension, a.of.2) := rfl
  have hImage : ((ExtensionCategory.stabilizedFunctorMap F).obj t).of =
      ((ExtensionCategory.mapFunctor F).obj t.of.1, F.core.obj t.of.2) :=
    (congrArg (fun x : SInverse (Core D) (ExtensionCategory D) => x.of)
      (ExtensionCategory.stabilizedFunctorMap_obj F t)).trans
      (ExtensionCategory.stabilizedFunctorObject_of F t)
  have hNumerator : t.of.1 =
      (zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C)).obj a.of.1 :=
    (congrArg Prod.fst ht).trans (originalZeroGivenObject a.of.1).symm
  have hDenominator : t.of.2 = a.of.2 := congrArg Prod.snd ht
  exact congrArg (fun p : ExtensionCategory D × Core D =>
      (⟨p⟩ : SInverse (Core D) (ExtensionCategory D)))
    (hImage.trans (congrArg₂
      (fun (E : ExtensionCategory C) (d : Core C) =>
        ((ExtensionCategory.mapFunctor F).obj E, F.core.obj d))
      hNumerator hDenominator))

omit [ExactCategory C] [F.IsExact] in
private theorem originalCompletedZeroTargetObject (a : SInverse (Core C) (Core C)) :
    (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F ⋙
        zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)).obj a =
      (MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)).obj
        ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1,
          F.core.obj a.of.2) := by
  let k := (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F).obj a
  have hk := CategoryTheory.CoreLocalizationComparison.completedCoreFunctor_obj F a
  have hNumerator : k.of.1 = F.core.obj a.of.1 :=
    (congrArg (fun x : SInverse (Core D) (Core D) => x.of.1) hk).trans (by rfl)
  have hDenominator : k.of.2 = F.core.obj a.of.2 :=
    (congrArg (fun x : SInverse (Core D) (Core D) => x.of.2) hk).trans (by rfl)
  have hImage :
      ((zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)).obj k).of =
        ((zeroRow k.of.1).toExtension, k.of.2) := rfl
  have hGiven := originalZeroGivenObject (C := D) (F.core.obj a.of.1)
  exact congrArg (fun p : ExtensionCategory D × Core D =>
      (⟨p⟩ : SInverse (Core D) (ExtensionCategory D)))
    (hImage.trans ((congrArg₂
      (fun (A d : Core D) => ((zeroRow A).toExtension, d))
      hNumerator hDenominator).trans
        (congrArg (fun E : ExtensionCategory D => (E, F.core.obj a.of.2)) hGiven.symm)))

/-- The ordinary zero-row component keeps the actual image denominator, with identity on it. -/
public def completedZeroOrdinarySourceComponent (a : SInverse (Core C) (Core C)) :
    ((zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
        ExtensionCategory.mapFunctor F).obj a.of.1, F.core.obj a.of.2) ≅
      ((F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D)).obj a.of.1,
        F.core.obj a.of.2) :=
  (zeroRowIdentityCoordinateIso F a.of.1).prod (Iso.refl (F.core.obj a.of.2))

private theorem originalCompletedZeroOrdinaryHomDenominator
    (a : SInverse (Core C) (Core C)) :
    (completedZeroOrdinarySourceComponent F a).hom.2 = 𝟙 (F.core.obj a.of.2) := rfl

/-- Its forward denominator is the identity of the same original denominator image. -/
public theorem completedZeroOrdinarySourceComponent_hom_denominator
    (a : SInverse (Core C) (Core C)) :
    (completedZeroOrdinarySourceComponent F a).hom.2 = 𝟙 (F.core.obj a.of.2) :=
  originalCompletedZeroOrdinaryHomDenominator F a

private theorem originalCompletedZeroOrdinaryInvDenominator
    (a : SInverse (Core C) (Core C)) :
    (completedZeroOrdinarySourceComponent F a).inv.2 = 𝟙 (F.core.obj a.of.2) := rfl

/-- Its inverse keeps that same denominator and its actual identity. -/
public theorem completedZeroOrdinarySourceComponent_inv_denominator
    (a : SInverse (Core C) (Core C)) :
    (completedZeroOrdinarySourceComponent F a).inv.2 = 𝟙 (F.core.obj a.of.2) :=
  originalCompletedZeroOrdinaryInvDenominator F a

/-- The actual total-object source component on every original completed-Core pair. -/
public def completedZeroTotalSourceComponent (a : SInverse (Core C) (Core C)) :
    (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
        ExtensionCategory.stabilizedFunctorMap F).obj a ≅
      (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F ⋙
        zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)).obj a :=
  eqToIso (originalCompletedZeroSourceObject F a) ≪≫
    (MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)).mapIso
      (completedZeroOrdinarySourceComponent F a) ≪≫
    (eqToIso (originalCompletedZeroTargetObject F a)).symm

/-- The forward component is the actual ordinary pair inclusion, with only proved endpoint casts. -/
public theorem completedZeroTotalSourceComponent_hom_heq
    (a : SInverse (Core C) (Core C)) :
    HEq (completedZeroTotalSourceComponent F a).hom
      ((MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)).map
        (completedZeroOrdinarySourceComponent F a).hom) := by
  let I := MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)
  let e := completedZeroOrdinarySourceComponent F a
  let hs := originalCompletedZeroSourceObject F a
  let ht := originalCompletedZeroTargetObject F a
  change HEq (eqToHom hs ≫ I.map e.hom ≫ eqToHom ht.symm) (I.map e.hom)
  exact (eqToHom_comp_heq (I.map e.hom ≫ eqToHom ht.symm) hs).trans
    (comp_eqToHom_heq (I.map e.hom) ht.symm)

private theorem originalCompletedZeroTotalInverseComputed
    (a : SInverse (Core C) (Core C)) :
    HEq (completedZeroTotalSourceComponent F a).inv
      ((MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)).map
        (completedZeroOrdinarySourceComponent F a).inv) := by
  let I := MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)
  let e := completedZeroOrdinarySourceComponent F a
  let hs := originalCompletedZeroSourceObject F a
  let ht := originalCompletedZeroTargetObject F a
  dsimp only [completedZeroTotalSourceComponent]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  change HEq (eqToHom ht ≫ I.map e.inv ≫ eqToHom hs.symm) (I.map e.inv)
  exact (eqToHom_comp_heq (I.map e.inv ≫ eqToHom hs.symm) ht).trans
    (comp_eqToHom_heq (I.map e.inv) hs.symm)

/-- The inverse is the inverse ordinary inclusion at the same denominator. -/
public theorem completedZeroTotalSourceComponent_inv_heq
    (a : SInverse (Core C) (Core C)) :
    HEq (completedZeroTotalSourceComponent F a).inv
      ((MonoidalActionCategory.inclusion (Core D) (ExtensionCategory D × Core D)).map
        (completedZeroOrdinarySourceComponent F a).inv) :=
  originalCompletedZeroTotalInverseComputed F a

end AlgebraicKTheory.FixedTargetExtension

end


/-!
# Whole original ordinary completed-zero component value

This proper owned value exposes the existing component recipe as a theorem.
The original forward and inverse numerator and identity denominator are
unchanged. Imported consumers can use the same full Iso without unfolding
the public definition or selecting another comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction

universe uCZeroValue vCZeroValue uDZeroValue vDZeroValue

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uCZeroValue} [Category.{vCZeroValue} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uDZeroValue} [Category.{vDZeroValue} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalCompletedZeroOrdinaryWholeValue
    (a : SInverse (Core C) (Core C)) :
    completedZeroOrdinarySourceComponent F a =
      (zeroRowIdentityCoordinateIso F a.of.1).prod (Iso.refl (F.core.obj a.of.2)) := rfl

/-- The SAME whole original ordinary component retains both Iso directions and its identity
  denominator. -/
public theorem completedZeroOrdinarySourceComponent_value
    (a : SInverse (Core C) (Core C)) :
    completedZeroOrdinarySourceComponent F a =
      (zeroRowIdentityCoordinateIso F a.of.1).prod (Iso.refl (F.core.obj a.of.2)) :=
  originalCompletedZeroOrdinaryWholeValue F a

end AlgebraicKTheory.FixedTargetExtension

end
