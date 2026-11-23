/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroUniformRealization

/-!
# Uniformity of the SAME actual projected original total-source family

The proved original base functor values and BOTH original component-edge
values identify the actual projected total-source transformation with the
SAME normalized uniform-base comparison. Equality transport of the original
realized family preserves every point/time value. Both projected directions
are uniform over the entire original completed-Core realization.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uA vA uB vB uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

private theorem actualNaturalTransHEqFromComponents
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (alpha : F ⟶ G) (beta : F' ⟶ G')
    (hApp : ∀ a, HEq (alpha.app a) (beta.app a)) : HEq alpha beta := by
  cases hF
  cases hG
  apply heq_of_eq
  apply NatTrans.ext
  funext a
  exact eq_of_heq (hApp a)

private theorem actualOriginalRealizedFamilyValue
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    {alpha : F ⟶ G} {beta : F' ⟶ G'} (h : HEq alpha beta)
    (t : unitInterval) (x : SSet.toTop.obj (nerve A)) :
    realizedNerveFunctorMapHomotopy alpha (t, x) =
      realizedNerveFunctorMapHomotopy beta (t, x) := by
  cases hF
  cases hG
  cases h
  rfl

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualOriginalProjectedHomHEq :
    HEq (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D)))
      (completedZeroUniformBaseIso F).hom := by
  let P := ExtensionCategory.localizedTarget (C := D)
  have hF : (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
      ExtensionCategory.stabilizedFunctorMap F) ⋙ P =
      (Functor.const (SInverse (Core C) (Core C))).obj
        ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)) :=
    completedZeroMappedTotalBase_eq_const F
  have hG : (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)) ⋙ P =
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : D)⟩ : QuillenQ D) :=
    completedZeroTargetTotalBase_eq_const F
  apply actualNaturalTransHEqFromComponents hF hG
  intro a
  have hActualApp : (completedZeroTotalNaturalityIso F).hom.app a =
      (completedZeroTotalSourceComponent F a).hom :=
    congrArg Iso.hom (completedZeroTotalNaturalityIso_app F a)
  have hProjectedApp : (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom P).app a =
      P.map (completedZeroTotalSourceComponent F a).hom := congrArg P.map hActualApp
  exact (heq_of_eq hProjectedApp).trans
    ((completedZeroTotalSourceComponent_target_hom_heq F a).trans
      (heq_of_eq (completedZeroUniformBaseIso_hom_app F a).symm))

private theorem actualOriginalProjectedInvHEq :
    HEq (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D)))
      (completedZeroUniformBaseIso F).inv := by
  let P := ExtensionCategory.localizedTarget (C := D)
  have hF : (completedCoreFunctor F ⋙ zeroLocalizedFunctor (C := D) ⋙ localizedForget (0 : D)) ⋙ P =
      (Functor.const (SInverse (Core C) (Core C))).obj (⟨(0 : D)⟩ : QuillenQ D) :=
    completedZeroTargetTotalBase_eq_const F
  have hG : (zeroLocalizedFunctor (C := C) ⋙ localizedForget (0 : C) ⋙
      ExtensionCategory.stabilizedFunctorMap F) ⋙ P =
      (Functor.const (SInverse (Core C) (Core C))).obj
        ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C)) :=
    completedZeroMappedTotalBase_eq_const F
  apply actualNaturalTransHEqFromComponents hF hG
  intro a
  have hActualApp : (completedZeroTotalNaturalityIso F).inv.app a =
      (completedZeroTotalSourceComponent F a).inv :=
    congrArg Iso.inv (completedZeroTotalNaturalityIso_app F a)
  have hProjectedApp : (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv P).app a =
      P.map (completedZeroTotalSourceComponent F a).inv := congrArg P.map hActualApp
  exact (heq_of_eq hProjectedApp).trans
    ((completedZeroTotalSourceComponent_target_inv_heq F a).trans
      (heq_of_eq (completedZeroUniformBaseIso_inv_app F a).symm))

private theorem actualOriginalProjectedForwardValue (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).hom (t, x) :=
  actualOriginalRealizedFamilyValue (completedZeroMappedTotalBase_eq_const F)
    (completedZeroTargetTotalBase_eq_const F) (actualOriginalProjectedHomHEq F) t x

private theorem actualOriginalProjectedInverseValue (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).inv (t, x) :=
  actualOriginalRealizedFamilyValue (completedZeroTargetTotalBase_eq_const F)
    (completedZeroMappedTotalBase_eq_const F) (actualOriginalProjectedInvHEq F) t x

/-- Every forward projected original total-family value is the SAME uniform-base family value. -/
public theorem completedZeroProjectedOriginalFamily_forward_value (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).hom (t, x) :=
  actualOriginalProjectedForwardValue F t x

/-- Every inverse value retains the SAME original inverse uniform-base family. -/
public theorem completedZeroProjectedOriginalFamily_inverse_value (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroUniformBaseIso F).inv (t, x) :=
  actualOriginalProjectedInverseValue F t x

/-- The actual projected original forward family is uniform over EVERY original completed-Core
  point. -/
public theorem completedZeroProjectedOriginalFamily_forward_uniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, x) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, y) :=
  (completedZeroProjectedOriginalFamily_forward_value F t x).trans
    ((completedZeroUniformBaseHomotopy_forward_uniform F t x y).trans
      (completedZeroProjectedOriginalFamily_forward_value F t y).symm)

/-- The SAME actual inverse family is uniform over the whole original source realization. -/
public theorem completedZeroProjectedOriginalFamily_inverse_uniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, x) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, y) :=
  (completedZeroProjectedOriginalFamily_inverse_value F t x).trans
    ((completedZeroUniformBaseHomotopy_inverse_uniform F t x y).trans
      (completedZeroProjectedOriginalFamily_inverse_value F t y).symm)

end AlgebraicKTheory.FixedTargetExtension

end
