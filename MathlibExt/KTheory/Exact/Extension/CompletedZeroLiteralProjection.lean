/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroTotalProjectionRealization

/-!
# The literal original full-fiber base projection of the total-source family

The SAME mixed realized target map is the original common-Hom map used by
the original full homotopy fiber. Both actual total-source family directions
therefore project to their exact original projected families at every point.
This identifies the literal base projection; the carried path remains explicit.
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

private theorem actualOriginalTargetWholeValue
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D)) =
      (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
        (ExtensionCategory.localizedTarget (C := D)))).hom :=
  realizedNerveFunctorMap_commonDownFrame.{uD, max uD vD}
    (ExtensionCategory.localizedTarget (C := D))

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualOriginalLiteralForwardValue (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
      (ExtensionCategory.localizedTarget (C := D))))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).hom (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  ((congrArg (fun p => p (realizedNerveFunctorMapHomotopy
      (completedZeroTotalNaturalityIso F).hom (t, x)))
    (actualOriginalTargetWholeValue (D := D))).symm).trans
      (completedZeroTotalRealization_forward_target_value F t x)

/-- EVERY original forward total-family point uses the SAME literal full-fiber common-Hom
  projection. -/
public theorem completedZeroTotalFamily_forward_literal_target (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
      (ExtensionCategory.localizedTarget (C := D))))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).hom (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  actualOriginalLiteralForwardValue F t x

private theorem actualOriginalLiteralInverseValue (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
      (ExtensionCategory.localizedTarget (C := D))))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).inv (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  ((congrArg (fun p => p (realizedNerveFunctorMapHomotopy
      (completedZeroTotalNaturalityIso F).inv (t, x)))
    (actualOriginalTargetWholeValue (D := D))).symm).trans
      (completedZeroTotalRealization_inverse_target_value F t x)

/-- The SAME inverse family retains the original literal target projection and all point/time
  values. -/
public theorem completedZeroTotalFamily_inverse_literal_target (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
      (ExtensionCategory.localizedTarget (C := D))))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).inv (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  actualOriginalLiteralInverseValue F t x

end AlgebraicKTheory.FixedTargetExtension

end
