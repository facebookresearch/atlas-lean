/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroProjectedTotalUniform

/-!
# Actual mixed base projection of the original total-space comparison family

The original total-comparison homotopy projects through the SAME actual
realized target functor to the realized original projected transformation.
The original source/target category charts and default working envelope
are retained. Both family directions are uniform after actual projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] CategoryTheory.uliftCategory

universe uNative uA vA uB vB uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

private theorem actualNativeRealizedHomotopyPostcompose
    {A B E : Type uNative} [Category.{uNative} A] [Category.{uNative} B]
    [Category.{uNative} E] {F G : A ⥤ B} (alpha : F ⟶ G) (P : B ⥤ E)
    (t : unitInterval) (x : SSet.toTop.obj (nerve A)) :
    SSet.toTop.map (nerveMap P)
        (SSet.realizeHomotopy (nerve A) (nerve B) (nerveMap F) (nerveMap G)
          (NatTrans.nerveHomotopy alpha) (t, x)) =
      SSet.realizeHomotopy (nerve A) (nerve E) (nerveMap (F ⋙ P)) (nerveMap (G ⋙ P))
        (NatTrans.nerveHomotopy (Functor.whiskerRight alpha P)) (t, x) := by
  let H := NatTrans.nerveHomotopy alpha
  let H' := NatTrans.nerveHomotopy (Functor.whiskerRight alpha P)
  have hData : H.h ≫ nerveMap P = H'.h :=
    (congrArg (fun q => q ≫ nerveMap P) (NatTrans.nerveHomotopy_h_value alpha)).trans
      ((NatTrans.nerveHomotopyMap_postcomp alpha P).trans
        (NatTrans.nerveHomotopy_h_value (Functor.whiskerRight alpha P)).symm)
  have hMap : SSet.realizeHomotopyMap (nerve A) (nerve B) (nerveMap F) (nerveMap G) H ≫
      SSet.toTop.map (nerveMap P) =
        SSet.realizeHomotopyMap (nerve A) (nerve E)
          (nerveMap (F ⋙ P)) (nerveMap (G ⋙ P)) H' := by
    dsimp only [SSet.realizeHomotopyMap]
    simp only [Category.assoc, ← Functor.map_comp, hData]
  let z := (TopCat.prodIsoProd TopCat.I (SSet.toTop.obj (nerve A))).inv
    (TopCat.I.homeomorph.symm t, x)
  change SSet.toTop.map (nerveMap P)
      (SSet.realizeHomotopyMap (nerve A) (nerve B) (nerveMap F) (nerveMap G) H z) =
    SSet.realizeHomotopyMap (nerve A) (nerve E)
      (nerveMap (F ⋙ P)) (nerveMap (G ⋙ P)) H' z
  exact (TopCat.comp_app _ _ z).symm.trans (ConcreteCategory.congr_hom hMap z)

private theorem actualDownFrameOriginalHomotopyProjection
    {A : Type uA} [Category.{vA} A]
    {B : Type (max uB vB)} [Category.{max uB vB} B]
    {E : Type uB} [Category.{max uB vB} E]
    {F G : A ⥤ B} (alpha : F ⟶ G) (P : B ⥤ E)
    (t : unitInterval) (x : SSet.toTop.obj (nerve A)) :
    realizedNerveFunctorMap P (realizedNerveFunctorMapHomotopy alpha (t, x)) =
      realizedNerveFunctorMapHomotopy (Functor.whiskerRight alpha P) (t, x) := by
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB} A
  let HB := SSet.realizedNerveLiftHomeomorph.{max uB vB, max uB vB, max uA vA uB vB} B
  let HE := SSet.realizedNerveLiftHomeomorph.{uB, max uB vB, max uA vA uB vB} E
  let UA := ULiftHomULiftCategory.equiv.{max uA vA uB vB, max uA vA uB vB, vA, uA} A
  let UB := ULiftHomULiftCategory.equiv.{max uA vA uB vB, max uA vA uB vB,
    max uB vB, max uB vB} B
  let UE := ULiftHomULiftCategory.equiv.{max uA vA uB vB, max uA vA uB vB,
    max uB vB, uB} E
  let LF := UA.inverse ⋙ F ⋙ UB.functor
  let LG := UA.inverse ⋙ G ⋙ UB.functor
  let LP := UB.inverse ⋙ P ⋙ UE.functor
  let alphaL : LF ⟶ LG := Functor.whiskerLeft UA.inverse (Functor.whiskerRight alpha UB.functor)
  let alphaP := Functor.whiskerLeft UA.inverse
    (Functor.whiskerRight (Functor.whiskerRight alpha P) UE.functor)
  have hAlpha : Functor.whiskerRight alphaL LP = alphaP := by
    apply NatTrans.ext
    funext a
    rfl
  rw [realizedNerveFunctorMap_larger_recipe.{max uB vB, max uB vB,
      uB, max uB vB, max uA vA uB vB} P]
  rw [realizedNerveFunctorMapHomotopy_value alpha t x,
    realizedNerveFunctorMapHomotopy_value (Functor.whiskerRight alpha P) t x]
  let z := HA.symm x
  change HE (SSet.toTop.map (nerveMap LP)
      (HB.symm (HB (SSet.realizeHomotopy _ _ (nerveMap LF) (nerveMap LG)
        (NatTrans.nerveHomotopy alphaL) (t, z))))) =
    HE (SSet.realizeHomotopy _ _ _ _ (NatTrans.nerveHomotopy alphaP) (t, z))
  rw [HB.symm_apply_apply]
  have hNative := actualNativeRealizedHomotopyPostcompose alphaL LP t z
  rw [hAlpha] at hNative
  exact congrArg HE hNative

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualOriginalTotalForwardProjection (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).hom (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  actualDownFrameOriginalHomotopyProjection (completedZeroTotalNaturalityIso F).hom
    (ExtensionCategory.localizedTarget (C := D)) t x

/-- Every actual original total-family point projects to its SAME original projected transformation
  family. -/
public theorem completedZeroTotalRealization_forward_target_value (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).hom (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).hom
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  actualOriginalTotalForwardProjection F t x

private theorem actualOriginalTotalInverseProjection (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).inv (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  actualDownFrameOriginalHomotopyProjection (completedZeroTotalNaturalityIso F).inv
    (ExtensionCategory.localizedTarget (C := D)) t x

/-- The SAME inverse total-family values retain the original inverse projected family at every
  point. -/
public theorem completedZeroTotalRealization_inverse_target_value (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).inv (t, x)) =
    realizedNerveFunctorMapHomotopy
      (Functor.whiskerRight (completedZeroTotalNaturalityIso F).inv
        (ExtensionCategory.localizedTarget (C := D))) (t, x) :=
  actualOriginalTotalInverseProjection F t x

/-- The actual base projection of the original forward total family is uniform on EVERY old source
  point. -/
public theorem completedZeroTotalRealization_forward_target_uniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).hom (t, x)) =
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).hom (t, y)) :=
  (completedZeroTotalRealization_forward_target_value F t x).trans
    ((completedZeroProjectedOriginalFamily_forward_uniform F t x y).trans
      (completedZeroTotalRealization_forward_target_value F t y).symm)

/-- The SAME inverse total-space family has uniform actual base projection over the entire source.
-/
public theorem completedZeroTotalRealization_inverse_target_uniform (t : unitInterval)
    (x y : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).inv (t, x)) =
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := D))
      (realizedNerveFunctorMapHomotopy (completedZeroTotalNaturalityIso F).inv (t, y)) :=
  (completedZeroTotalRealization_inverse_target_value F t x).trans
    ((completedZeroProjectedOriginalFamily_inverse_uniform F t x y).trans
      (completedZeroTotalRealization_inverse_target_value F t y).symm)

end AlgebraicKTheory.FixedTargetExtension

end
