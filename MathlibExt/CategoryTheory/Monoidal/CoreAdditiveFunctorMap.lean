/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.CoreRealizedTranslations
public import MathlibExt.CategoryTheory.Monoidal.SInverseSFunctor
public import Mathlib.CategoryTheory.Whiskering

/-!
# Actual additive maps on the original completed Core

The original positive-first Core/Pair equivalences and the existing
additive Pair functor define the map on SInverse(Core C, Core C).
Their original unit/counit data give the comparison square. Both positive
and denominator objects retain their literal F images. No equivalence,
localization map, comparison square or component restriction is an input.
-/

noncomputable section

open CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal CategoryTheory.MonoidalCategory

attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace CategoryTheory.CoreLocalizationComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

variable (F : C ⥤ D) [F.Additive]

/-- The original additive Pair image, returned to the original completed Core carrier. -/
public def completedCoreFunctor : SInverse (Core C) (Core C) ⥤ SInverse (Core D) (Core D) :=
  (coreAdditivePairEquivalence (C := C)).functor ⋙ SInverseS.pairFunctor F ⋙
    (coreAdditivePairEquivalence (C := D)).inverse

private theorem completedCoreFunctorObjectComputed (a : SInverse (Core C) (Core C)) :
    (completedCoreFunctor F).obj a =
      fromPairObj (C := D) (⟨F.obj a.of.1.of, F.obj a.of.2.of⟩ : SInverseS.Pair D) := by
  let E := coreAdditivePairEquivalence (C := D)
  have hC := coreAdditivePairEquivalence_functor_obj (C := C) a
  have hF : (SInverseS.pairFunctor F).obj (toPairObj (C := C) a) =
      (⟨F.obj a.of.1.of, F.obj a.of.2.of⟩ : SInverseS.Pair D) :=
    (SInverseS.pairFunctor_characteristic F F (Iso.refl F) (𝟭 D)).1 (toPairObj a)
  exact (congrArg E.inverse.obj
    ((congrArg (SInverseS.pairFunctor F).obj hC).trans hF)).trans
      (coreAdditivePairEquivalence_inverse_obj (C := D) _)

/-- Both original coordinates are the literal image objects, without a coordinate swap. -/
public theorem completedCoreFunctor_obj (a : SInverse (Core C) (Core C)) :
    (completedCoreFunctor F).obj a =
      fromPairObj (C := D) (⟨F.obj a.of.1.of, F.obj a.of.2.of⟩ : SInverseS.Pair D) :=
  completedCoreFunctorObjectComputed F a

/-- The original Pair equivalence counit supplies the whole additive transport square. -/
public def completedCoreFunctorPairIso :
    completedCoreFunctor F ⋙ (coreAdditivePairEquivalence (C := D)).functor ≅
      (coreAdditivePairEquivalence (C := C)).functor ⋙ SInverseS.pairFunctor F := by
  let A := (coreAdditivePairEquivalence (C := C)).functor
  let B := SInverseS.pairFunctor F
  let U := (coreAdditivePairEquivalence (C := D)).inverse
  let V := (coreAdditivePairEquivalence (C := D)).functor
  let h : U ⋙ V ≅ 𝟭 (SInverseS.Pair D) :=
    (coreAdditivePairEquivalence (C := D)).counitIso
  change (A ⋙ B ⋙ U) ⋙ V ≅ A ⋙ B
  exact Functor.associator A (B ⋙ U) V ≪≫
    Functor.isoWhiskerLeft A (Functor.associator B U V) ≪≫
      Functor.isoWhiskerLeft A
        (Functor.isoWhiskerLeft B h ≪≫ Functor.rightUnitor B)


private theorem originalCompletedCoreRepresentativeComputed
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq ((completedCoreFunctor F).map (Hom.mk r))
      (Hom.mk (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r)))) := heq_of_eq rfl

/-- The actual completed-Core functor retains the original Pair-mapped raw representative. -/
public theorem completedCoreFunctor_mkHom_heq
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq ((completedCoreFunctor F).map (Hom.mk r))
      (Hom.mk (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r)))) :=
  originalCompletedCoreRepresentativeComputed F r

end CategoryTheory.CoreLocalizationComparison

end


/-!
# Proper whole value of the original completed-Core functor

The original positive-first Core/Pair equivalences and actual additive Pair
functor remain unchanged. The characteristic makes that exact full functor
recipe usable without unfolding an imported opaque definition.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD

namespace CategoryTheory.CoreLocalizationComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

private theorem originalCompletedCoreFunctorWholeValueComputed :
    completedCoreFunctor F =
      (coreAdditivePairEquivalence (C := C)).functor ⋙ SInverseS.pairFunctor F ⋙
        (coreAdditivePairEquivalence (C := D)).inverse := rfl

/-- The WHOLE original completed-Core functor has the SAME original
positive-first Core/Pair/additive-functor/inverse recipe, in independent worlds. -/
public theorem completedCoreFunctor_value :
    completedCoreFunctor F =
      (coreAdditivePairEquivalence (C := C)).functor ⋙ SInverseS.pairFunctor F ⋙
        (coreAdditivePairEquivalence (C := D)).inverse :=
  originalCompletedCoreFunctorWholeValueComputed F

end CategoryTheory.CoreLocalizationComparison

end
