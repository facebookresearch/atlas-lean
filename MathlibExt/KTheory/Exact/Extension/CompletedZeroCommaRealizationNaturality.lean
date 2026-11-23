/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroCommaNaturality
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberComparison
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMapComposition

/-!
# Actual mixed realization square of the original zero-comma map

The original full common-up comma map is identified by its proper whole
recipe. Actual independent-world realization composition attaches both
sides of the original comma NatIso to those literal original maps. Both
component directions are realized, and every family value is retained.
This is the comma realization square; the full fiber/conull return and
original loop-unit compatibility are subsequent obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uD vD uX uY

namespace AlgebraicKTheory.OriginalQZeroComparison

private def actualHomotopyEndpointTransport
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f g f' g' : C(X, Y)} (hf : f = f') (hg : g = g')
    (H : ContinuousMap.Homotopy f g) : ContinuousMap.Homotopy f' g' := by
  cases hf
  cases hg
  exact H

private theorem actualHomotopyEndpointTransportValue
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {f g f' g' : C(X, Y)} (hf : f = f') (hg : g = g')
    (H : ContinuousMap.Homotopy f g) (t : unitInterval) (x : X) :
    actualHomotopyEndpointTransport hf hg H (t, x) = H (t, x) := by
  cases hf
  cases hg
  rfl

private theorem actualCompletedZeroCommaRealizationValue
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))).hom =
      realizedNerveFunctorMap (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) := by
  let Z := FixedTargetExtension.zeroLocalizedFunctor (C := C)
  let Y := FixedTargetExtension.localizedFiberFunctor (0 : C)
  let U := Functor.fiberToStructuredArrow
    (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)
  have hNerve : completedCoreToZeroLeftCommaNerveMap (C := C) =
      nerveMapCommonHomUp.{uC, max uC vC, 0} (Z ⋙ Y ⋙ U) :=
    (completedCoreToZeroLeftCommaNerveMap_value (C := C)).trans
      (nerveMapCommonHomUp_nerveMap_comp.{uC, max uC vC, 0} (Z ⋙ Y) U)
  exact (congrArg (fun h => (SSet.toTop.map h).hom) hNerve).trans
    (realizedNerveFunctorMap_commonUpFrame (Z ⋙ Y ⋙ U)).symm

/-- The literal original whole zero-comma realization is its SAME original composed-functor
  realization. -/
public theorem completedCoreToZeroLeftCommaRealization_value
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))).hom =
      realizedNerveFunctorMap (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) :=
  actualCompletedZeroCommaRealizationValue (C := C)

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualLeftRealizationComposite :
    realizedNerveFunctorMap ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
      zeroStructuredArrowMap F) =
      (realizedNerveFunctorMap (zeroStructuredArrowMap F)).comp
        (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))).hom := by
  let L := FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)
  exact (realizedNerveFunctorMap_comp_independent L (zeroStructuredArrowMap F)).trans
    (congrArg (fun h => (realizedNerveFunctorMap (zeroStructuredArrowMap F)).comp h)
      (completedCoreToZeroLeftCommaRealization_value (C := C)).symm)

omit [F.IsExact] [ExactCategory C] in
private theorem actualRightRealizationComposite :
    realizedNerveFunctorMap (completedCoreFunctor F ⋙
      FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
      FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
      Functor.fiberToStructuredArrow
        (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)) =
      (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := D))).hom.comp
        (realizedNerveFunctorMap (completedCoreFunctor F)) := by
  let R := FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)
  exact (realizedNerveFunctorMap_comp_independent (completedCoreFunctor F) R).trans
    (congrArg (fun h => h.comp (realizedNerveFunctorMap (completedCoreFunctor F)))
      (completedCoreToZeroLeftCommaRealization_value (C := D)).symm)

/-- The original mixed-world zero-comma scalar square has its actual whole forward homotopy. -/
public def completedZeroCommaRealizationHomotopy :
    ContinuousMap.Homotopy
      ((realizedNerveFunctorMap (zeroStructuredArrowMap F)).comp
        (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))).hom)
      ((SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := D))).hom.comp
        (realizedNerveFunctorMap (completedCoreFunctor F))) :=
  actualHomotopyEndpointTransport (actualLeftRealizationComposite F)
    (actualRightRealizationComposite F)
    (realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).hom)

/-- The SAME original inverse comma components give the whole reverse realization homotopy. -/
public def completedZeroCommaRealizationInverseHomotopy :
    ContinuousMap.Homotopy
      ((SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := D))).hom.comp
        (realizedNerveFunctorMap (completedCoreFunctor F)))
      ((realizedNerveFunctorMap (zeroStructuredArrowMap F)).comp
        (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))).hom) :=
  actualHomotopyEndpointTransport (actualRightRealizationComposite F)
    (actualLeftRealizationComposite F)
    (realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).inv)

private theorem actualForwardFamilyValue (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    completedZeroCommaRealizationHomotopy F (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).hom (t, x) :=
  actualHomotopyEndpointTransportValue (actualLeftRealizationComposite F)
    (actualRightRealizationComposite F)
    (realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).hom) t x

/-- Every forward interval value is the SAME original realized component-homotopy value. -/
public theorem completedZeroCommaRealizationHomotopy_value (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    completedZeroCommaRealizationHomotopy F (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).hom (t, x) :=
  actualForwardFamilyValue F t x

private theorem actualInverseFamilyValue (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    completedZeroCommaRealizationInverseHomotopy F (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).inv (t, x) :=
  actualHomotopyEndpointTransportValue (actualRightRealizationComposite F)
    (actualLeftRealizationComposite F)
    (realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).inv) t x

/-- Every reverse interval value retains the SAME original inverse component-homotopy value. -/
public theorem completedZeroCommaRealizationInverseHomotopy_value (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    completedZeroCommaRealizationInverseHomotopy F (t, x) =
      realizedNerveFunctorMapHomotopy (completedZeroCommaNaturalityIso F).inv (t, x) :=
  actualInverseFamilyValue F t x

private theorem actualSourceVertexValue (a : SInverse (Core C) (Core C)) :
    ((realizedNerveFunctorMap (zeroStructuredArrowMap F)).comp
      (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))).hom)
        (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        (((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
          Functor.fiberToStructuredArrow
            (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
          zeroStructuredArrowMap F).obj a)) := by
  let L := (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
    zeroStructuredArrowMap F
  have h := congrArg (fun k => k (SSet.realizedVertex
    (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a)))
    (actualLeftRealizationComposite F)
  exact h.symm.trans (realizedNerveFunctorMap_vertex L a)

/-- The scalar composite sends every original completed-Core vertex to its actual comma image. -/
public theorem completedZeroCommaRealization_source_vertex (a : SInverse (Core C) (Core C)) :
    ((realizedNerveFunctorMap (zeroStructuredArrowMap F)).comp
      (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))).hom)
        (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        (((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
          Functor.fiberToStructuredArrow
            (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
          zeroStructuredArrowMap F).obj a)) :=
  actualSourceVertexValue F a

omit [F.IsExact] [ExactCategory C] in
private theorem actualTargetVertexValue (a : SInverse (Core C) (Core C)) :
    ((SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := D))).hom.comp
      (realizedNerveFunctorMap (completedCoreFunctor F)))
        (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
          FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
          Functor.fiberToStructuredArrow
            (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)).obj a)) :=
                by
  let R := completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)
  have h := congrArg (fun k => k (SSet.realizedVertex
    (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a)))
    (actualRightRealizationComposite F)
  exact h.symm.trans (realizedNerveFunctorMap_vertex R a)

omit [F.IsExact] [ExactCategory C] in
/-- The original target comma map after the scalar Core map keeps every actual vertex image. -/
public theorem completedZeroCommaRealization_target_vertex (a : SInverse (Core C) (Core C)) :
    ((SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := D))).hom.comp
      (realizedNerveFunctorMap (completedCoreFunctor F)))
        (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a)) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
          FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
          Functor.fiberToStructuredArrow
            (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)).obj a)) :=
  actualTargetVertexValue F a

private theorem actualForwardVertexTrace (a : SInverse (Core C) (Core C)) :
    (((completedZeroCommaRealizationHomotopy F).evalAt
      (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a))).cast
        (completedZeroCommaRealization_source_vertex F a).symm
        (completedZeroCommaRealization_target_vertex F a).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((completedZeroCommaNaturalityIso F).hom.app a)))) := by
  let L := (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
    zeroStructuredArrowMap F
  let R := completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)
  let alpha : L ⟶ R := (completedZeroCommaNaturalityIso F).hom
  let H := realizedNerveFunctorMapHomotopy alpha
  have hOriginal := realizedNerveFunctorMapHomotopy_vertex alpha a
  have hPath :
      (((completedZeroCommaRealizationHomotopy F).evalAt
        (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀
            a))).cast
          (completedZeroCommaRealization_source_vertex F a).symm
          (completedZeroCommaRealization_target_vertex F a).symm) =
        ((H.evalAt (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
          (ComposableArrows.mk₀ a))).cast
            (realizedNerveFunctorMap_vertex L a).symm
            (realizedNerveFunctorMap_vertex R a).symm) := by
    apply Path.ext
    funext t
    exact completedZeroCommaRealizationHomotopy_value F t
      (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a))
  exact hPath.symm ▸ hOriginal

/-- The entire forward vertex trace is the SAME original forward comma-component edge up to
  endpoint-fixed path homotopy. -/
public theorem completedZeroCommaRealizationHomotopy_vertex (a : SInverse (Core C) (Core C)) :
    (((completedZeroCommaRealizationHomotopy F).evalAt
      (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a))).cast
        (completedZeroCommaRealization_source_vertex F a).symm
        (completedZeroCommaRealization_target_vertex F a).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((completedZeroCommaNaturalityIso F).hom.app a)))) :=
  actualForwardVertexTrace F a

private theorem actualInverseVertexTrace (a : SInverse (Core C) (Core C)) :
    (((completedZeroCommaRealizationInverseHomotopy F).evalAt
      (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a))).cast
        (completedZeroCommaRealization_target_vertex F a).symm
        (completedZeroCommaRealization_source_vertex F a).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((completedZeroCommaNaturalityIso F).inv.app a)))) := by
  let L := (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) ⋙
    zeroStructuredArrowMap F
  let R := completedCoreFunctor F ⋙ FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : D) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := D)) (⟨(0 : D)⟩ : QuillenQ D)
  let alpha : R ⟶ L := (completedZeroCommaNaturalityIso F).inv
  let H := realizedNerveFunctorMapHomotopy alpha
  have hOriginal := realizedNerveFunctorMapHomotopy_vertex alpha a
  have hPath :
      (((completedZeroCommaRealizationInverseHomotopy F).evalAt
        (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀
            a))).cast
          (completedZeroCommaRealization_target_vertex F a).symm
          (completedZeroCommaRealization_source_vertex F a).symm) =
        ((H.evalAt (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
          (ComposableArrows.mk₀ a))).cast
            (realizedNerveFunctorMap_vertex R a).symm
            (realizedNerveFunctorMap_vertex L a).symm) := by
    apply Path.ext
    funext t
    exact completedZeroCommaRealizationInverseHomotopy_value F t
      (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a))
  exact hPath.symm ▸ hOriginal

/-- The inverse vertex trace retains the SAME original inverse comma-component edge and both
  original endpoints. -/
public theorem completedZeroCommaRealizationInverseHomotopy_vertex (a : SInverse (Core C) (Core C))
    :
    (((completedZeroCommaRealizationInverseHomotopy F).evalAt
      (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ a))).cast
        (completedZeroCommaRealization_target_vertex F a).symm
        (completedZeroCommaRealization_source_vertex F a).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk ((completedZeroCommaNaturalityIso F).inv.app a)))) :=
  actualInverseVertexTrace F a

end AlgebraicKTheory.OriginalQZeroComparison

end
