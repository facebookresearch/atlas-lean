/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroFiberNaturality
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberLoopEquivalence
public import MathlibExt.CategoryTheory.Monoidal.CoreAdditiveFunctorMap
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The actual original completed-Core and total scalar unit

The whole original completed-Core functor retains both F-zero coordinates.
The original pair inclusion carries both canonical mapZeroObject Isos.
The original total NatIso at the source unit and this actual unit Iso give
the total-unit comparison. Its actual projected Q-zero Iso and entire
realized root path retain the original choices and independent worlds.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uD vD uE vE

namespace AlgebraicKTheory.OriginalQZeroComparison

private theorem originalHomEndpointTransportHEq
    {E : Type uE} [Category.{vE} E] {a b a' b' : E}
    (ha : a = a') (hb : b = b') (f : a ⟶ b) :
    HEq f (eqToHom ha.symm ≫ f ≫ eqToHom hb) := by
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact HEq.rfl

private theorem originalEdgePathHEqValue
    {E : Type uE} [Category.{vE} E] {a b a' b' : E}
    (ha : a = a') (hb : b = b') (f : a ⟶ b) (g : a' ⟶ b')
    (h : HEq f g) (t : unitInterval) :
    TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f)) t =
      TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk g)) t := by
  cases ha
  cases hb
  cases h
  rfl

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

/-- The SAME original completed functor's actual unit comparison maps BOTH
F-zero coordinates through their canonical Core.mapZeroObject Isos. -/
public def completedCoreOriginalUnitIso :
    (completedCoreFunctor F).obj
        ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))) ≅
      (SInverse.inclusion (Core D) (Core D)).obj (𝟙_ (Core D)) := by
  let a := (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
  let b := (SInverse.inclusion (Core D) (Core D)).obj (𝟙_ (Core D))
  let J := MonoidalActionCategory.inclusion (Core D) (Core D × Core D)
  let z : F.core.obj (𝟙_ (Core C)) ≅ 𝟙_ (Core D) := Core.isoMk F.mapZeroObject
  have hA : (completedCoreFunctor F).obj a =
      J.obj (F.core.obj (𝟙_ (Core C)), F.core.obj (𝟙_ (Core C))) :=
    (completedCoreFunctor_obj F a).trans (by rfl)
  have hB : J.obj (𝟙_ (Core D), 𝟙_ (Core D)) = b := rfl
  exact eqToIso hA ≪≫ J.mapIso (z.prod z) ≪≫ eqToIso hB

/-- The actual completed-unit root is the realized edge of that SAME Iso. -/
public def completedCoreOriginalUnitRootPath :
    Path (realizedNerveFunctorMap (completedCoreFunctor F)
        (SSet.realizedVertex (ComposableArrows.mk₀
          ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))))
      (SSet.realizedVertex (ComposableArrows.mk₀
        ((SInverse.inclusion (Core D) (Core D)).obj (𝟙_ (Core D))))) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (completedCoreOriginalUnitIso
      F).hom))).cast
    (realizedNerveFunctorMap_vertex (completedCoreFunctor F)
      ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))) rfl

variable [ExactCategory C] [ExactCategory D] [F.IsExact]

private theorem originalZeroFiberUnitTotalValue
    {E : Type uE} [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    (zeroFiberUnit (C := E)).val =
      (FixedTargetExtension.zeroLocalizedFunctor (C := E) ⋙
        FixedTargetExtension.localizedForget (0 : E)).obj
          ((SInverse.inclusion (Core E) (Core E)).obj (𝟙_ (Core E))) :=
  Functor.congr_obj (FixedTargetExtension.localizedFiberFunctor_forget (C := E) (X := (0 : E)))
    ((FixedTargetExtension.zeroLocalizedFunctor (C := E)).obj
      ((SInverse.inclusion (Core E) (Core E)).obj (𝟙_ (Core E))))

/-- The actual total-unit Iso retains the SAME original total NatIso component
and the original zero-total functor's image of BOTH mapped Core-unit coordinates. -/
public def originalMappedTotalUnitIso :
    (ExtensionCategory.stabilizedFunctorMap F).obj (zeroFiberUnit (C := C)).val ≅
      (zeroFiberUnit (C := D)).val := by
  let a := (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
  let Z := FixedTargetExtension.zeroLocalizedFunctor (C := D) ⋙
    FixedTargetExtension.localizedForget (0 : D)
  let T := ExtensionCategory.stabilizedFunctorMap F
  have hA : T.obj (zeroFiberUnit (C := C)).val =
      (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedForget (0 : C) ⋙ T).obj a :=
    congrArg T.obj (originalZeroFiberUnitTotalValue (E := C))
  exact eqToIso hA ≪≫ (FixedTargetExtension.completedZeroTotalNaturalityIso F).app a ≪≫
    Z.mapIso (completedCoreOriginalUnitIso F) ≪≫
      eqToIso (originalZeroFiberUnitTotalValue (E := D)).symm

private theorem originalMappedTotalUnitBaseSource :
    (ExtensionCategory.localizedTarget (C := D)).obj
        ((ExtensionCategory.stabilizedFunctorMap F).obj (zeroFiberUnit (C := C)).val) =
      (QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C) :=
  (Functor.congr_obj (ExtensionCategory.stabilizedFunctorMap_target F)
    (zeroFiberUnit (C := C)).val).trans
      (congrArg (QuillenQ.map F).obj (zeroFiberUnit_target (C := C)))

private theorem originalMappedTotalUnitBaseHomHEq :
    HEq ((ExtensionCategory.localizedTarget (C := D)).map (originalMappedTotalUnitIso F).hom)
      (QuillenQ.zeroComparisonIso F).hom := by
  have hA := originalMappedTotalUnitBaseSource F
  have hB := zeroFiberUnit_target (C := D)
  let X := (ExtensionCategory.localizedTarget (C := D)).obj
    ((ExtensionCategory.stabilizedFunctorMap F).obj (zeroFiberUnit (C := C)).val)
  let Y := (ExtensionCategory.localizedTarget (C := D)).obj (zeroFiberUnit (C := D)).val
  let f : X ⟶ Y := (ExtensionCategory.localizedTarget (C := D)).map (originalMappedTotalUnitIso
      F).hom
  have hZero : IsZero (⟨(0 : D)⟩ : QuillenQ D).obj := isZero_zero D
  have hCast : eqToHom hA.symm ≫ f ≫ eqToHom hB = (QuillenQ.zeroComparisonIso F).hom :=
    QuillenQ.hom_eq_of_target_isZero _ _ hZero
  have hUncast : HEq f (eqToHom hA.symm ≫ f ≫ eqToHom hB) :=
    originalHomEndpointTransportHEq hA hB f
  exact hUncast.trans (heq_of_eq hCast)

/-- The entire actual projected total-unit Iso is the original mapped-zero
comparison after ONLY its internally proved original endpoint transports. -/
public theorem originalMappedTotalUnitIso_base_value :
    eqToIso ((Functor.congr_obj (ExtensionCategory.stabilizedFunctorMap_target F)
        (zeroFiberUnit (C := C)).val).trans
      (congrArg (QuillenQ.map F).obj (zeroFiberUnit_target (C := C)))).symm ≪≫
        (ExtensionCategory.localizedTarget (C := D)).mapIso (originalMappedTotalUnitIso F) ≪≫
        eqToIso (zeroFiberUnit_target (C := D)) = QuillenQ.zeroComparisonIso F := by
  apply Iso.ext
  exact QuillenQ.hom_eq_of_target_isZero _ _ (isZero_zero D)

/-- The actual total-unit path is the SAME entire realized original total-unit edge. -/
public def originalMappedTotalUnitPath :
    Path (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)
        (zeroTotalVertex (C := C))) (zeroTotalVertex (C := D)) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (originalMappedTotalUnitIso F).hom))).cast
    (realizedNerveFunctorMap_vertex (ExtensionCategory.stabilizedFunctorMap F)
      (zeroFiberUnit (C := C)).val) rfl

private theorem originalMappedTotalUnitPathValueComputed (t : unitInterval) :
    originalMappedTotalUnitPath F t =
      TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (originalMappedTotalUnitIso F).hom)) t
          :=
  rfl

/-- EVERY time of the actual total-unit path retains the SAME original total-unit edge. -/
public theorem originalMappedTotalUnitPath_value (t : unitInterval) :
    originalMappedTotalUnitPath F t =
      TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (originalMappedTotalUnitIso F).hom)) t
          :=
  originalMappedTotalUnitPathValueComputed F t

private abbrev originalUnitProjection
    {E : Type uE} [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :=
  SSet.toTop.map (nerveMapCommonHom.{uE, max uE vE, 0}
    (ExtensionCategory.localizedTarget (C := E)))

private theorem originalMappedTotalUnitPathBaseSource :
    QuillenMixedUniverseTransport.mixedNQRealMap F (NQReal.basepoint C) =
      originalUnitProjection (E := D)
        (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)
          (zeroTotalVertex (C := C))) := by
  let T := ExtensionCategory.stabilizedFunctorMap F
  let P := ExtensionCategory.localizedTarget (C := D)
  let a := (zeroFiberUnit (C := C)).val
  have hT : realizedNerveFunctorMap T (zeroTotalVertex (C := C)) =
      SSet.realizedVertex (ComposableArrows.mk₀ (T.obj a)) := realizedNerveFunctorMap_vertex T a
  have hP : originalUnitProjection (E := D)
        (SSet.realizedVertex (ComposableArrows.mk₀ (T.obj a))) =
      SSet.realizedVertex (ComposableArrows.mk₀ (P.obj (T.obj a))) :=
    (congrArg (fun m => m (SSet.realizedVertex (ComposableArrows.mk₀ (T.obj a))))
      (realizedNerveFunctorMap_commonDownFrame.{uD, max uD vD} P)).symm.trans
        (realizedNerveFunctorMap_vertex P (T.obj a))
  have hObj := congrArg (fun y : QuillenQ D => SSet.realizedVertex
        (X := (nerve (QuillenQ D) : SSet.{max uD vD})) (ComposableArrows.mk₀ y))
    (originalMappedTotalUnitBaseSource F)
  have hTotal := (congrArg (originalUnitProjection (E := D)) hT).trans (hP.trans hObj)
  exact (QuillenMixedUniverseTransport.mixedNQRealMap_zeroVertex F).trans hTotal.symm

private theorem originalTotalUnitPathBaseTarget
    {E : Type uE} [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    NQReal.basepoint E = originalUnitProjection (E := E) (zeroTotalVertex (C := E)) :=
  (NQReal.basepoint_eq_realizedVertex E).trans (zeroTotalVertex_map (C := E)).symm

/-- The base path is the literal projection of the actual whole total-unit path,
with only the internally proved original Q-basepoint endpoint transports. -/
public def originalMappedTotalUnitBasePath :
    Path (QuillenMixedUniverseTransport.mixedNQRealMap F (NQReal.basepoint C)) (NQReal.basepoint D)
        :=
  ((originalMappedTotalUnitPath F).map (originalUnitProjection (E := D)).hom.continuous).cast
    (originalMappedTotalUnitPathBaseSource F) (originalTotalUnitPathBaseTarget (E := D))

private theorem originalMappedTotalUnitBasePathValueComputed (t : unitInterval) :
    originalMappedTotalUnitBasePath F t =
      SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
        (ExtensionCategory.localizedTarget (C := D))) (originalMappedTotalUnitPath F t) := rfl

/-- EVERY projected original total-unit time retains the actual common-Hom projection. -/
public theorem originalMappedTotalUnitBasePath_value (t : unitInterval) :
    originalMappedTotalUnitBasePath F t =
      SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
        (ExtensionCategory.localizedTarget (C := D))) (originalMappedTotalUnitPath F t) :=
  originalMappedTotalUnitBasePathValueComputed F t

/-- The whole original total-unit path projects to the SAME canonical original
mixed Q root up to an endpoint-fixed path homotopy, derived from its actual Iso. -/
public theorem originalMappedTotalUnitBasePath_homotopic_root :
    (originalMappedTotalUnitBasePath F).Homotopic (QuillenMixedUniverseTransport.mixedNQRootPath F)
        := by
  let T := ExtensionCategory.stabilizedFunctorMap F
  let P := ExtensionCategory.localizedTarget (C := D)
  let a := T.obj (zeroFiberUnit (C := C)).val
  let b := (zeroFiberUnit (C := D)).val
  let f : a ⟶ b := (originalMappedTotalUnitIso F).hom
  have hs : QuillenMixedUniverseTransport.mixedNQRealMap F (NQReal.basepoint C) =
      SSet.realizedVertex (ComposableArrows.mk₀ (P.obj a)) :=
    (QuillenMixedUniverseTransport.mixedNQRealMap_zeroVertex F).trans
      (congrArg (fun y : QuillenQ D => SSet.realizedVertex
        (X := (nerve (QuillenQ D) : SSet.{max uD vD})) (ComposableArrows.mk₀ y))
        (originalMappedTotalUnitBaseSource F)).symm
  have ht : NQReal.basepoint D = SSet.realizedVertex (ComposableArrows.mk₀ (P.obj b)) :=
    (NQReal.basepoint_eq_realizedVertex D).trans
      (congrArg (fun y : QuillenQ D => SSet.realizedVertex
        (X := (nerve (QuillenQ D) : SSet.{max uD vD})) (ComposableArrows.mk₀ y))
        (zeroFiberUnit_target (C := D))).symm
  have hActual := (realizedNerveFunctorMap_edge_homotopic P f).pathCast hs ht
  have hLeft : (((TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk f))).map
      (realizedNerveFunctorMap P).continuous).cast
        (realizedNerveFunctorMap_vertex P a).symm
        (realizedNerveFunctorMap_vertex P b).symm).cast hs ht = originalMappedTotalUnitBasePath F :=
            by
    apply Path.ext
    funext t
    have hValue := congrArg (fun m => m (TopCat.pathEquiv
      (SSet.realizedEdgePath (nerve.edgeMk f)) t))
        (realizedNerveFunctorMap_commonDownFrame.{uD, max uD vD} P)
    exact hValue.trans ((congrArg (originalUnitProjection (E := D))
      (originalMappedTotalUnitPath_value F t).symm).trans
        (originalMappedTotalUnitBasePath_value F t).symm)
  have hRight : (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (P.map f)))).cast hs ht =
      QuillenMixedUniverseTransport.mixedNQRootPath F := by
    apply Path.ext
    funext t
    exact (originalEdgePathHEqValue (originalMappedTotalUnitBaseSource F)
      (zeroFiberUnit_target (C := D)) (P.map f) (QuillenQ.zeroComparisonIso F).hom
      (originalMappedTotalUnitBaseHomHEq F) t).trans
        (QuillenMixedUniverseTransport.mixedNQRootPath_value F t).symm
  exact hLeft ▸ hRight ▸ hActual

end AlgebraicKTheory.OriginalQZeroComparison

end
