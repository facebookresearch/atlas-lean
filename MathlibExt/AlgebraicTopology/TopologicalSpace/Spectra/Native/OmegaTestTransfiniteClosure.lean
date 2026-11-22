/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OmegaTestHomotopyCofiberClosure
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourcePreservation
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import MathlibExt.CategoryTheory.SmallObject.SourceMappingLimit
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.HomotopyExtensionClosure

/-!
# Actual native mapping limits of continuous ordinal cocones

The literal native weighted end sends every actual source colimit to a limit.
This file keeps the original well-order-continuous diagram, cocone point,
all restriction maps and the original initial endpoint. Limit preservation
is proved from the native tensor/cotensor adjunction; weakness of the final
restriction is a separate subsequent homotopy argument.
-/

set_option autoImplicit false
noncomputable section
universe u v w w' uC vC uV vV

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed


namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  {J : Type w} [Category.{w'} J]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The whole original source diagram, contravariantly mapped to native weighted ends. -/
def sourceMappingDiagram (F : J ⥤ D (I := I)) (E : D (I := I)) :
    Jᵒᵖ ⥤ PointedCGWH.{u, v} :=
  OriginalSourceMappingLimit.diagram (PointedCGWH.NativeMappingSourceFunctor.source E) F

/-- The literal source mapping cone of the caller's actual cocone. -/
def sourceMappingCone {F : J ⥤ D (I := I)} (c : Cocone F) (E : D (I := I)) :
    Cone (sourceMappingDiagram F E) :=
  OriginalSourceMappingLimit.cone (PointedCGWH.NativeMappingSourceFunctor.source E) c

/-- Every original cocone leg is retained as the full native source restriction. -/
theorem sourceMappingCone_π {F : J ⥤ D (I := I)} (c : Cocone F)
    (E : D (I := I)) (j : Jᵒᵖ) :
    (sourceMappingCone c E).π.app j =
      (PointedCGWH.NativeMappingSourceFunctor.source E).map (c.ι.app j.unop).op := rfl

/-- The original source colimit gives an actual native mapping limit without a supplied
mapping preservation hypothesis. -/
def sourceMappingConeIsLimit {F : J ⥤ D (I := I)} (c : Cocone F)
    (hc : IsColimit c) (E : D (I := I)) : IsLimit (sourceMappingCone c E) := by
  let : PreservesLimitsOfSize.{w', w}
      (PointedCGWH.NativeMappingSourceFunctor.source E) :=
    PointedCGWH.NativeMappingSourcePreservation.source_preservesLimitsOfSize E
  exact OriginalSourceMappingLimit.isLimit (PointedCGWH.NativeMappingSourceFunctor.source E) c hc

/-- The full native universal map and all original projection equations use one actual
chosen limiting witness. -/
def sourceMappingLiftData {F : J ⥤ D (I := I)} (c : Cocone F)
    (hc : IsColimit c) (E : D (I := I)) (s : Cone (sourceMappingDiagram F E)) :
    OriginalSourceMappingLimit.ChosenLift (sourceMappingCone c E) s :=
  OriginalSourceMappingLimit.chosenLift (sourceMappingCone c E) (sourceMappingConeIsLimit c hc E) s

/-- Every full actual cone lifts through the original native mapping limit. -/
def sourceMappingLift {F : J ⥤ D (I := I)} (c : Cocone F)
    (hc : IsColimit c) (E : D (I := I)) (s : Cone (sourceMappingDiagram F E)) :
    s.pt ⟶ (sourceMappingCone c E).pt :=
  (sourceMappingLiftData c hc E s).hom

/-- The full native mapping lift is the same actual original limiting witness's map. -/
theorem sourceMappingLift_eq_isLimitLift {F : J ⥤ D (I := I)} (c : Cocone F)
    (hc : IsColimit c) (E : D (I := I)) (s : Cone (sourceMappingDiagram F E)) :
    sourceMappingLift c hc E s = (sourceMappingConeIsLimit c hc E).lift s :=
  OriginalSourceMappingLimit.chosenLift_hom
    (sourceMappingCone c E) (sourceMappingConeIsLimit c hc E) s

/-- The lift retains every original restriction equation, at all indices. -/
@[reassoc]
theorem sourceMappingLift_π {F : J ⥤ D (I := I)} (c : Cocone F)
    (hc : IsColimit c) (E : D (I := I)) (s : Cone (sourceMappingDiagram F E))
    (j : Jᵒᵖ) :
    sourceMappingLift c hc E s ≫ (sourceMappingCone c E).π.app j = s.π.app j :=
  (congrArg (fun f : s.pt ⟶ (sourceMappingCone c E).pt =>
    f ≫ (sourceMappingCone c E).π.app j) (sourceMappingLift_eq_isLimitLift c hc E s)).trans
      ((sourceMappingConeIsLimit c hc E).fac s j)

/-- Equality of complete source mapping maps is detected by all original cocone legs. -/
theorem sourceMapping_hom_ext {F : J ⥤ D (I := I)} (c : Cocone F)
    (hc : IsColimit c) (E : D (I := I)) {T : PointedCGWH.{u, v}}
    {a b : T ⟶ (sourceMappingCone c E).pt}
    (h : ∀ j : Jᵒᵖ, a ≫ (sourceMappingCone c E).π.app j =
      b ≫ (sourceMappingCone c E).π.app j) : a = b :=
  (sourceMappingConeIsLimit c hc E).hom_ext h

section Ordinal

variable [Preorder J] [OrderBot J]

/-- The complete initial restriction of an actual continuous ordinal cocone. -/
def ordinalInitialRestriction (F : J ⥤ D (I := I)) (c : Cocone F)
    (E : D (I := I)) : (sourceMappingCone c E).pt ⟶
      (sourceMappingDiagram F E).obj (Opposite.op ⊥) :=
  (sourceMappingCone c E).π.app (Opposite.op ⊥)

/-- The actual initial restriction is the original cocone's bottom leg under the same source
mapping functor. -/
theorem ordinalInitialRestriction_eq (F : J ⥤ D (I := I)) (c : Cocone F)
    (E : D (I := I)) :
    ordinalInitialRestriction F c E =
      (PointedCGWH.NativeMappingSourceFunctor.source E).map (c.ι.app ⊥).op := rfl

end Ordinal

end PointedCGWH.Spectra.NativeOmegaWeakClosure
namespace TopCat

open CategoryTheory CategoryTheory.Limits Topology

/-- A pointwise weak map between actual closed-T1 diagrams gives a weak map between their
chosen colimits. All source and target cocone legs are kept; no endpoint cofibrancy enters. -/
theorem closedOrdinalCoconeComparison_weak
    {J : Type w} [LinearOrder J] [OrderBot J] [UnivLE.{w, v}]
    {F G : J ⥤ TopCat.{v}} (c : Cocone F) (d : Cocone G)
    (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    (hG : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (G.map f))
    (a : F ⟶ G) (ha : ∀ j : J, weakHomotopyEquivalences (a.app j))
    (f : c.pt ⟶ d.pt) (hf : ∀ j : J, c.ι.app j ≫ f = a.app j ≫ d.ι.app j) :
    weakHomotopyEquivalences f := by
  let : IsFiltered J := inferInstance
  let : PreservesColimit F TopCat.toSSet := preservesColimit_toSSet_of_closedT1_transfinite hF
  let : PreservesColimit G TopCat.toSSet := preservesColimit_toSSet_of_closedT1_transfinite hG
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (F ⋙ TopCat.toSSet) (G ⋙ TopCat.toSSet)
    (TopCat.toSSet.mapCocone c) (TopCat.toSSet.mapCocone d)
    (isColimitOfPreserves TopCat.toSSet hc) (isColimitOfPreserves TopCat.toSSet hd)
    (Functor.whiskerRight a TopCat.toSSet)
    (fun j => (mem_weakHomotopyEquivalences_iff (a.app j)).mp (ha j))
    (TopCat.toSSet.map f) (fun j => by
      simpa only [Functor.mapCocone_ι_app, Functor.whiskerRight_app,
        ← TopCat.toSSet.map_comp] using congrArg TopCat.toSSet.map (hf j))

end TopCat

namespace CGWH

open CategoryTheory CategoryTheory.Limits Topology

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The caller's same continuous native ordinal cocone is a topological colimit when all
actual successor maps are closed embeddings. -/
def closedOrdinalCoconeIsColimitTop (F : J ⥤ CGWH.{u, v}) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j → IsClosedEmbedding
      (ConcreteCategory.hom (F.map (homOfLE (Order.le_succ j))))) :
    IsColimit (CGWH.cgwhToTop.mapCocone c) := by
  have hC := CGWH.isColimitMapCoconeOfInjectiveSucc F
    (fun j hj => (hF j hj).injective) c hc
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves CompactlyGenerated.compactlyGeneratedToTop hC)
    (Cocone.ext (Iso.refl _))

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
/-- Every genuine native closed transition is closed-T1 in the actual underlying diagram. -/
theorem ordinalClosedMap_closedT1 {F : J ⥤ CGWH.{u, v}}
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    {i j : J} (f : i ⟶ j) : TopCat.closedT1Embeddings ((F ⋙ CGWH.cgwhToTop).map f) :=
  { toIsClosedEmbedding := hF f
    isClosed_singleton_of_notMem_range := fun x _hx => by
      change IsClosed ({x} : Set (F.obj j))
      exact isClosed_singleton }

/-- The actual original comparison of two continuous native closed diagrams is level weak
when every complete original stage comparison is level weak. -/
theorem closedOrdinalCoconeComparison_weak
    {F G : J ⥤ CGWH.{u, v}} [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (F.map f)))
    (hG : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (ConcreteCategory.hom (G.map f)))
    (a : F ⟶ G) (ha : ∀ j : J, CGWH.weakHomotopyEquivalences (a.app j))
    (f : c.pt ⟶ d.pt) (hf : ∀ j : J, c.ι.app j ≫ f = a.app j ≫ d.ι.app j) :
    CGWH.weakHomotopyEquivalences f := by
  change TopCat.weakHomotopyEquivalences (CGWH.cgwhToTop.map f)
  exact TopCat.closedOrdinalCoconeComparison_weak
    (CGWH.cgwhToTop.mapCocone c) (CGWH.cgwhToTop.mapCocone d)
    (closedOrdinalCoconeIsColimitTop F c hc (fun j _hj => hF _))
    (closedOrdinalCoconeIsColimitTop G d hd (fun j _hj => hG _))
    (fun _ _ g => ordinalClosedMap_closedT1 hF g)
    (fun _ _ g => ordinalClosedMap_closedT1 hG g)
    (Functor.whiskerRight a CGWH.cgwhToTop) ha (CGWH.cgwhToTop.map f)
    (fun j => by
      simpa only [Functor.mapCocone_ι_app, Functor.whiskerRight_app,
        ← CGWH.cgwhToTop.map_comp] using congrArg CGWH.cgwhToTop.map (hf j))

end CGWH
namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped MonoidalClosed CGWH.modelCategory

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits

private abbrev NativeD := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The actual caller continuous cocone gives an original HEP transfinite witness, with the
same functor, bottom, endpoint, legs and universal property. -/
def originalHEPOrdinalWitness {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] (F : J ⥤ NativeD (I := I)) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j)))) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property.TransfiniteCompositionOfShape J
      (c.ι.app ⊥) where
  F := F
  isoBot := Iso.refl (F.obj ⊥)
  incl := c.ι
  isColimit := hc
  fac := Category.id_comp _
  map_mem := hF

/-- Every original transition of the actual continuous HEP diagram has genuine HEP,
including maps crossing limit stages. -/
theorem originalHEPOrdinal_map_mem {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] (F : J ⥤ NativeD (I := I)) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j)))) {i j : J} (f : i ⟶ j) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property (F.map f) :=
  (originalHEPOrdinalWitness F c hc hF).mem_map f

/-- Every actual native level of every original HEP transition is a closed inclusion.
The entire well-order continuity and original cocone are retained. -/
theorem originalHEPOrdinal_component_closed {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] (F : J ⥤ NativeD (I := I)) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j)))) {i j : J} (f : i ⟶ j) (a : I) :
    Topology.IsClosedEmbedding (ConcreteCategory.hom (component (F.map f) a).right) :=
  nativeHEP_component_closed (F.map f) (originalHEPOrdinal_map_mem F c hc hF f) a

/-- The full endpoint at every original native level is closed for the actual caller cocone. -/
theorem originalHEPOrdinal_endpoint_component_closed {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J] (F : J ⥤ NativeD (I := I)) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j)))) (a : I) :
    Topology.IsClosedEmbedding (ConcreteCategory.hom (component (c.ι.app ⊥) a).right) :=
  nativeHEP_component_closed (c.ι.app ⊥)
    (PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.nativeHEP_colimit_endpoint_mem
      J F c hc hF) a

end PointedCGWH.Spectra.NativeOmegaWeakClosure
namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev NativeCarrier := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The actual native CGWH colimit construction gives the original pointed small colimits. -/
private instance nativePointedSmallColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

/-- The complete native level functor retains actual evaluation and the original chosen
point-forgetting map. -/
def originalNativeLevel (a : I) : NativeCarrier (I := I) ⥤ CGWH.{u, v} :=
  evaluation a ⋙ PointedCGWH.pointedToCGWH

/-- Actual native evaluation followed by pointed forgetting preserves every connected
colimit of the original allowable size. -/
theorem originalNativeLevel_preservesConnected {K : Type v} [Category.{v} K]
    [IsConnected K] (a : I) : PreservesColimitsOfShape K (originalNativeLevel a) := by
  let : PreservesColimitsOfShape K (evaluation (V := PointedCGWH.{u, v}) a) :=
    CategoryTheory.EnrichedFunctorCat.evaluationPreservesColimitsOfShape a
  let : PreservesColimitsOfShape K PointedCGWH.pointedToCGWH.{u, v} :=
    Under.preservesColimitsOfShape_forget_of_isConnected
  change PreservesColimitsOfShape K (evaluation a ⋙ PointedCGWH.pointedToCGWH)
  infer_instance

/-- Every actual original endpoint and principal-segment cocone is preserved by the same
native level functor. No preservation of arbitrary disconnected pointed colimits is claimed. -/
def originalNativeLevelOrdinalWitness (F : J ⥤ NativeCarrier (I := I)) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j)))) (a : I) :
    CategoryTheory.TransfiniteCompositionOfShape J
      ((originalNativeLevel a).map (c.ι.app ⊥)) := by
  let U := originalNativeLevel a
  let : IsFiltered J := inferInstance
  let : IsConnected J := IsFiltered.isConnected J
  let : PreservesColimitsOfShape J U := originalNativeLevel_preservesConnected a
  let : PreservesColimit F U := inferInstance
  have hLimit (m : J) (hm : Order.IsSuccLimit m) :
      PreservesColimit ((Set.principalSegIio m).monotone.functor ⋙ F) U := by
    let : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    let : OrderBot (Set.Iio m) :=
      { bot := ⟨⊥, hm.bot_lt⟩
        bot_le := fun _ => bot_le }
    let : IsFiltered (Set.Iio m) := inferInstance
    let : IsConnected (Set.Iio m) := IsFiltered.isConnected (Set.Iio m)
    let : PreservesColimitsOfShape (Set.Iio m) U := originalNativeLevel_preservesConnected a
    infer_instance
  let witness := (originalHEPOrdinalWitness F c hc hF).toTransfiniteCompositionOfShape
  let : PreservesColimit witness.F U := by
    change PreservesColimit F U
    infer_instance
  exact witness.mapOfPreserves U hLimit

/-- The caller's same native level cocone remains colimiting. -/
def originalNativeLevelCoconeIsColimit (F : J ⥤ NativeCarrier (I := I))
    (c : Cocone F) (hc : IsColimit c) (a : I) :
    IsColimit ((originalNativeLevel a).mapCocone c) := by
  let : IsFiltered J := inferInstance
  let : IsConnected J := IsFiltered.isConnected J
  let : PreservesColimitsOfShape J (originalNativeLevel a) :=
    originalNativeLevel_preservesConnected a
  exact isColimitOfPreserves (originalNativeLevel a) hc

omit [SuccOrder J] [WellFoundedLT J] in
/-- The actual evaluated/forgotten diagram remains well-order continuous, with all
original limit-stage maps and cocones retained. -/
theorem originalNativeLevel_continuous (F : J ⥤ NativeCarrier (I := I)) [F.IsWellOrderContinuous]
    (a : I) :
    (F ⋙ originalNativeLevel a).IsWellOrderContinuous := by
  constructor
  intro m hm
  let : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
  let : OrderBot (Set.Iio m) :=
    { bot := ⟨⊥, hm.bot_lt⟩
      bot_le := fun x => show (⊥ : J) ≤ x.1 from bot_le }
  let : IsFiltered (Set.Iio m) := inferInstance
  let : IsConnected (Set.Iio m) := IsFiltered.isConnected (Set.Iio m)
  let : PreservesColimitsOfShape (Set.Iio m) (originalNativeLevel a) :=
    originalNativeLevel_preservesConnected a
  exact ⟨isColimitOfPreserves (originalNativeLevel a)
    (F.isColimitOfIsWellOrderContinuous m hm)⟩

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- All original stage weak maps retain every actual native level and chosen point. -/
theorem originalNativeLevel_weak {X Y : NativeCarrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (NativeCarrier (I := I)) f) (a : I) :
    CGWH.weakHomotopyEquivalences ((originalNativeLevel a).map f) := by
  rw [Native.weakEquivalences_eq] at hf
  have hPointed : weakEquivalences PointedCGWH.{u, v} ((evaluation a).map f) :=
    (EvaluationTransfer.evaluationProperty_iff
      (fun b : I => evaluation b) (weakEquivalences PointedCGWH.{u, v}) f).mp hf a
  have hPW : WeakEquivalence ((evaluation a).map f) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr hPointed
  have hCG : WeakEquivalence (((evaluation a).map f).right) :=
    (PointedCGWH.weakEquivalence_iff _).mp hPW
  exact (CGWH.modelCategory.weakEquivalence_iff _).mp hCG

/-- A pointwise original level weak map between actual continuous native HEP diagrams
induces an original level weak map between the caller's same chosen colimits. All original
stage maps, endpoints, ordinal limits and both full cocone legs remain explicit. -/
theorem originalHEPOrdinal_levelWeak_comparison
    {F G : J ⥤ NativeCarrier (I := I)} [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (G.map (homOfLE (Order.le_succ j))))
    (a : F ⟶ G) (ha : ∀ j : J, weakEquivalences (NativeCarrier (I := I)) (a.app j))
    (f : c.pt ⟶ d.pt) (hf : ∀ j : J, c.ι.app j ≫ f = a.app j ≫ d.ι.app j) :
    weakEquivalences (NativeCarrier (I := I)) f := by
  rw [Native.weakEquivalences_eq]
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun b : I => evaluation b) (weakEquivalences PointedCGWH.{u, v}) f).mpr
  intro b
  let U := originalNativeLevel b
  let : (F ⋙ U).IsWellOrderContinuous := originalNativeLevel_continuous F b
  let : (G ⋙ U).IsWellOrderContinuous := originalNativeLevel_continuous G b
  have hCG : CGWH.weakHomotopyEquivalences (U.map f) :=
    CGWH.closedOrdinalCoconeComparison_weak
      (U.mapCocone c) (U.mapCocone d)
      (originalNativeLevelCoconeIsColimit F c hc b)
      (originalNativeLevelCoconeIsColimit G d hd b)
      (fun _ _ g => originalHEPOrdinal_component_closed F c hc hF g b)
      (fun _ _ g => originalHEPOrdinal_component_closed G d hd hG g b)
      (Functor.whiskerRight a U)
      (fun j => originalNativeLevel_weak (a.app j) (ha j) b) (U.map f)
      (fun j => by
        simpa only [Functor.mapCocone_ι_app, Functor.whiskerRight_app,
          ← U.map_comp] using congrArg U.map (hf j))
  have hCW : WeakEquivalence (((evaluation b).map f).right) :=
    (CGWH.modelCategory.weakEquivalence_iff _).mpr hCG
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    ((PointedCGWH.weakEquivalence_iff _).mpr hCW)

end PointedCGWH.Spectra.NativeOmegaWeakClosure
