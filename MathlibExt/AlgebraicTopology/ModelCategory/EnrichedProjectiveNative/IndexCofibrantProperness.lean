/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Data
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.Proper
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantTensorPowers
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHProper
public import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen
public import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer.Proper

/-!
# Actual native index-Hom cofibrancy and derived level left properness

The explicit source proof says every original enriched index Hom is
cofibrant. The original native generation record and the general evaluated-left
class API prove every native projective cofibration is a base cofibration
at every evaluation, retaining the original I, cardinal and B. The general
cofibrant-Hom properness API and proved CGWH properness derive native
level left properness. No target properness or final model is assumed.
The original I and J maps retain their complete evaluated classes.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

private instance originalCardinalRegular : Fact realizedGeneratorCardinal.{v}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal⟩

private instance originalPointedColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexCofibrantProperness

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] CGWH.modelCategory.instPointedCGWHIsClosedSymmetricMonoidalModelCategory

/-- Tensoring any original cofibration by the actual source-index Hom preserves cofibrations. -/
theorem indexHom_tensorRight_cofibration
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (a b : I) {A C : PointedCGWH.{u, v}} (f : A ⟶ C)
    (hf : cofibrations PointedCGWH.{u, v} f) :
    cofibrations PointedCGWH.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  let H := (a ⟶[PointedCGWH.{u, v}] b)
  let _ : IsCofibrant H := hHom a b
  have h := IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations H f hf
  let e : tensorLeft H ≅ tensorRight H := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight H
  let eArrow : CategoryTheory.Arrow.mk (H ◁ f) ≅ CategoryTheory.Arrow.mk (f ▷ H) :=
    Arrow.isoMk' _ _ (e.app A) (e.app C) (e.hom.naturality f).symm
  exact ((cofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff eArrow).mp h

/-- The SAME actual source Hom also preserves original trivial cofibrations. -/
theorem indexHom_tensorRight_trivialCofibration
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (a b : I) {A C : PointedCGWH.{u, v}} (f : A ⟶ C)
    (hf : trivialCofibrations PointedCGWH.{u, v} f) :
    trivialCofibrations PointedCGWH.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  let H := (a ⟶[PointedCGWH.{u, v}] b)
  let _ : IsCofibrant H := hHom a b
  have h := IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_trivialCofibrations H f hf
  let e : tensorLeft H ≅ tensorRight H := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight H
  let eArrow : CategoryTheory.Arrow.mk (H ◁ f) ≅ CategoryTheory.Arrow.mk (f ▷ H) :=
    Arrow.isoMk' _ _ (e.app A) (e.app C) (e.hom.naturality f).symm
  exact ((trivialCofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff eArrow).mp h

private theorem originalPointedI_le_cofibrations :
    PointedCGWH.realizedBoundaryInclusions.{u, v} ≤ cofibrations PointedCGWH.{u, v} := by
  intro A C i hi
  have h := PointedCGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp i hi
  have hI : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.I_rlp
  rwa [hI, trivialFibrations_llp] at h

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every original native projective Cof map is a base Cof at EVERY complete evaluation. -/
theorem originalNativeCofibration_component_cofibration
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) f) (a : I) :
    cofibrations PointedCGWH.{u, v} ((evaluation a).map f) := by
  let _ : (cofibrations PointedCGWH.{u, v}).IsStableUnderCoproducts.{v} :=
    IsStableUnderCoproducts.of_llp_eq _ _ (trivialFibrations_llp _)
  let _ : (cofibrations PointedCGWH.{u, v}).IsStableUnderTransfiniteCompositionOfShape
      realizedGeneratorCardinal.{v}.ord.ToType := by
    rw [← trivialFibrations_llp PointedCGWH.{u, v}]
    infer_instance
  have h := HomotopicalAlgebra.EnrichedProjective.cofibrations_le_evaluationProperty
    (Native.Data.generationData (A := I) (B := B))
    PointedCGWH.realizedBoundaryInclusions.{u, v} (cofibrations PointedCGWH.{u, v})
    (Native.Data.generationData_I (A := I) (B := B))
    (fun b c {A C} i hi => indexHom_tensorRight_cofibration hHom b c i
      (originalPointedI_le_cofibrations i hi))
  exact (EvaluationTransfer.evaluationProperty_iff
    (fun b : I => evaluation (V := PointedCGWH.{u, v}) b)
    (cofibrations PointedCGWH.{u, v}) f).mp (h f hf) a

/-- The full original pointwise level weak class retains every actual evaluation function. -/
theorem originalNativeLevelWeak_iff_evaluation
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f ↔
      ∀ a : I, weakEquivalences PointedCGWH.{u, v} ((evaluation a).map f) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq]
  exact EvaluationTransfer.evaluationProperty_iff _ _ f

/-- The SAME native projective model is left proper on arbitrary original sources and targets. -/
theorem originalNativeLevelLeftProper
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b)) :
    IsLeftProper (EnrichedFunctorCat PointedCGWH.{u, v} I) := by
  exact HomotopicalAlgebra.EnrichedProjective.isLeftProper_of_isCofibrant_homs
    (Native.Data.generationData (A := I) (B := B))
    PointedCGWH.realizedBoundaryInclusions.{u, v}
    (Native.Data.generationData_I (A := I) (B := B))
    originalPointedI_le_cofibrations Native.weakEquivalences_eq hHom

/-- Actual original native pushouts along native Cof preserve the SAME original level weak map. -/
theorem originalNativePushout_levelWeak
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {A C X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)}
    (i : A ⟶ C) (f : A ⟶ X) (f' : C ⟶ Y) (j : X ⟶ Y)
    (sq : IsPushout i f f' j)
    (hi : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f' := by
  let _ : IsLeftProper (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    originalNativeLevelLeftProper hHom
  let _ : Cofibration i := (HomotopicalAlgebra.cofibration_iff i).mpr hi
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff f).mpr hf
  exact (HomotopicalAlgebra.weakEquivalence_iff f').mp
    (IsLeftProper.weakEquivalence_of_isPushout sq)

/-- EVERY original native level-TC map is an actual pointed TC at every full evaluation. -/
theorem originalNativeTrivialCofibration_component_trivialCofibration
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (f : X ⟶ Y)
    (hf : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) f)
    (a : I) :
    trivialCofibrations PointedCGWH.{u, v} ((evaluation a).map f) :=
  ⟨originalNativeCofibration_component_cofibration hHom f hf.1 a,
    (originalNativeLevelWeak_iff_evaluation f).mp hf.2 a⟩

/-- The SAME original I injection retains actual base cofibrations at ALL source-index values. -/
theorem originalIInjection_component_cofibration
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    cofibrations PointedCGWH.{u, v}
      ((evaluation a).map
        (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData.i.app F)) :=
  originalNativeCofibration_component_cofibration hHom _
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData.hi F) a

/-- The SAME original J injection retains actual base TC maps at ALL source-index values. -/
theorem originalJInjection_component_trivialCofibration
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) :
    trivialCofibrations PointedCGWH.{u, v}
      ((evaluation a).map
        (HomotopicalAlgebra.EnrichedProjective.Native.fibrantFactorizationData.i.app F)) :=
  originalNativeTrivialCofibration_component_trivialCofibration hHom _
    (HomotopicalAlgebra.EnrichedProjective.Native.fibrantFactorizationData.hi F) a


end HomotopicalAlgebra.EnrichedProjective.Native.IndexCofibrantProperness
