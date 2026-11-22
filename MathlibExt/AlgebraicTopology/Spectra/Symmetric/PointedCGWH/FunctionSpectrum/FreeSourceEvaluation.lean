/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceCoefficientBase
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.LambdaAdjunction
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceFactors
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeObjectComparison
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.Naturality
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.InternalHomSource
import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom

/-!
# Evaluated original symmetric free-function source comparisons

These equations expose the existing free-unit and end comparison at every
original output index. Arbitrary genuine native free source arrows retain the
same original module representative and the same two source isomorphisms.
The source mapping-equalizer construction is identified separately; this file
computes the complete original comparison used in that identification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.OriginalSourceInverse
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] (B : CommMon C)
  {D : Type uD} [Category.{vD} D] (E : Mod C B.X ≌ D)
/-- The inverse of the same original complete equality Iso is the original identity. -/
theorem inverse (N : Mod C B.X) (X : D) :
    (eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj B E N)).inv.app X =
      𝟙 ((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj
        (.op N) |>.obj X) := rfl
/-- Whole original source-Iso equality is transported before its inverse is evaluated. -/
theorem inverse_of_eq (N : Mod C B.X)
    (s : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj (.op N) ≅
      E.inverse ⋙ Mod.internalHom B N ⋙ E.functor)
    (hs : s = eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj B E N))
    (X : D) :
    s.inv.app X =
      𝟙 ((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E).obj (.op N) |>.obj X) :=
  (congrArg (fun q => q.inv.app X) hs).trans (inverse B E N X)

private theorem identity_component {W : Type*} [Category W] [MonoidalCategory W]
    [BraidedCategory W] [MonoidalClosed W]
    {J : Type*} [EnrichedCategory W J] (F : EnrichedFunctorCat W J)
    (p : F ⟶ F) (h : p = 𝟙 F) (a : J) :
    component p a = 𝟙 (F.toEnrichedFunctor.obj a) :=
  (congrArg (fun q => component q a) h).trans (component_id F a)

/-- The same original whole source inverse keeps its identity at every enriched output. -/
theorem inverse_component_of_eq
    {W : Type*} [Category W] [MonoidalCategory W]
    [BraidedCategory W] [MonoidalClosed W] {J : Type*} [EnrichedCategory W J]
    (E' : Mod C B.X ≌ EnrichedFunctorCat W J) (N : Mod C B.X)
    (s : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E').obj (.op N) ≅
      E'.inverse ⋙ Mod.internalHom B N ⋙ E'.functor)
    (hs : s = eqToIso
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj B E' N))
    (X : EnrichedFunctorCat W J) (a : J) :
    component (s.inv.app X) a =
      𝟙 ((((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor B E').obj
        (.op N)).obj X).toEnrichedFunctor.obj a) :=
  identity_component _ (s.inv.app X) (inverse_of_eq B E' N s hs X) a
end NativeOmegaRecovery.OriginalSourceInverse

namespace NativeOmegaRecovery.FreeFunctionSourceEvaluation

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)]


private abbrev freeDiagram (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

/-- The exact selected Day end family supplies the unchanged free-diagram end. -/
local instance originalFreeEnd (r : I) (M : V) (G : I ⥤ V) (n : I) :
    HasEnd (NativeOmegaPreparation.OrdinaryFreeEnd.diagram r M (tensorRight n ⋙ G)) := by
  change HasEnd ((dayConvolutionInternalHomDiagramFunctor
    ((evaluationLeftAdjoint V r).obj M)).obj G |>.obj n)
  infer_instance

omit [HasEqualizers (DayFunctor I V)] in
/-- The complete Day source arrow is evaluated at its literal identity-index free adjunct. -/
theorem day_source_projection (s : I) (M : V)
    {F : DayFunctor I V} (f : freeDiagram s M ⟶ F) (G : DayFunctor I V) (n : I) :
    ((MonoidalClosed.pre f).app G).natTrans.app n ≫
      ((NativeOmegaPreparation.DayFreeEnd.comparison s M ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison s M).app G).hom.natTrans.app n =
    end_.π ((dayConvolutionInternalHomDiagramFunctor F.functor).obj
      G.functor |>.obj n) s ≫
      (MonoidalClosed.pre
        (Sigma.ι (fun _ : s ⟶ s => M) (𝟙 s) ≫ f.natTrans.app s)).app
          (G.functor.obj (s ⊗ n)) ≫
      (ihom M).map (G.functor.map (β_ s n).hom) := by
  let T := G.functor.obj (s ⊗ n)
  let Hr := (ihom F).obj G
  let Hs := (ihom (freeDiagram s M)).obj G
  let p : Hr.functor.obj n ⟶ Hs.functor.obj n :=
    ((MonoidalClosed.pre f).app G).natTrans.app n
  let πr : Hr.functor.obj n ⟶ (ihom (F.functor.obj s)).obj T :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor F.functor).obj
      G.functor |>.obj n) s
  let πs : Hs.functor.obj n ⟶ (ihom ((freeDiagram s M).functor.obj s)).obj T :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor (freeDiagram s M).functor).obj
      G.functor |>.obj n) s
  let g : M ⟶ (freeDiagram s M).functor.obj s :=
    Sigma.ι (fun _ : s ⟶ s => M) (𝟙 s)
  let b := (ihom M).map (G.functor.map (β_ s n).hom)
  have hp : p ≫ πs = πr ≫ (MonoidalClosed.pre (f.natTrans.app s)).app T :=
    DayFunctor.internalHomPre f G n s
  have hpre := congrArg
    (fun z : ihom (F.functor.obj s) ⟶ ihom M => z.app T)
    (MonoidalClosed.pre_map g (f.natTrans.app s))
  simp only [NatTrans.comp_app] at hpre
  change p ≫ ((πs ≫ (MonoidalClosed.pre g).app T) ≫ b) =
    πr ≫ (MonoidalClosed.pre (g ≫ f.natTrans.app s)).app T ≫ b
  simp only [Category.assoc]
  rw [← Category.assoc p πs, hp, Category.assoc, hpre]
  simp only [Category.assoc]



section Modules
variable [HasCoequalizers (DayFunctor I V)] (A : CommMon (DayFunctor I V))
/-- The original monoidal structure on complete commutative-coefficient modules. -/
local instance originalModuleMonoidal : MonoidalCategory (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalCategory A
/-- The original closed structure for that same complete module monoidal record. -/
local instance originalModuleClosed : MonoidalClosed (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalClosed A
attribute [local irreducible] Mod.internalHom

/-- Every entire free-module source arrow keeps the original equalizer inclusion,
Day end projection, identity-index free adjunct and final original block braiding. -/
theorem module_source_projection (r s : I) (M M' : V)
    (f : (Mod.free A.X).obj (freeDiagram s M') ⟶
      (Mod.free A.X).obj (freeDiagram r M))
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    ((MonoidalClosed.pre f).app N).hom.natTrans.app n ≫
      (FullFreeFunctionPair.comparison A s M' N).hom.natTrans.app n =
    (Mod.internalHomι A ((Mod.free A.X).obj (freeDiagram r M)) N).natTrans.app n ≫
      end_.π ((dayConvolutionInternalHomDiagramFunctor
        ((Mod.free A.X).obj (freeDiagram r M)).X.functor).obj N.X.functor |>.obj n) s ≫
      (MonoidalClosed.pre
        (Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s) ≫
          ((Mod.freeForgetAdjunction A.X).unit.app (freeDiagram s M')).natTrans.app s ≫
          f.hom.natTrans.app s)).app (N.X.functor.obj (s ⊗ n)) ≫
      (ihom M').map (N.X.functor.map (β_ s n).hom) := by
  let F := (Mod.free A.X).obj (freeDiagram r M)
  let g : freeDiagram s M' ⟶ F.X :=
    (Mod.freeForgetAdjunction A.X).unit.app (freeDiagram s M') ≫ f.hom
  let p := ((MonoidalClosed.pre f).app N).hom.natTrans.app n
  let u := (Mod.FreeInternalHom.forward A (freeDiagram s M') N).natTrans.app n
  let j := (Mod.internalHomι A F N).natTrans.app n
  let q := ((MonoidalClosed.pre g).app N.X).natTrans.app n
  let d := ((NativeOmegaPreparation.DayFreeEnd.comparison s M' ≪≫
    NativeOmegaPreparation.DayIndexOrder.comparison s M').app N.X).hom.natTrans.app n
  have hm := Mod.FreeInternalHom.forward_precompose A
    (P := freeDiagram r M) (P' := freeDiagram s M') f N
  have hmp := congrArg (fun z => z.natTrans.app n) hm
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at hmp
  have hd := day_source_projection s M' g N.X n
  change p ≫ (u ≫ d) = _
  change p ≫ u = j ≫ q at hmp
  calc
    p ≫ (u ≫ d) = (p ≫ u) ≫ d := (Category.assoc p u d).symm
    _ = (j ≫ q) ≫ d := congrArg (fun z => z ≫ d) hmp
    _ = j ≫ (q ≫ d) := Category.assoc j q d
    _ = j ≫ (end_.π ((dayConvolutionInternalHomDiagramFunctor F.X.functor).obj
          N.X.functor |>.obj n) s ≫
        (MonoidalClosed.pre (Sigma.ι (fun _ : s ⟶ s => M') (𝟙 s) ≫
          g.natTrans.app s)).app (N.X.functor.obj (s ⊗ n)) ≫
        (ihom M').map (N.X.functor.map (β_ s n).hom)) := congrArg (fun z => j ≫ z) hd
    _ = _ := by
      dsimp only [g, j, F]
      simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]

end Modules
end NativeOmegaRecovery.FreeFunctionSourceEvaluation

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

open PointedCGWH.SymmetricModulePresentation

/- The complete-map boundaries share the existing chosen internal-Hom objects before
projecting to levels. Local opacity affects elaboration only. -/
attribute [local irreducible] Mod.internalHom

/-- The natural comparison uses the same entire original map as the object comparison. -/
theorem moduleComparisonNat_hom_whole (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) :
    ((moduleComparisonNat r M).hom.app N).hom = (moduleIso r M N).hom.hom := rfl

/-- The target-natural original module comparison retains its original beta at every level. -/
theorem moduleComparisonNat_hom_beta (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v}) (n : I) :
    ((moduleComparisonNat r M).hom.app N).hom.natTrans.app n = forwardLevel r M N n := by
  have hp := congrArg (fun z => z.natTrans.app n) (moduleComparisonNat_hom_whole r M N)
  exact hp.trans (moduleIso_hom_beta r M N n)


/-- The complete carrier comparison is the unchanged original object comparison. -/
theorem moduleOperatorComparison_hom_whole (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) :
    (moduleOperatorComparison r M).hom.app N = (objectIso r M N).hom := rfl

/-- The complete original carrier counit keeps the same beta component. -/
theorem moduleOperatorComparison_hom_beta (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) (n : I) :
    component ((moduleOperatorComparison r M).hom.app N)
        (PointedCGWH.symmetricOperatorObj.{u, v} n) = forwardLevel r M N n := by
  have hp := congrArg (fun z => component z (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (moduleOperatorComparison_hom_whole r M N)
  exact hp.trans (objectIso_hom_beta r M N n)

/-- Every component of the original shifted-cotensor carrier recovery is the identity. -/
theorem shiftedCotensorRecovery_component (r : I) (M : V.{u, v}) (E : Carrier.{u, v}) (n : I) :
    component ((PointedCGWH.SymmetricShift.functor r ⋙ cotensor M).map
      (operatorRecoveryNatIso.hom.app E)) (PointedCGWH.symmetricOperatorObj.{u, v} n) = 𝟙 _ := by
  have hC := cotensorMap_component M
    ((PointedCGWH.SymmetricShift.functor r).map (operatorRecoveryNatIso.hom.app E))
    (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have hS := PointedCGWH.SymmetricShift.functor_map_component r n
    (operatorRecoveryNatIso.hom.app E)
  have hR := operatorRecoveryIso_hom_component E
    (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))
  exact hC.trans ((congrArg (fun z => (ihom M).map z) (hS.trans hR)).trans
    ((ihom M).map_id _))


/-- The original inverse carrier comparison is the complete inverse object comparison. -/
theorem moduleOperatorComparison_inv_whole (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) :
    (moduleOperatorComparison r M).inv.app N = (objectIso r M N).inv := rfl

/-- The original inverse carrier comparison retains every inverse end-extension component. -/
theorem moduleOperatorComparison_inv_beta (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) (n : I) :
    component ((moduleOperatorComparison r M).inv.app N)
        (PointedCGWH.symmetricOperatorObj.{u, v} n) = inverseLevel r M N n := by
  have hp := congrArg (fun z => component z (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (moduleOperatorComparison_inv_whole r M N)
  exact hp.trans (objectIso_inv_beta r M N n)

/-- The inverse carrier recovery also retains the identity at every shifted cotensor level. -/
theorem shiftedCotensorRecovery_inv_component (r : I) (M : V.{u, v})
    (E : Carrier.{u, v}) (n : I) :
    component ((PointedCGWH.SymmetricShift.functor r ⋙ cotensor M).map
      (operatorRecoveryNatIso.inv.app E)) (PointedCGWH.symmetricOperatorObj.{u, v} n) = 𝟙 _ := by
  have hC := cotensorMap_component M
    ((PointedCGWH.SymmetricShift.functor r).map (operatorRecoveryNatIso.inv.app E))
    (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have hS := PointedCGWH.SymmetricShift.functor_map_component r n
    (operatorRecoveryNatIso.inv.app E)
  have hR := operatorRecoveryIso_inv_component E
    (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))
  exact hC.trans ((congrArg (fun z => (ihom M).map z) (hS.trans hR)).trans
    ((ihom M).map_id _))


end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.EvaluatedComparisonMaps

universe uC vC uD vD

/-- Pointwise equal components retain the entire original natural transformation data. -/
def withComponents {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F G : C ⥤ D} (τ : F ⟶ G) (f : ∀ X, F.obj X ⟶ G.obj X)
    (h : ∀ X, τ.app X = f X) : F ⟶ G where
  app := f
  naturality {X Y} g := by
    rw [← h X, ← h Y]
    exact τ.naturality g

/-- The original full map, its source/target functors and every component are unchanged. -/
theorem withComponents_eq {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {F G : C ⥤ D}
    (τ : F ⟶ G) (f : ∀ X, F.obj X ⟶ G.obj X) (h : ∀ X, τ.app X = f X) :
    withComponents τ f h = τ := by
  apply NatTrans.ext
  funext X
  exact (h X).symm

private theorem whiskerRight_app_of_eq {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {E : Type*} [Category E]
    {F G : C ⥤ D} (τ : F ⟶ G) (K : D ⥤ E) (X : C)
    (f : K.obj (F.obj X) ⟶ K.obj (G.obj X)) (h : K.map (τ.app X) = f) :
    (Functor.whiskerRight τ K).app X = f := h

end NativeOmegaRecovery.EvaluatedComparisonMaps

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

open PointedCGWH.SymmetricModulePresentation
attribute [local irreducible] Mod.internalHom

/-- Every original raw free-unit/end component supplies the full evaluated module map. -/
def moduleForwardLevelNat (r : I) (M : V.{u, v}) (n : I) :
    type_of% (EvaluatedComparisonMaps.withComponents
      (Functor.whiskerRight (moduleOperatorComparison r M).hom
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)))
      (fun N => forwardLevel r M N n)
      (fun N => moduleOperatorComparison_hom_beta r M N n)) :=
  Functor.whiskerRight (moduleOperatorComparison r M).hom
    (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))

/-- The raw free-unit/end transformation is equal to the whole original evaluated map. -/
theorem moduleOperatorComparison_hom_evaluation_nat (r : I) (M : V.{u, v}) (n : I) :
    Functor.whiskerRight (moduleOperatorComparison r M).hom
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)) =
      moduleForwardLevelNat r M n :=
  rfl

/-- The raw transformation retains the literal original free-unit/end component on every module. -/
theorem moduleForwardLevelNat_app (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) (n : I) :
    (moduleForwardLevelNat r M n).app N = forwardLevel r M N n :=
  EvaluatedComparisonMaps.whiskerRight_app_of_eq (moduleOperatorComparison r M).hom
    (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)) N (forwardLevel r M N n)
    (moduleOperatorComparison_hom_beta r M N n)

end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.EvaluatedComparisonMaps

universe uB vB uC vC uD vD uE vE

/-- The two actual evaluated maps retain the original isomorphism's forward inverse law. -/
theorem forward_inverse {C : Type uC} [Category.{vC} C]
    {F G : C} (e : F ≅ G) (f : F ⟶ G) (g : G ⟶ F)
    (hf : e.hom = f) (hg : e.inv = g) : f ≫ g = 𝟙 F := by
  rw [← hf, ← hg]
  exact e.hom_inv_id

/-- The same entire maps retain the original isomorphism's inverse forward law. -/
theorem inverse_forward {C : Type uC} [Category.{vC} C]
    {F G : C} (e : F ≅ G) (f : F ⟶ G) (g : G ⟶ F)
    (hf : e.hom = f) (hg : e.inv = g) : g ≫ f = 𝟙 G := by
  rw [← hf, ← hg]
  exact e.inv_hom_id

/-- Evaluation and source whiskering retain the actual functor associators. -/
theorem isoWhiskerLeft_hom_evaluation
    {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
    (F : B ⥤ C) {G H : C ⥤ D} (e : G ≅ H) (K : D ⥤ E)
    (τ : G ⋙ K ⟶ H ⋙ K) (h : Functor.whiskerRight e.hom K = τ) :
    Functor.whiskerRight (Functor.isoWhiskerLeft F e).hom K =
      (Functor.associator F G K).hom ≫ Functor.whiskerLeft F τ ≫
        (Functor.associator F H K).inv := by
  rw [Functor.isoWhiskerLeft_hom, Functor.whiskerRight_left, h]

/-- Inverse evaluation keeps the same source whiskering and genuine associators. -/
theorem isoWhiskerLeft_inv_evaluation
    {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
    (F : B ⥤ C) {G H : C ⥤ D} (e : G ≅ H) (K : D ⥤ E)
    (τ : H ⋙ K ⟶ G ⋙ K) (h : Functor.whiskerRight e.inv K = τ) :
    Functor.whiskerRight (Functor.isoWhiskerLeft F e).inv K =
      (Functor.associator F H K).hom ≫ Functor.whiskerLeft F τ ≫
        (Functor.associator F G K).inv := by
  rw [Functor.isoWhiskerLeft_inv, Functor.whiskerRight_left, h]

end NativeOmegaRecovery.EvaluatedComparisonMaps

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

open PointedCGWH.SymmetricModulePresentation
attribute [local irreducible] Mod.internalHom

/-- Every original inverse end extension supplies the full evaluated inverse module map. -/
def moduleInverseLevelNat (r : I) (M : V.{u, v}) (n : I) :
    type_of% (EvaluatedComparisonMaps.withComponents
      (Functor.whiskerRight (moduleOperatorComparison r M).inv
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)))
      (fun N => inverseLevel r M N n)
      (fun N => moduleOperatorComparison_inv_beta r M N n)) :=
  Functor.whiskerRight (moduleOperatorComparison r M).inv
    (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))

/-- The entire evaluated inverse map retains the original module comparison. -/
theorem moduleOperatorComparison_inv_evaluation_nat (r : I) (M : V.{u, v}) (n : I) :
    Functor.whiskerRight (moduleOperatorComparison r M).inv
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)) =
      moduleInverseLevelNat r M n :=
  rfl

/-- The inverse transformation reads back the original component on every original module. -/
theorem moduleInverseLevelNat_app (r : I) (M : V.{u, v})
    (N : OriginalModule.{u, v}) (n : I) :
    (moduleInverseLevelNat r M n).app N = inverseLevel r M N n :=
  EvaluatedComparisonMaps.whiskerRight_app_of_eq (moduleOperatorComparison r M).inv
    (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)) N (inverseLevel r M N n)
    (moduleOperatorComparison_inv_beta r M N n)

/-- The complete raw forward and inverse transformations compose to the original source identity. -/
theorem moduleForwardInverseLevelNat (r : I) (M : V.{u, v}) (n : I) :
    moduleForwardLevelNat r M n ≫ moduleInverseLevelNat r M n = 𝟙 _ :=
  EvaluatedComparisonMaps.forward_inverse
    (Functor.isoWhiskerRight (moduleOperatorComparison r M)
      (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)))
    (moduleForwardLevelNat r M n) (moduleInverseLevelNat r M n)
    (moduleOperatorComparison_hom_evaluation_nat r M n)
    (moduleOperatorComparison_inv_evaluation_nat r M n)

/-- The complete raw inverse and forward transformations compose to the original target identity. -/
theorem moduleInverseForwardLevelNat (r : I) (M : V.{u, v}) (n : I) :
    moduleInverseLevelNat r M n ≫ moduleForwardLevelNat r M n = 𝟙 _ :=
  EvaluatedComparisonMaps.inverse_forward
    (Functor.isoWhiskerRight (moduleOperatorComparison r M)
      (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)))
    (moduleForwardLevelNat r M n) (moduleInverseLevelNat r M n)
    (moduleOperatorComparison_hom_evaluation_nat r M n)
    (moduleOperatorComparison_inv_evaluation_nat r M n)

attribute [local irreducible] operatorToModule

/-- The original native module factor evaluates through the genuine source associators. -/
theorem comparisonModuleFactor_hom_evaluation_assoc (r : I) (M : V.{u, v}) (n : I) :
    Functor.whiskerRight (comparisonModuleFactor r M).hom
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)) =
      (Functor.associator operatorToModule _
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))).hom ≫
      Functor.whiskerLeft operatorToModule (moduleForwardLevelNat r M n) ≫
      (Functor.associator operatorToModule _
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))).inv :=
  EvaluatedComparisonMaps.isoWhiskerLeft_hom_evaluation
    operatorToModule (moduleOperatorComparison r M)
    (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (moduleForwardLevelNat r M n)
    (moduleOperatorComparison_hom_evaluation_nat r M n)

/-- The original native inverse factor retains its full inverse map and source associators. -/
theorem comparisonModuleFactor_inv_evaluation_assoc (r : I) (M : V.{u, v}) (n : I) :
    Functor.whiskerRight (comparisonModuleFactor r M).inv
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)) =
      (Functor.associator operatorToModule _
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))).hom ≫
      Functor.whiskerLeft operatorToModule (moduleInverseLevelNat r M n) ≫
      (Functor.associator operatorToModule _
        (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))).inv :=
  EvaluatedComparisonMaps.isoWhiskerLeft_inv_evaluation
    operatorToModule (moduleOperatorComparison r M)
    (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (moduleInverseLevelNat r M n)
    (moduleOperatorComparison_inv_evaluation_nat r M n)

end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.EvaluatedComparisonMaps

universe uC vC uD vD

/-- The component constructor exposes its actual component without unfolding the old map. -/
theorem withComponents_app {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {F G : C ⥤ D}
    (τ : F ⟶ G) (f : ∀ X, F.obj X ⟶ G.obj X) (h : ∀ X, τ.app X = f X) (X : C) :
    (withComponents τ f h).app X = f X := rfl

/-- The forward component of the actual composite retains both original maps. -/
theorem trans_hom_app {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {F G H : C ⥤ D}
    (e : F ≅ G) (f : G ≅ H) (X : C) :
    (e ≪≫ f).hom.app X = e.hom.app X ≫ f.hom.app X := by
  simp only [Iso.trans_hom, NatTrans.comp_app]

/-- The inverse component retains the reverse order of both original maps. -/
theorem trans_inv_app {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {F G H : C ⥤ D}
    (e : F ≅ G) (f : G ≅ H) (X : C) :
    (e ≪≫ f).inv.app X = f.inv.app X ≫ e.inv.app X := by
  simp only [Iso.trans_inv, NatTrans.comp_app]

/-- Every original inverse factor is evaluated in its genuine reversed order. -/
theorem triple_inv_app {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {F G H K : C ⥤ D}
    (e : F ≅ G) (f : G ≅ H) (g : H ≅ K) (X : C) :
    (e ≪≫ f ≪≫ g).inv.app X = g.inv.app X ≫ f.inv.app X ≫ e.inv.app X := by
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]

/-- The entire inverse composite retains the original reversed factor order. -/
theorem triple_inv {C : Type uC} [Category.{vC} C] {F G H K : C}
    (e : F ≅ G) (f : G ≅ H) (g : H ≅ K) :
    (e ≪≫ f ≪≫ g).inv = g.inv ≫ f.inv ≫ e.inv := by
  simp only [Iso.trans_inv, Category.assoc]

end NativeOmegaRecovery.EvaluatedComparisonMaps

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

open PointedCGWH.SymmetricModulePresentation
attribute [local irreducible] Mod.internalHom

/-- The original inverse source transport is the identity on its complete source value. -/
theorem comparisonSourceTransport_inv_whole (r : I) (M : V.{u, v}) (E : Carrier.{u, v}) :
    type_of% (OriginalSourceInverse.inverse_of_eq A.{u, v} moduleOperatorEquivalence.{u, v}
      ((Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} r).obj M) (comparisonSourceTransport r M)
      (comparisonSourceTransport_eq_old r M) E) :=
  OriginalSourceInverse.inverse_of_eq A.{u, v} moduleOperatorEquivalence.{u, v}
      ((Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} r).obj M) (comparisonSourceTransport r M)
      (comparisonSourceTransport_eq_old r M) E

/-- Its inverse component retains the same original identity at every output index. -/
theorem comparisonSourceTransport_inv_component (r : I) (M : V.{u, v})
    (E : Carrier.{u, v}) (n : I) :
    type_of% (OriginalSourceInverse.inverse_component_of_eq A.{u, v}
      moduleOperatorEquivalence.{u, v}
      ((Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} r).obj M)
      (comparisonSourceTransport r M) (comparisonSourceTransport_eq_old r M)
      E (PointedCGWH.symmetricOperatorObj.{u, v} n)) :=
  OriginalSourceInverse.inverse_component_of_eq A.{u, v} moduleOperatorEquivalence.{u, v}
    ((Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} r).obj M)
    (comparisonSourceTransport r M) (comparisonSourceTransport_eq_old r M)
    E (PointedCGWH.symmetricOperatorObj.{u, v} n)

/-- The entire original recovery factor retains the already proved identity component. -/
theorem comparisonRecoveryFactor_hom_component (r : I) (M : V.{u, v})
    (E : Carrier.{u, v}) (n : I) :
    component ((comparisonRecoveryFactor r M).hom.app E)
      (PointedCGWH.symmetricOperatorObj.{u, v} n) = 𝟙 _ :=
  shiftedCotensorRecovery_component r M E n

/-- The original inverse recovery factor retains that same identity component. -/
theorem comparisonRecoveryFactor_inv_component (r : I) (M : V.{u, v})
    (E : Carrier.{u, v}) (n : I) :
    component ((comparisonRecoveryFactor r M).inv.app E)
      (PointedCGWH.symmetricOperatorObj.{u, v} n) = 𝟙 _ :=
  shiftedCotensorRecovery_inv_component r M E n

/-- The whole original inverse retains all three actual transformations before evaluation. -/
theorem comparison_inv_transport_factors_nat (r : I) (M : V.{u, v}) :
    (comparison r M).inv =
      (comparisonRecoveryFactor r M).inv ≫ (comparisonModuleFactor r M).inv ≫
        (comparisonSourceTransport r M).inv :=
  EvaluatedComparisonMaps.triple_inv (comparisonSourceTransport r M)
    (comparisonModuleFactor r M) (comparisonRecoveryFactor r M)

/-- The actual original inverse comparison retains all three complete factors. -/
theorem comparison_inv_transport_factors (r : I) (M : V.{u, v}) (E : Carrier.{u, v}) :
    (comparison r M).inv.app E =
      (comparisonRecoveryFactor r M).inv.app E ≫
        (comparisonModuleFactor r M).inv.app E ≫
          (comparisonSourceTransport r M).inv.app E :=
  NatTrans.congr_app (comparison_inv_transport_factors_nat r M) E

/-- The complete native forward map retains the literal original source comparison factor. -/
theorem nativeFreeComparison_hom_factors_nat (r : I) (M : V.{u, v}) :
    (nativeFreeComparison r M).hom =
      (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison r M).inv ≫
        (comparison r M).hom := rfl

/-- The complete native inverse retains that same original source recovery factor. -/
theorem nativeFreeComparison_inv_factors_nat (r : I) (M : V.{u, v}) :
    (nativeFreeComparison r M).inv =
      (comparison r M).inv ≫
        (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison r M).hom := rfl

end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

open PointedCGWH.SymmetricModulePresentation
attribute [local irreducible] Mod.internalHom operatorToModule

/-- The actual entire inverse factor is the original inverse module map at its given module. -/
theorem comparisonModuleFactor_inv_app_exact (r : I) (M : V.{u, v})
    (E : Carrier.{u, v}) :
    (comparisonModuleFactor.{u, v} r M).inv.app E =
      (moduleOperatorComparison.{u, v} r M).inv.app (operatorToModule.{u, v}.obj E) := rfl

/-- Evaluating the exact entire forward factor retains the full original raw component. -/
theorem comparisonModuleFactor_hom_levelNat_component (r : I) (M : V.{u, v})
    (E : Carrier.{u, v}) (n : I) :
    component ((comparisonModuleFactor.{u, v} r M).hom.app E)
        (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      (moduleForwardLevelNat.{u, v} r M n).app (operatorToModule.{u, v}.obj E) := by
  have h₁ := congrArg
    (fun f => (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)).map f)
    (comparisonModuleFactor_hom_app_exact.{u, v} r M E)
  have h₂ := NatTrans.congr_app
    (moduleOperatorComparison_hom_evaluation_nat.{u, v} r M n)
    (operatorToModule.{u, v}.obj E)
  exact h₁.trans h₂

/-- The actual entire inverse factor evaluates to the original inverse component at every level. -/
theorem comparisonModuleFactor_inv_levelNat_component (r : I) (M : V.{u, v})
    (E : Carrier.{u, v}) (n : I) :
    component ((comparisonModuleFactor.{u, v} r M).inv.app E)
        (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      (moduleInverseLevelNat.{u, v} r M n).app (operatorToModule.{u, v}.obj E) := by
  have h₁ := congrArg
    (fun f => (evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n)).map f)
    (comparisonModuleFactor_inv_app_exact.{u, v} r M E)
  have h₂ := NatTrans.congr_app
    (moduleOperatorComparison_inv_evaluation_nat.{u, v} r M n)
    (operatorToModule.{u, v}.obj E)
  exact h₁.trans h₂

end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.FreeFunctionCarrierComparison

/-- The same original full comparison is identified before the source square is composed. -/
theorem sourceSquare_comparison_of_whole_eq {D : Type*} [Category D]
    {H H' G G' K : D} (e : H ≅ G) (e' : H' ≅ G')
    (p : G ⟶ G') (q : H ⟶ H') (h : e.hom ≫ p = q ≫ e'.hom)
    (d : H' ≅ K) (c : G' ≅ K) (hc : c = e'.symm ≪≫ d) :
    p ≫ c.hom = e.inv ≫ q ≫ d.hom := by
  cases hc
  change p ≫ (e'.inv ≫ d.hom) = e.inv ≫ q ≫ d.hom
  calc
    p ≫ (e'.inv ≫ d.hom) = (p ≫ e'.inv) ≫ d.hom :=
      (Category.assoc p e'.inv d.hom).symm
    _ = (e.inv ≫ q) ≫ d.hom :=
      congrArg (fun z => z ≫ d.hom) (sourceSquare e e' p q h)
    _ = e.inv ≫ q ≫ d.hom := Category.assoc e.inv q d.hom

end NativeOmegaRecovery.FreeFunctionCarrierComparison

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction


attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

attribute [local irreducible] Mod.internalHom

/-- The actual entire native free comparison retains both original complete isomorphisms. -/
theorem nativeFreeComparison_whole_original (r : I) (M : V.{u, v}) :
    nativeFreeComparison.{u, v} r M =
      (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} r M).symm ≪≫
        comparison.{u, v} r M := rfl

/-- Every original native free source arrow retains the complete original module source square. -/
theorem nativeFreeComparison_precompose_source {r s : I} {M M' : V.{u, v}}
    (f : NativeSymmetricFreeSource.nativeFree.{u, v} s M' ⟶
      NativeSymmetricFreeSource.nativeFree.{u, v} r M) :
    type_of% (FreeFunctionCarrierComparison.sourceSquare_comparison_of_whole_eq
      (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} r M)
      (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} s M')
      (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
      (NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
        (NativeSymmetricFreeSource.sourceArrow.{u, v} f))
      (@NativeSymmetricFreeSource.originalFreeComparison_precompose.{u, v} r s M M' f)
      (comparison.{u, v} s M') (nativeFreeComparison.{u, v} s M')
      (nativeFreeComparison_whole_original s M')) :=
  FreeFunctionCarrierComparison.sourceSquare_comparison_of_whole_eq
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} r M)
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} s M')
    (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
      (NativeSymmetricFreeSource.sourceArrow.{u, v} f))
    (@NativeSymmetricFreeSource.originalFreeComparison_precompose.{u, v} r s M M' f)
    (comparison.{u, v} s M') (nativeFreeComparison.{u, v} s M')
    (nativeFreeComparison_whole_original s M')

end NativeOmegaRecovery.NativeSymmetricFreeFunction

namespace NativeOmegaRecovery.FreeFunctionCarrierComparison

/-- The whole original coaugmentation is composed only after its complete source equation is
  identified. -/
theorem prepend_source_of_whole_eq {D : Type*} [Category D] {W G G' K : D}
    (w : W ⟶ G) (p : G ⟶ G') (c : G' ⟶ K) (r : G ⟶ K) (h : p ≫ c = r)
    (eta : W ⟶ G') (heta : eta = w ≫ p) : eta ≫ c = w ≫ r := by
  cases heta
  exact (Category.assoc w p c).trans (congrArg (fun z => w ≫ z) h)

end NativeOmegaRecovery.FreeFunctionCarrierComparison

namespace NativeOmegaRecovery.NativeSymmetricFreeFunction


attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

attribute [local irreducible] Mod.internalHom

/-- A whole original input source map retains the same complete native/unit/module comparison
  word. -/
theorem nativeFreeComparison_source_word {r s : I} {M M' : V.{u, v}}
    (f : NativeSymmetricFreeSource.nativeFree.{u, v} s M' ⟶
      NativeSymmetricFreeSource.nativeFree.{u, v} r M)
    (W : Carrier.{u, v} ⥤ Carrier.{u, v})
    (w : W ⟶ NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
      (NativeSymmetricFreeSource.nativeFree.{u, v} r M))
    (eta : W ⟶ NativeOmegaPreparation.NativeSymmetricFunction.functor.{u, v}
      (NativeSymmetricFreeSource.nativeFree.{u, v} s M'))
    (heta : eta = w ≫ NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f) :
    type_of% (FreeFunctionCarrierComparison.prepend_source_of_whole_eq w
      (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
      (nativeFreeComparison.{u, v} s M').hom
      ((NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} r M).inv ≫
        NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
          (NativeSymmetricFreeSource.sourceArrow.{u, v} f) ≫ (comparison.{u, v} s M').hom)
      (nativeFreeComparison_precompose_source f) eta heta) :=
  FreeFunctionCarrierComparison.prepend_source_of_whole_eq w
    (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
    (nativeFreeComparison.{u, v} s M').hom
    ((NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} r M).inv ≫
      NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
        (NativeSymmetricFreeSource.sourceArrow.{u, v} f) ≫ (comparison.{u, v} s M').hom)
    (nativeFreeComparison_precompose_source f) eta heta

/-- The literal original unit source coaugmentation retains every full comparison factor. -/
theorem unitSource_full_comparison_word (r : I) :
    type_of% (@nativeFreeComparison_source_word.{u, v} (𝟙_ I) ((𝟙_ I) ⊗ r)
    (𝟙_ V.{u, v}) (PointedCGWH.sphereSequence.{u, v}.functor.obj r)
      (NativeSymmetricLambda.unitStabilization.{u, v} r)
    (𝟭 Carrier.{u, v}) NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}.inv
    (NativeSymmetricLambda.sourceCoaugmentation.{u, v} r)
      (NativeSymmetricLambdaAdjunction.sourceCoaugmentation_original r)) :=
  @nativeFreeComparison_source_word.{u, v} (𝟙_ I) ((𝟙_ I) ⊗ r)
    (𝟙_ V.{u, v}) (PointedCGWH.sphereSequence.{u, v}.functor.obj r)
      (NativeSymmetricLambda.unitStabilization.{u, v} r)
    (𝟭 Carrier.{u, v}) NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}.inv
    (NativeSymmetricLambda.sourceCoaugmentation.{u, v} r)
      (NativeSymmetricLambdaAdjunction.sourceCoaugmentation_original r)

/-- The literal original first source coaugmentation retains every full comparison factor. -/
theorem firstSource_full_comparison_word :
    type_of% (@nativeFreeComparison_source_word.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex
    (𝟙_ V.{u, v}) PointedCGWH.sphereOne.{u, v} NativeSymmetricLambda.firstSource.{u, v}
    (𝟭 Carrier.{u, v}) NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}.inv
    NativeSymmetricLambda.coaugmentation.{u, v} NativeSymmetricLambda.coaugmentation_original.{u,
      v}) :=
  @nativeFreeComparison_source_word.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex
    (𝟙_ V.{u, v}) PointedCGWH.sphereOne.{u, v} NativeSymmetricLambda.firstSource.{u, v}
    (𝟭 Carrier.{u, v}) NativeSymmetricFreeFunction.nativeUnitComparison.{u, v}.inv
    NativeSymmetricLambda.coaugmentation.{u, v} NativeSymmetricLambda.coaugmentation_original.{u,
      v}

end NativeOmegaRecovery.NativeSymmetricFreeFunction
