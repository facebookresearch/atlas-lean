/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeSelectedUnitTransport

/-!
# The original native symmetric selected-unit mate

The complete free source, contraction, curry and comparison are retained before
identifying their mate with the original carrier unit and scalar/index unit.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj ExternalProduct


namespace NativeOmegaRecovery.NativeSelectedUnitTransport.SourceValueTools

/-- The entire original comparison value is retained when its complete
source functor equality is eliminated before any component is selected. -/
theorem rebaseComparison_heq
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F F' K : C ⥤ D} (e : F ≅ K) (h : F = F') : HEq (rebaseComparison e h) e := by
  cases h
  apply heq_of_eq
  apply Iso.ext
  change (𝟙 _ ≫ e.hom) = e.hom
  exact Category.id_comp e.hom

end NativeOmegaRecovery.NativeSelectedUnitTransport.SourceValueTools

namespace NativeOmegaRecovery.NativeSelectedUnitTransport.WholeMateTools

/-- The complete source, adjunct and comparison equalities are eliminated
before either actual whole mate is projected to any original module. -/
theorem mate_eq_of_whole_data
    {C : Type uC} [Category.{vC} C] {F F' K : C ⥤ C}
    (hF : F = F') (c : 𝟭 C ⟶ F) (c' : 𝟭 C ⟶ F') (hc : HEq c c')
    (e : F ≅ K) (e' : F' ≅ K) (he : HEq e e') : c ≫ e.hom = c' ≫ e'.hom := by
  cases hF
  cases hc
  cases he
  rfl

end NativeOmegaRecovery.NativeSelectedUnitTransport.WholeMateTools

namespace NativeOmegaRecovery.NativeSelectedUnitTransport.Native
universe u v
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

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

open NativeSymmetricFreeFunction NativeSymmetricSourceMatch
private abbrev FreeZeroModule := NativeSymmetricFreeSource.freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v})
private abbrev FreeZero := NativeSymmetricFreeSource.nativeFree.{u, v} (𝟙_ I) (𝟙_ V.{u, v})


/-- The canonical comparison keeps the complete original module comparison
value under both genuine whole source equalities. -/
theorem canonicalModuleComparison_heq_original :
    HEq canonicalModuleComparison.{u, v} (moduleComparisonNat.{u, v} (𝟙_ I) (𝟙_ V.{u, v})) :=
  (SourceValueTools.rebaseComparison_heq originalModuleComparison.{u, v}
    originalHom_eq_canonical.{u, v}).trans
      (SourceValueTools.rebaseComparison_heq
        (moduleComparisonNat.{u, v} (𝟙_ I) (𝟙_ V.{u, v})) actualModuleSource_eq_originalHom.{u, v})

/-- The entire original module comparison retains the exact original pair,
target-sequence and target-action constructor before any projection. -/
theorem moduleComparison_initializer :
    HEq (moduleComparisonNat.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
      (FullFreeFunctionTargetNaturality.comparison (I := I) (V := V.{u, v}) A.{u, v}
        (𝟙_ I) (𝟙_ V.{u, v}) (targetModuleFunctor.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
        (targetSequenceNatIso.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
        (native_target_pair_square.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))) := HEq.rfl

/-- The same complete canonical comparison preserves that unchanged original
constructor value through both actual free-source equality casts. -/
theorem canonicalModuleComparison_initializer :
    HEq canonicalModuleComparison.{u, v}
      (FullFreeFunctionTargetNaturality.comparison (I := I) (V := V.{u, v}) A.{u, v}
        (𝟙_ I) (𝟙_ V.{u, v}) (targetModuleFunctor.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
        (targetSequenceNatIso.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
        (native_target_pair_square.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))) :=
  canonicalModuleComparison_heq_original.{u, v}.trans moduleComparison_initializer.{u, v}

end NativeOmegaRecovery.NativeSelectedUnitTransport.Native

namespace NativeOmegaRecovery.NativeSelectedUnitTransport.Day
universe uI vI uV vV
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
  [HasEqualizers (DayFunctor I V)] [HasCoequalizers (DayFunctor I V)]
  (A : CommMon (DayFunctor I V))

private abbrev ZeroDiagram : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V (𝟙_ I)).obj (𝟙_ V))


/-- The actual complete canonical contraction mate keeps the original target
sequence component after its genuine scalar/index unit pair. -/
theorem canonical_zero_mate_component
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor (𝟙_ I) (𝟙_ V) ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A (𝟙_ I) (𝟙_ V) N a n ≫
          (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    (((SelectedUnitTensorCompatibility.contractionCurry A ZeroDiagram
        FreeFunctionSourceEvaluation.originalZeroDiagramUnit).app N ≫
      (FullFreeFunctionTargetNaturality.comparison A (𝟙_ I) (𝟙_ V) K t hPair).hom.app N).hom).natTrans.app n =
      (N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))) ≫
          (t.app N).hom.natTrans.app n := by
  let c := (SelectedUnitTensorCompatibility.contractionCurry A ZeroDiagram
    FreeFunctionSourceEvaluation.originalZeroDiagramUnit).app N
  let e := FullFreeFunctionTargetNaturality.comparison A (𝟙_ I) (𝟙_ V) K t hPair
  let p := (FullFreeFunctionPair.comparison A (𝟙_ I) (𝟙_ V) N).hom
  let z := (t.app N).hom
  have he : (e.hom.app N).hom = p ≫ z :=
    FullFreeFunctionTargetNaturality.hom_app_hom A (𝟙_ I) (𝟙_ V) K t hPair N
  have h₀ := congrArg (fun f => (c.hom ≫ f).natTrans.app n) he
  have h₁ := congrArg (fun f => f.natTrans.app n) (Category.assoc c.hom p z).symm
  have hPairUnit := canonical_zero_contraction_pair A N n
  change (c.hom ≫ (e.hom.app N).hom).natTrans.app n = _
  exact h₀.trans (h₁.trans (congrArg (fun f => f ≫ z.natTrans.app n) hPairUnit))


/-- The same full source data keep the original natural-transformation
composition before any target module or output coordinate is selected. -/
theorem canonical_zero_whole_mate_component
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor (𝟙_ I) (𝟙_ V) ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A (𝟙_ I) (𝟙_ V) N a n ≫
          (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    (((SelectedUnitTensorCompatibility.contractionCurry A ZeroDiagram
        FreeFunctionSourceEvaluation.originalZeroDiagramUnit ≫
      (FullFreeFunctionTargetNaturality.comparison A (𝟙_ I) (𝟙_ V) K t hPair).hom).app N).hom).natTrans.app n =
      (N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))) ≫
          (t.app N).hom.natTrans.app n := by
  exact canonical_zero_mate_component A K t hPair N n


/-- The complete original source, curry and comparison values are identified
before the full mate is compared using the genuine scalar/index unit data. -/
theorem full_zero_mate_eq_of_original_values
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor (𝟙_ I) (𝟙_ V) ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A (𝟙_ I) (𝟙_ V) N a n ≫
          (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    {F : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X}
    (hF : F = Mod.internalHom A ((Mod.free A.X).obj ZeroDiagram))
    (c : 𝟭 (Mod (DayFunctor I V) A.X) ⟶ F)
    (hc : HEq c (SelectedUnitTensorCompatibility.contractionCurry A ZeroDiagram
      FreeFunctionSourceEvaluation.originalZeroDiagramUnit))
    (e : F ≅ K)
    (he : HEq e (FullFreeFunctionTargetNaturality.comparison A (𝟙_ I) (𝟙_ V) K t hPair))
    (U : 𝟭 (Mod (DayFunctor I V) A.X) ⟶ K)
    (hUnit : ∀ N n,
      (U.app N).hom.natTrans.app n =
        (N.X.functor.map (ρ_ n).inv ≫
          MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))) ≫
            (t.hom.app N).natTrans.app n) :
    c ≫ e.hom = U := by
  cases hF
  cases hc
  cases he
  apply NatTrans.ext
  funext N
  apply Mod.hom_ext
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext n
  exact (canonical_zero_whole_mate_component A K t hPair N n).trans (hUnit N n).symm

end NativeOmegaRecovery.NativeSelectedUnitTransport.Day


namespace NativeOmegaRecovery.NativeSelectedUnitTransport.Native
universe u v
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction NativeSymmetricFreeSource

private abbrev Modules := NativeSymmetricFreeFunction.OriginalModule.{u, v}

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

/-- The whole canonical comparison is the unchanged original constructor;
its complete source casts are eliminated before any module is selected. -/
theorem canonicalModuleComparison_eq_initializer :
    canonicalModuleComparison.{u, v} =
      FullFreeFunctionTargetNaturality.comparison (I := I) (V := V.{u, v}) A.{u, v}
        (𝟙_ I) (𝟙_ V.{u, v}) (targetModuleFunctor.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
        (targetSequenceNatIso.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
        (native_target_pair_square.{u, v} (𝟙_ I) (𝟙_ V.{u, v})) :=
  eq_of_heq canonicalModuleComparison_initializer.{u, v}

/-- The whole original carrier-unit mate retains the original unit
identity and the actual scalar/index inverse at every unchanged module level. -/
theorem originalCarrierUnitMate_component (N : Modules.{u, v}) (n : I) :
    (originalCarrierUnitMate.{u, v}.app N).hom.natTrans.app n =
      N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I))) := by
  let p := E.{u, v}.unitIso.hom.app N
  let q := E.{u, v}.inverse.map (zeroScalarIndexUnit.{u, v}.inv.app (E.{u, v}.functor.obj N))
  have hp := moduleOperatorEquivalence_unit_component N n
  have hq := NativeSymmetricSelectedUnit.inverse_zeroScalarIndexUnit_component N n
  change (p ≫ q).hom.natTrans.app n = _
  change p.hom.natTrans.app n ≫ q.hom.natTrans.app n = _
  exact (congrArg₂ (fun f g => f ≫ g) hp hq).trans (Category.id_comp _)

/-- The original carrier-unit prefix retains its genuine original target
sequence map before it is used in the complete source mate. -/
theorem originalCarrierUnitMate_target_component (N : Modules.{u, v}) (n : I) :
    (originalCarrierUnitMate.{u, v}.app N).hom.natTrans.app n =
      (N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))) ≫
          ((targetSequenceNatIso.{u, v} (𝟙_ I) (𝟙_ V.{u, v})).hom.app N).natTrans.app n := by
  have hu := originalCarrierUnitMate_component N n
  have ht := targetSequenceNatIso_zero_hom_component N n
  exact hu.trans ((Category.comp_id _).symm.trans
    (congrArg (fun f =>
      (N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))) ≫ f) ht.symm))

/-- The actual complete canonical module mate equals the original carrier
unit mate, with the complete source data identified before every projection. -/
theorem canonicalModuleMate_eq_originalCarrierUnitMate :
    canonicalModuleMate.{u, v} = originalCarrierUnitMate.{u, v} :=
  Day.full_zero_mate_eq_of_original_values A.{u, v}
    (targetModuleFunctor.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
    (targetSequenceNatIso.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
    (native_target_pair_square.{u, v} (𝟙_ I) (𝟙_ V.{u, v})) rfl
    canonicalZeroCurry.{u, v} HEq.rfl canonicalModuleComparison.{u, v}
    canonicalModuleComparison_initializer.{u, v} originalCarrierUnitMate.{u, v}
    originalCarrierUnitMate_target_component.{u, v}

/-- Every original module and output is read only after the genuine whole
source mate has been identified with the original carrier-unit mate. -/
theorem canonicalModuleMate_component (N : Modules.{u, v}) (n : I) :
    (canonicalModuleMate.{u, v}.app N).hom.natTrans.app n =
      N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I))) :=
  (congrArg (fun t => (t.app N).hom.natTrans.app n)
    canonicalModuleMate_eq_originalCarrierUnitMate.{u, v}).trans
      (originalCarrierUnitMate_component N n)

/-- The whole original curry and original module comparison satisfy the
actual source equation with the original carrier unit. -/
theorem originalModuleMate_eq_originalCarrierUnitMate :
    originalModuleMate.{u, v} = originalCarrierUnitMate.{u, v} :=
  originalModuleMate_eq_canonical.{u, v}.trans canonicalModuleMate_eq_originalCarrierUnitMate.{u, v}

end NativeOmegaRecovery.NativeSelectedUnitTransport.Native
