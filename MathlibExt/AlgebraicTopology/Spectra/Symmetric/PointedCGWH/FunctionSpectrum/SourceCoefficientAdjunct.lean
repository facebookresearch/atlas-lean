/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.SourceCoefficientAdjunct
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeSourceCoefficientBase
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Delooping
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Lambda

/-!
# Coefficient adjuncts for free symmetric spectra

Free-evaluation adjunctions are compared across an equivalence between modules
and enriched functors. The resulting formulas describe how a coefficient map
followed by a stabilization arrow is carried to a module arrow and its adjunct.
For symmetric spectra, these formulas identify the source of the first
coaugmentation with the sphere-coefficient map followed by module stabilization.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

namespace NativeOmegaRecovery.ModuleFreeAdjunctTransport
universe uC vC uV vV uJ
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C) {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (E : Mod C A.X ≌ EnrichedFunctorCat V J)

/-- The original stabilization adjunct preserves the literal scalar, free coend map and unitor. -/
theorem source_point_stabilization (a b : J)
    (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V) (adj : L ⊣ R)
    (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V) (adj' : L' ⊣ R')
    (r' : E.functor ⋙ evaluation b ≅ R')
    (W K : V) (f : W ⟶ K) (D : K ⟶ (a ⟶[V] b)) :
    adj'.homEquiv W (L.obj (𝟙_ V))
        (L'.map f ≫ ModuleFreeSourceTransport.sourceArrow A E
          ((FreeAdjunctionSource.comparison E a L R adj r).app (𝟙_ V))
          ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K)
          (CurrentFree.stabilization
            a b K D)) =
      (f ≫ D ≫ (λ_ (a ⟶[V] b)).inv ≫
        component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app (𝟙_ V)) b) ≫
          r'.hom.app (L.obj (𝟙_ V)) := by
  have h := source_point_postCoefficient_back A E a b L R adj r L' R' adj' r'
    (𝟙_ V) W K f
    (CurrentFree.stabilization
      a b K D)
  have hs := CurrentFree.stabilization_adjunct
    a b K D
  rw [Free.adjunction_homEquiv] at hs
  simpa only [Category.assoc] using h.trans (congrArg (fun q => (f ≫ q ≫
    component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app (𝟙_ V)) b) ≫
      r'.hom.app (L.obj (𝟙_ V))) hs)

end NativeOmegaRecovery.ModuleFreeAdjunctTransport

namespace NativeOmegaRecovery.NativeSymmetricSourceComposite
universe u v
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

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

open NativeSymmetricFreeSource
open PointedCGWH.SymmetricModulePresentation
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

/-- The entire native pre-map retains its unchanged actual module-source initializer. -/
theorem nativePrecompose_heq_initializer {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    HEq (NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v} f)
      (NativeOmegaPreparation.ModuleFunctionTransport.precompose A.{u, v}
        moduleOperatorEquivalence.{u, v} f) := HEq.rfl

/-- The entire original pre-map retains the same given original full source functor. -/
theorem originalPrecompose_heq_map {r s : I} {M N : V.{u, v}}
    (m : freeModule.{u, v} s N ⟶ freeModule.{u, v} r M) :
    HEq (NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
        (n := r) (k := s) (M := M) (N := N) m)
      (NativeOmegaPreparation.SymmetricFunction.sourceFunctor.{u, v}.map m.op) := HEq.rfl

/-- Every scalar map followed by any given native free-source arrow retains the full original
module word. -/
theorem sourceArrow_postCoefficient {r s : I} {M W K : V.{u, v}}
    (f : W ⟶ K) (g : nativeFree.{u, v} s K ⟶ nativeFree.{u, v} r M) :
    sourceArrow.{u, v} (r := r) (s := s) (M := M) (M' := W)
        (Free.coefficientMap (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} s) f ≫ g) =
      (Mod.dayFreeAt S.{u, v} s).map f ≫
        sourceArrow.{u, v} (r := r) (s := s) (M := M) (M' := K) g :=
  FreeAdjunctionCoefficientSource.sourceArrow_postCoefficient A.{u, v}
    moduleOperatorEquivalence.{u, v} (PointedCGWH.symmetricOperatorObj.{u, v} s)
    (Mod.dayFreeAt S.{u, v} s) (NativeOmegaPreparation.SymmetricNativeFree.comparison.{u, v} s)
    (freeIso.{u, v} r M) f g

/-- The given whole source comparison retains the literal scalar/module source word. -/
theorem postCoefficient_precompose_hom {r s : I} {M W K : V.{u, v}}
    (f : W ⟶ K) (g : nativeFree.{u, v} s K ⟶ nativeFree.{u, v} r M) :
    (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} r M).hom ≫
        NativeOmegaPreparation.NativeSymmetricFunction.precompose.{u, v}
          (A := nativeFree.{u, v} s W) (B := nativeFree.{u, v} r M)
          (Free.coefficientMap (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} s) f ≫ g) =
      NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
          (n := r) (k := s) (M := M) (N := W)
          ((Mod.dayFreeAt S.{u, v} s).map f ≫ sourceArrow.{u, v} g) ≫
        (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} s W).hom := by
  have h := originalFreeComparison_precompose.{u, v}
    (r := r) (s := s) (M := M) (M' := W)
    (Free.coefficientMap (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} s) f ≫ g)
  have hArrow := sourceArrow_postCoefficient.{u, v} f g
  exact h.trans (congrArg
    (fun m : freeModule.{u, v} s W ⟶ freeModule.{u, v} r M =>
      NativeOmegaPreparation.SymmetricFunction.precompose.{u, v}
        (n := r) (k := s) (M := M) (N := W) m ≫
        (NativeOmegaPreparation.NativeSymmetricFunction.originalFreeComparison.{u, v} s W).hom)
    hArrow)

/-- The actual full operator comparison keeps its literal original chosen free/evaluation
initializer. -/
theorem operatorComparison_eq_initializer (r : I) :
    NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} r =
      FreeAdjunctionSource.operatorIso moduleOperatorEquivalence.{u, v}
        (PointedCGWH.symmetricOperatorObj.{u, v} r)
        (Mod.dayFreeAt S.{u, v} r) (Mod.dayEvaluation S.{u, v} r)
        (Mod.dayFreeAtEvaluationAdjunction S.{u, v} r)
        (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} r) := rfl

/-- The complete module adjunct is specialized only after the whole actual operator Iso is
identified. -/
theorem postCoefficient_adjunct {r s : I} {M W K : V.{u, v}}
    (f : W ⟶ K) (g : nativeFree.{u, v} s K ⟶ nativeFree.{u, v} r M) :
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} s).homEquiv W (freeModule.{u, v} r M)
        ((Mod.dayFreeAt S.{u, v} s).map f ≫ sourceArrow.{u, v} g) =
      (f ≫ Free.evaluate (PointedCGWH.symmetricOperatorObj.{u, v} s) K (nativeFree.{u, v} r M) g ≫
        component
          ((NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} r).inv.app M)
          (PointedCGWH.symmetricOperatorObj.{u, v} s)) ≫
        (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} s).hom.app
          (freeModule.{u, v} r M) := by
  exact ModuleFreeAdjunctTransport.source_point_postCoefficient_of_operatorIso A.{u, v}
    moduleOperatorEquivalence.{u, v}
    (PointedCGWH.symmetricOperatorObj.{u, v} r) (PointedCGWH.symmetricOperatorObj.{u, v} s)
    (Mod.dayFreeAt S.{u, v} r) (Mod.dayEvaluation S.{u, v} r)
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} r)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} r)
    (Mod.dayFreeAt S.{u, v} s) (Mod.dayEvaluation S.{u, v} s)
    (Mod.dayFreeAtEvaluationAdjunction S.{u, v} s)
    (NativeOmegaPreparation.SymmetricNativeFree.evaluationIso.{u, v} s)
    (NativeOmegaPreparation.SymmetricNativeFree.operatorComparison.{u, v} r)
    (operatorComparison_eq_initializer.{u, v} r) M W K f g

/-- Every literal scalar and all-pair stabilization retains the full original
module source arrow. -/
theorem scalarStabilization_sourceArrow (r a : I) {W : V.{u, v}}
    (f : W ⟶ S.{u, v}.functor.obj a) :
    sourceArrow.{u, v} (r := r) (s := r ⊗ a) (M := 𝟙_ V.{u, v}) (M' := W)
        (Free.coefficientMap (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} (r ⊗ a)) f ≫
          Actual.symmetricStabilization.{u, v} r a) =
      (Mod.dayFreeAt S.{u, v} (r ⊗ a)).map f ≫ moduleStabilization.{u, v} r a :=
  sourceArrow_postCoefficient.{u, v} f (Actual.symmetricStabilization.{u, v} r a)

/-- The actual first coefficient inverse precedes the original unit-index stabilization module
arrow. -/
theorem firstSource_moduleArrow :
    sourceArrow.{u, v} (r := 𝟙_ I) (s := NativeSymmetricDelooping.firstIndex)
        (M := 𝟙_ V.{u, v}) (M' := PointedCGWH.sphereOne.{u, v})
        (Free.coefficientMap (V := V.{u, v})
            (PointedCGWH.symmetricOperatorObj.{u, v} NativeSymmetricDelooping.firstIndex)
            NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ≫
          Actual.symmetricStabilization.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex) =
      (Mod.dayFreeAt S.{u, v} NativeSymmetricDelooping.firstIndex).map
          NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ≫
        moduleStabilization.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex :=
  scalarStabilization_sourceArrow.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex
    NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv


/-- The original lambda source itself is the same scalar and unit-index module arrow,
with the first coefficient inverse retained in its actual order. -/
theorem actualFirstSource_moduleArrow :
    sourceArrow.{u, v} (r := 𝟙_ I) (s := NativeSymmetricDelooping.firstIndex)
        (M := 𝟙_ V.{u, v}) (M' := PointedCGWH.sphereOne.{u, v})
        NativeSymmetricLambda.firstSource.{u, v} =
      (Mod.dayFreeAt S.{u, v} NativeSymmetricDelooping.firstIndex).map
          NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv ≫
        moduleStabilization.{u, v} (𝟙_ I) NativeSymmetricDelooping.firstIndex := by
  rw [NativeSymmetricLambda.firstSource_original]
  exact firstSource_moduleArrow.{u, v}

end NativeOmegaRecovery.NativeSymmetricSourceComposite
