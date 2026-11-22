/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.LeftPresentationModel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Quillen
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Factorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Generators
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.FreeEvaluation

/-!
# Original HSS-left free adjunction and cardinal-data migration

Use the full proved original sphere Day-module/operator equivalence. Original
left-module free maps, their entire Hom correspondence, and native cardinal
data remain on the same module carrier. The right-module/D_R source join
remains a separate dependency.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed ExternalProduct

namespace PointedCGWH.Spectra.Symmetric.LeftPresentationModel

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal PointedCGWH.sphereSequenceMonObj
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

private theorem pointedSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] pointedSmallColimits

private abbrev presentation :=
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
private def originalAdjunction (n : I) :
    Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n ⊣
      Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} n :=
  Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v} n

/-- Compare ORIGINAL HSS-left free modules to the native free functor through the actual inverse. -/
def freeComparison (n : I) :
    SymmetricFreeEvaluation.originalFreeFunctor.{u, v} n ≅
      SymmetricFreeEvaluation.nativeFreeFunctor.{u, v} n :=
  SymmetricFreeEvaluation.freeComparison n

/-- The full original HSS-left free functor maps naturally to the actual native free functor. -/
def mappedFreeComparison (n : I) :
    SymmetricFreeEvaluation.originalFreeFunctor.{u, v} n ⋙
      PointedCGWH.SymmetricModulePresentation.moduleToOperator.{u, v} ≅
        EnrichedFunctorCat.Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} n) :=
  Functor.isoWhiskerRight (freeComparison n) presentation.functor ≪≫
    eqToIso (congrArg (fun F => F ⋙ presentation.functor)
      (SymmetricFreeEvaluation.nativeFreeFunctor_eq n)) ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (EnrichedFunctorCat.Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} n))
          presentation.counitIso ≪≫ Functor.rightUnitor _

/-- Every whole ORIGINAL free-module adjunct retains the full native and carrier Hom maps. -/
theorem freeComparison_homEquiv (n : I) {X : PointedCGWH.{u, v}} {M : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u,
  v}}
    (f : (SymmetricFreeEvaluation.nativeFreeFunctor.{u, v} n).obj X ⟶ M) :
    (SymmetricFreeEvaluation.originalAdjunction n).homEquiv X M
        ((freeComparison n).hom.app X ≫ f) =
      (SymmetricFreeEvaluation.transportedAdjunction n).homEquiv X M f ≫
        (SymmetricFreeEvaluation.evaluationIso n).hom.app M :=
  (SymmetricFreeEvaluation.freeComparison_homEquiv n f).trans
    (SymmetricFreeEvaluation.migratedAdjunction_homEquiv n f)

/-- Every ORIGINAL inverse module adjunct is retained by the full native free comparison. -/
theorem freeComparison_homEquiv_symm (n : I) {X : PointedCGWH.{u, v}} {M :
  PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}}
    (f : X ⟶ (SymmetricFreeEvaluation.originalEvaluationFunctor.{u, v} n).obj M) :
    (freeComparison n).hom.app X ≫
      ((SymmetricFreeEvaluation.migratedAdjunction n).homEquiv X M).symm f =
        ((SymmetricFreeEvaluation.originalAdjunction n).homEquiv X M).symm f :=
  SymmetricFreeEvaluation.freeComparison_homEquiv_symm n f

/-- The actual ORIGINAL module unit is preserved by the complete free comparison. -/
theorem freeComparison_unit (n : I) (X : PointedCGWH.{u, v}) :
    (SymmetricFreeEvaluation.originalAdjunction n).unit.app X ≫
      (SymmetricFreeEvaluation.originalEvaluationFunctor.{u, v} n).map
        ((freeComparison n).hom.app X) =
        (SymmetricFreeEvaluation.migratedAdjunction n).unit.app X :=
  SymmetricFreeEvaluation.freeComparison_unit n X

/-- The actual ORIGINAL module counit is preserved by the complete free comparison. -/
theorem freeComparison_counit (n : I) (M : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    (freeComparison n).hom.app
        ((SymmetricFreeEvaluation.originalEvaluationFunctor.{u, v} n).obj M) ≫
      (SymmetricFreeEvaluation.migratedAdjunction n).counit.app M =
        (SymmetricFreeEvaluation.originalAdjunction n).counit.app M :=
  SymmetricFreeEvaluation.freeComparison_counit n M

/-- The mapped original whole free module arrow is isomorphic to the actual native free arrow. -/
def freeGeneratorArrowIso (n : I) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk (presentation.functor.map
      ((Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n).map f)) ≅
        CategoryTheory.Arrow.mk ((EnrichedFunctorCat.Free.functor
          (PointedCGWH.symmetricOperatorObj.{u, v} n)).map f) :=
  CategoryTheory.Arrow.isoOfNatIso
    (eqToIso (congrArg (fun F => F ⋙ presentation.functor)
      (SymmetricFreeEvaluation.originalFreeFunctor_eq n).symm) ≪≫ mappedFreeComparison n)
    (CategoryTheory.Arrow.mk f)

/-- The entire ORIGINAL HSS-left I family maps to the canonical full Arrow iso closure. -/
theorem boundaryGenerators_map : boundaryGenerators.{u, v}.map presentation.functor =
    (EnrichedProjective.generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      PointedCGWH.realizedBoundaryInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.originalGenerators_map_eq presentation
    PointedCGWH.symmetricOperatorObj.{u, v} operatorObj_surjective
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v})
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v})
    originalAdjunction evaluationIso _

/-- The entire ORIGINAL HSS-left J family maps to the canonical full Arrow iso closure. -/
theorem hornGenerators_map : hornGenerators.{u, v}.map presentation.functor =
    (EnrichedProjective.generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
      PointedCGWH.realizedHornInclusions.{u, v}).isoClosure :=
  EnrichedProjective.NativePresentation.originalGenerators_map_eq presentation
    PointedCGWH.symmetricOperatorObj.{u, v} operatorObj_surjective
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v})
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v})
    originalAdjunction evaluationIso _

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/--
The actual ORIGINAL HSS-left free/evaluation adjunction is Quillen for the constructed source
model.
-/
theorem freeAtEvaluation_isQuillenAdjunction (n : I) :
    let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v} n).IsQuillenAdjunction :=
  EnrichedProjective.NativePresentation.originalFreeEvaluation_isQuillenAdjunction presentation
    (PointedCGWH.symmetricOperatorObj.{u, v} n) (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n)
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} n) (originalAdjunction n) (evaluationIso n)

/-- The entire original free-I middle functor uses the actual complete inverse module functor. -/
theorem cofibrantFactorizationData_Z :
  ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).Z =
    presentation.functor.mapArrow ⋙
      (EnrichedProjective.Native.cofibrantFactorizationData (A :=
        PointedCGWH.SymmetricOperatorIndex.{u, v})).Z ⋙
      PointedCGWH.SymmetricModulePresentation.operatorToModule.{u, v} := rfl

/-- The entire original free-J middle functor uses the actual complete inverse module functor. -/
theorem fibrantFactorizationData_Z : ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
  PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).Z =
    presentation.functor.mapArrow ⋙
      (EnrichedProjective.Native.fibrantFactorizationData (A :=
        PointedCGWH.SymmetricOperatorIndex.{u, v})).Z ⋙
      PointedCGWH.SymmetricModulePresentation.operatorToModule.{u, v} := rfl

/-- Every arbitrary original module square retains the whole original free-I middle map. -/
theorem cofibrantFactorizationData_Z_map {f g : CategoryTheory.Arrow PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}}
  (φ : f ⟶ g) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).Z.map φ = presentation.inverse.map
      ((EnrichedProjective.Native.cofibrantFactorizationData (A :=
        PointedCGWH.SymmetricOperatorIndex.{u, v})).Z.map
        (presentation.functor.mapArrow.map φ)) := rfl

/-- Every arbitrary original module square retains the whole original free-J middle map. -/
theorem fibrantFactorizationData_Z_map {f g : CategoryTheory.Arrow PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}}
  (φ : f ⟶ g) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).Z.map φ = presentation.inverse.map
      ((EnrichedProjective.Native.fibrantFactorizationData (A :=
        PointedCGWH.SymmetricOperatorIndex.{u, v})).Z.map
        (presentation.functor.mapArrow.map φ)) := rfl

/-- The actual source free-I components factor the SAME original whole module arrow. -/
theorem cofibrantFactorizationData_fac (f : CategoryTheory.Arrow PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).p.app f =
      f.hom :=
  EnrichedProjective.NativePresentation.cofibrantFactorizationData_fac presentation f

/-- The actual source free-J components factor the SAME original whole module arrow. -/
theorem fibrantFactorizationData_fac (f : CategoryTheory.Arrow PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).p.app f = f.hom :=
  EnrichedProjective.NativePresentation.fibrantFactorizationData_fac presentation f

/--
The original free-I source left lifting class and ALL original right-map levels are preserved.
-/
theorem cofibrantFactorizationData_original_classes (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    boundaryGenerators.{u, v}.rlp.llp
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : I, trivialFibrations PointedCGWH.{u, v}
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
          PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app n) := by
  let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
  have h : cofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f) ∧
      trivialFibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).p.app f) :=
    EnrichedProjective.NativePresentation.cofibrantFactorizationData_classes presentation f
  exact ⟨Eq.mp (congrArg (fun P : MorphismProperty PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} =>
    P (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f)) cofibrations_eq) h.1,
    (trivialFibrations_iff _).mp h.2⟩

/--
The original free-J source left lifting class and ALL original right-map levels are preserved.
-/
theorem fibrantFactorizationData_original_classes (f : CategoryTheory.Arrow
  PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    hornGenerators.{u, v}.rlp.llp (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f) ∧
      ∀ n : I, fibrations PointedCGWH.{u, v}
        ((((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
          PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).p.app f).hom.natTrans.app n) := by
  let _ : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
  have h : trivialCofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
    (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f) ∧
      fibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).p.app f) :=
    EnrichedProjective.NativePresentation.fibrantFactorizationData_classes presentation f
  exact ⟨Eq.mp (congrArg (fun P : MorphismProperty PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} =>
    P (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})).i.app f)) trivialCofibrations_eq) h.1,
    (fibrations_iff _).mp h.2⟩

end PointedCGWH.Spectra.Symmetric.LeftPresentationModel
