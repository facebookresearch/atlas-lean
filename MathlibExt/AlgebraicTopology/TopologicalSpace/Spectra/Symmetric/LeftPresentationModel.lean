/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.OriginalClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.FreeEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation

/-!
# Actual native projective classes on the original HSS-left presentation

Use the complete proved sphere Day module/operator equivalence. All classes
refer to the actual native model and original whole module arrows/free labels.
The MMSS right-module/D_R comparison remains a separate dependency.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed ExternalProduct

namespace PointedCGWH.Spectra.Symmetric.LeftPresentationModel

open PointedCGWH.SymmetricModulePresentation
attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal PointedCGWH.sphereSequenceMonObj
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

private theorem pointedSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] pointedSmallColimits

/-- Every original finite-bijection object labels its exact native operator object. -/
theorem operatorObj_surjective :
    Function.Surjective (PointedCGWH.symmetricOperatorObj.{u, v}) := by
  intro a
  rcases a with ⟨n⟩
  exact ⟨(show I from n), rfl⟩

/-- Forward native evaluation is naturally the ORIGINAL whole Day-module evaluation. -/
def evaluationIso (n : I) :
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor ⋙
      EnrichedFunctorCat.evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n) ≅
        Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} n :=
  NatIso.ofComponents (fun M => Iso.refl (M.X.functor.obj n)) (by
    intro M N f
    change EnrichedFunctorCat.component (toOperatorMorphism f)
        (PointedCGWH.symmetricOperatorObj.{u, v} n) ≫ 𝟙 (N.X.functor.obj n) =
      𝟙 (M.X.functor.obj n) ≫ f.hom.natTrans.app n
    rw [toOperatorMorphism_component]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Literal ORIGINAL free-boundary module images, with whole original labels. -/
def boundaryGenerators : MorphismProperty (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v})
  PointedCGWH.sphereSequence.{u, v}) :=
  MorphismProperty.adjointFamilyGenerators
    (fun n : I => Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n)
    PointedCGWH.realizedBoundaryInclusions.{u, v}

/-- Literal ORIGINAL free-horn module images, with whole original labels. -/
def hornGenerators : MorphismProperty (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v})
  PointedCGWH.sphereSequence.{u, v}) :=
  MorphismProperty.adjointFamilyGenerators
    (fun n : I => Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n)
    PointedCGWH.realizedHornInclusions.{u, v}

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Actual source weak equivalences are detected by ORIGINAL module level maps. -/
theorem weakEquivalences_iff {M N : (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v})
  PointedCGWH.sphereSequence.{u, v})} (f : M ⟶ N) :
    letI : ModelCategory (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v})
      := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    weakEquivalences (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v}) f ↔
      ∀ n : I, weakEquivalences PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  EnrichedProjective.NativePresentation.weakEquivalences_iff_original
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    PointedCGWH.symmetricOperatorObj operatorObj_surjective
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v}) evaluationIso f

/-- Actual source fibrations are detected by ORIGINAL module level maps. -/
theorem fibrations_iff {M N : (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u,
  v})} (f : M ⟶ N) :
    letI : ModelCategory (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v})
      := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    fibrations (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v}) f ↔
      ∀ n : I, fibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  EnrichedProjective.NativePresentation.fibrations_iff_original
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    PointedCGWH.symmetricOperatorObj operatorObj_surjective
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v}) evaluationIso f

/-- The actual intersection class is detected at ORIGINAL source levels. -/
theorem trivialFibrations_iff {M N : (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v})
  PointedCGWH.sphereSequence.{u, v})} (f : M ⟶ N) :
    letI : ModelCategory (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v})
      := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    trivialFibrations (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v}) f ↔
      ∀ n : I, trivialFibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  EnrichedProjective.NativePresentation.trivialFibrations_iff_original
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    PointedCGWH.symmetricOperatorObj operatorObj_surjective
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v}) evaluationIso f

/-- The actual source right class is detected by ORIGINAL free-boundary maps. -/
theorem trivialFibrations_eq :
    letI : ModelCategory (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v})
      := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    trivialFibrations (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v}) =
      boundaryGenerators.{u, v}.rlp :=
  EnrichedProjective.NativePresentation.trivialFibrations_eq_originalGenerators
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    PointedCGWH.symmetricOperatorObj operatorObj_surjective
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v})
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v})
    (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v}) evaluationIso

/-- The actual source fibration class is detected by ORIGINAL free-horn maps. -/
theorem fibrations_eq :
    letI : ModelCategory (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v})
      := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    fibrations (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v}) =
      hornGenerators.{u, v}.rlp :=
  EnrichedProjective.NativePresentation.fibrations_eq_originalGenerators
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    PointedCGWH.symmetricOperatorObj operatorObj_surjective
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v})
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v})
    (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v}) evaluationIso

/-- The ACTUAL source cofibrations use the ORIGINAL full free-I generated class. -/
theorem cofibrations_eq :
    letI : ModelCategory (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v})
      := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    cofibrations (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v}) =
      boundaryGenerators.{u, v}.rlp.llp :=
  EnrichedProjective.NativePresentation.cofibrations_eq_originalGenerators
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    PointedCGWH.symmetricOperatorObj operatorObj_surjective
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v})
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v})
    (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v}) evaluationIso

/-- The ACTUAL source trivial cofibrations use the ORIGINAL full free-J generated class. -/
theorem trivialCofibrations_eq :
    letI : ModelCategory (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v})
      := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v})
    trivialCofibrations (CategoryTheory.Mod (PointedCGWH.SymmetricSequence.{u, v}) PointedCGWH.sphereSequence.{u, v}) =
      hornGenerators.{u, v}.rlp.llp :=
  EnrichedProjective.NativePresentation.trivialCofibrations_eq_originalGenerators
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    PointedCGWH.symmetricOperatorObj operatorObj_surjective
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v})
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v})
    (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v}) evaluationIso

end PointedCGWH.Spectra.Symmetric.LeftPresentationModel
