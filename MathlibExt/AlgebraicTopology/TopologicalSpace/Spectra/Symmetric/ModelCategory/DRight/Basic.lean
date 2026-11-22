/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.StandardRightMigration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.DRight.Equivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.CanonicalCarrierMigration

/-!
# Native model classes on the genuine original D_R source

The source index is the actual opposite standard RIGHT free-module mapping
category. The full source equivalence and original standard Day adjunction
identify every original level map and the whole free-I/J families. The direct
source-index algorithm and transported OLD J algorithm are separate data.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory CGWH.limits ExternalProduct

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
  PointedCGWH.SymmetricModuleMappingComparison.literalEnrichedOrdinaryCategory

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual original standard RIGHT sphere-module category. -/
abbrev Carrier := PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}

/-- Genuine full enriched diagrams on the independent original D_R mapping category. -/
abbrev SourceCarrier := EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricDRight.Index

/-- The full actual original module/source equivalence, including its given inverse. -/
abbrev presentation : Carrier.{u, v} ≌ SourceCarrier.{u, v} :=
  PointedCGWH.SymmetricDRightEquivalence.moduleDiagramEquivalence.{u, v}


/-- The actual stock RIGHT-module conversion to the canonical spectrum carrier. -/
abbrev canonicalPresentation : Carrier.{u, v} ≌ Spectrum.{u, v} :=
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence

/-- The entire original source inverse followed by the actual canonical RIGHT conversion. -/
abbrev canonicalSourcePresentation : SourceCarrier.{u, v} ≌ Spectrum.{u, v} :=
  presentation.symm.trans canonicalPresentation

/-- Every original degree label covers the entire genuine D_R source index. -/
theorem sourceObj_surjective : Function.Surjective PointedCGWH.SymmetricDRight.obj := by
  intro a
  rcases a with ⟨n⟩
  exact ⟨n, rfl⟩

private def restrictionEvaluationIso (d : PointedCGWH.SymmetricDRight.Index) :
    EnrichedFunctorCat.restriction PointedCGWH.SymmetricDRightEquivalence.sourceToOperator.{u, v} ⋙
      EnrichedFunctorCat.evaluation d ≅
        EnrichedFunctorCat.evaluation
          (PointedCGWH.SymmetricDRightEquivalence.sourceToOperator.{u, v}.obj d) :=
  NatIso.ofComponents (fun F =>
    Iso.refl (F.toEnrichedFunctor.obj
      (PointedCGWH.SymmetricDRightEquivalence.sourceToOperator.obj d))) (by
    intro F G f
    change EnrichedFunctorCat.component
      (EnrichedFunctorCat.restrictionMap
        PointedCGWH.SymmetricDRightEquivalence.sourceToOperator f) d ≫ 𝟙 _ =
          𝟙 _ ≫ EnrichedFunctorCat.component f
            (PointedCGWH.SymmetricDRightEquivalence.sourceToOperator.obj d)
    rw [EnrichedFunctorCat.restrictionMap_component]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Full actual D_R restriction retains the exact original degree evaluation. -/
def rightDiagramEvaluationIso (n : I) :
    EnrichedFunctorCat.restriction PointedCGWH.SymmetricDRightEquivalence.sourceToOperator.{u, v} ⋙
      EnrichedFunctorCat.evaluation (PointedCGWH.SymmetricDRight.obj n) ≅
        EnrichedFunctorCat.evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n) :=
  restrictionEvaluationIso (PointedCGWH.SymmetricDRight.obj n) ≪≫
    eqToIso (congrArg (fun a => EnrichedFunctorCat.evaluation a)
      ((PointedCGWH.SymmetricDRightEquivalence.sourceToOperator_obj
        (PointedCGWH.SymmetricDRight.obj n)).trans
          (PointedCGWH.SymmetricDRightHomComparison.objectEquiv_apply n)))

/-- The genuine original module/source equivalence keeps the actual standard RIGHT evaluation. -/
def evaluationIso (n : I) :
    presentation.functor ⋙
      EnrichedFunctorCat.evaluation (PointedCGWH.SymmetricDRight.obj n) ≅
        RightPresentationModel.standardEvaluation.{u, v} n :=
  eqToIso (congrArg (fun F => F ⋙
    EnrichedFunctorCat.evaluation (PointedCGWH.SymmetricDRight.obj n))
      PointedCGWH.SymmetricDRightEquivalence.moduleDiagram_functor) ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft PointedCGWH.SymmetricRightModulePresentation.rightModuleToOperator
        (rightDiagramEvaluationIso n) ≪≫ RightPresentationModel.standardEvaluationIso n

/-- The actual standard RIGHT free-I family with all correlated original degree labels. -/
abbrev boundaryGenerators := RightPresentationModel.standardBoundaryGenerators.{u, v}

/-- The actual standard RIGHT free-J family with all correlated original degree labels. -/
abbrev hornGenerators := RightPresentationModel.standardHornGenerators.{u, v}

section LegacyReadbacks
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every original standard RIGHT module weak map is detected on all original degree components. -/
theorem weakEquivalences_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      presentation)
    weakEquivalences Carrier.{u, v} f ↔
      ∀ n : I, weakEquivalences PointedCGWH.{u, v} (f.hom.natTrans.app n) := by
  let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    presentation)
  refine (EnrichedProjective.NativePresentation.weakEquivalences_iff_original presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardEvaluation evaluationIso f).trans ?_
  apply forall_congr'
  intro n
  rw [show RightPresentationModel.standardEvaluation.{u, v} n =
    PointedCGWH.SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} n from
      PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n]
  rfl

/-- Every original standard RIGHT module fibration is detected on all original degree components. -/
theorem fibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      presentation)
    fibrations Carrier.{u, v} f ↔
      ∀ n : I, fibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) := by
  let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    presentation)
  refine (EnrichedProjective.NativePresentation.fibrations_iff_original presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardEvaluation evaluationIso f).trans ?_
  apply forall_congr'
  intro n
  rw [show RightPresentationModel.standardEvaluation.{u, v} n =
    PointedCGWH.SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} n from
      PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n]
  rfl

/-- Every original standard RIGHT trivial fibration is detected on all original components. -/
theorem trivialFibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      presentation)
    trivialFibrations Carrier.{u, v} f ↔
      ∀ n : I, trivialFibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) := by
  let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    presentation)
  refine (EnrichedProjective.NativePresentation.trivialFibrations_iff_original presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardEvaluation evaluationIso f).trans ?_
  apply forall_congr'
  intro n
  rw [show RightPresentationModel.standardEvaluation.{u, v} n =
    PointedCGWH.SymmetricStandardRightFreeEvaluation.literalEvaluation.{u, v} n from
      PointedCGWH.SymmetricStandardRightFreeEvaluation.originalEvaluationFunctor_eq n]
  rfl

/-- The complete original standard RIGHT free-I family gives the source cofibrations. -/
theorem cofibrations_eq :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      presentation)
    cofibrations Carrier.{u, v} = boundaryGenerators.{u, v}.rlp.llp :=
  EnrichedProjective.NativePresentation.cofibrations_eq_originalGenerators presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardFreeAt RightPresentationModel.standardEvaluation
    RightPresentationModel.standardFreeAdjunction evaluationIso

/-- The complete original standard RIGHT free-J family gives exactly the trivial cofibrations. -/
theorem trivialCofibrations_eq :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      presentation)
    trivialCofibrations Carrier.{u, v} = hornGenerators.{u, v}.rlp.llp :=
  EnrichedProjective.NativePresentation.trivialCofibrations_eq_originalGenerators presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardFreeAt RightPresentationModel.standardEvaluation
    RightPresentationModel.standardFreeAdjunction evaluationIso

/-- The original standard RIGHT free/evaluation adjunction is Quillen for the source model. -/
theorem standardFreeAdjunction_isQuillen (n : I) :
    let _ : ModelCategory Carrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      presentation)
    (RightPresentationModel.standardFreeAdjunction n).IsQuillenAdjunction :=
  EnrichedProjective.NativePresentation.originalFreeEvaluation_isQuillenAdjunction presentation
    (PointedCGWH.SymmetricDRight.obj n) (RightPresentationModel.standardFreeAt n)
    (RightPresentationModel.standardEvaluation n)
    (RightPresentationModel.standardFreeAdjunction n) (evaluationIso n)

/-- Literal original D_R source weak maps are checked at every original degree label. -/
theorem source_weakEquivalences_iff {X Y : SourceCarrier.{u, v}} (f : X ⟶ Y) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    weakEquivalences SourceCarrier.{u, v} f ↔
      ∀ n : I, weakEquivalences PointedCGWH.{u, v}
        (EnrichedFunctorCat.component f (PointedCGWH.SymmetricDRight.obj n)) := by
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  have hEq := EnrichedProjective.Native.weakEquivalences_eq
    (B := B) (A := PointedCGWH.SymmetricDRight.Index)
  refine (Iff.of_eq (congrArg
    (fun P : MorphismProperty SourceCarrier.{u, v} => P f) hEq)).trans ?_
  constructor
  · exact fun h n => h (Discrete.mk (PointedCGWH.SymmetricDRight.obj n))
  · intro h a
    rcases sourceObj_surjective a.as with ⟨n, hn⟩
    change weakEquivalences PointedCGWH.{u, v} (EnrichedFunctorCat.component f a.as)
    rw [← hn]
    exact h n

/-- Literal original D_R source fibrations are checked at every original degree label. -/
theorem source_fibrations_iff {X Y : SourceCarrier.{u, v}} (f : X ⟶ Y) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    fibrations SourceCarrier.{u, v} f ↔
      ∀ n : I, fibrations PointedCGWH.{u, v}
        (EnrichedFunctorCat.component f (PointedCGWH.SymmetricDRight.obj n)) := by
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  have hEq := EnrichedProjective.Native.fibrations_eq
    (B := B) (A := PointedCGWH.SymmetricDRight.Index)
  refine (Iff.of_eq (congrArg
    (fun P : MorphismProperty SourceCarrier.{u, v} => P f) hEq)).trans ?_
  constructor
  · exact fun h n => h (Discrete.mk (PointedCGWH.SymmetricDRight.obj n))
  · intro h a
    rcases sourceObj_surjective a.as with ⟨n, hn⟩
    change fibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component f a.as)
    rw [← hn]
    exact h n

/-- Literal D_R source trivial fibrations are checked on the complete original components. -/
theorem source_trivialFibrations_iff {X Y : SourceCarrier.{u, v}} (f : X ⟶ Y) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    trivialFibrations SourceCarrier.{u, v} f ↔
      ∀ n : I, trivialFibrations PointedCGWH.{u, v}
        (EnrichedFunctorCat.component f (PointedCGWH.SymmetricDRight.obj n)) := by
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  have hEq := EnrichedProjective.Native.trivialFibrations_eq
    (B := B) (A := PointedCGWH.SymmetricDRight.Index)
  refine (Iff.of_eq (congrArg
    (fun P : MorphismProperty SourceCarrier.{u, v} => P f) hEq)).trans ?_
  constructor
  · exact fun h n => h (Discrete.mk (PointedCGWH.SymmetricDRight.obj n))
  · intro h a
    rcases sourceObj_surjective a.as with ⟨n, hn⟩
    change trivialFibrations PointedCGWH.{u, v} (EnrichedFunctorCat.component f a.as)
    rw [← hn]
    exact h n


end LegacyReadbacks

attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.generatorOrderBot
open HomotopicalAlgebra.EnrichedProjective

/-- Weak equivalences of symmetric sphere modules in the canonical operator presentation. -/
def moduleWeak : MorphismProperty Carrier.{u, v} :=
  CanonicalCarrierMigration.sourceWeakEquivalences

/-- Cofibrations of symmetric sphere modules detected by the original right-module-to-operator
functor. -/
def moduleCofibrations : MorphismProperty Carrier.{u, v} :=
  (cofibrations Spectrum.{u, v}).inverseImage
    PointedCGWH.SymmetricRightModulePresentation.rightModuleToOperator

/-- Fibrations of symmetric sphere modules detected by the original right-module-to-operator
functor. -/
def moduleFibrations : MorphismProperty Carrier.{u, v} :=
  (fibrations Spectrum.{u, v}).inverseImage
    PointedCGWH.SymmetricRightModulePresentation.rightModuleToOperator

/-- Trivial fibrations of symmetric sphere modules detected by the original
right-module-to-operator functor. -/
def moduleTrivialFibrations : MorphismProperty Carrier.{u, v} :=
  (trivialFibrations Spectrum.{u, v}).inverseImage
    PointedCGWH.SymmetricRightModulePresentation.rightModuleToOperator

/-- Trivial cofibrations of symmetric sphere modules detected by the original
right-module-to-operator functor. -/
def moduleTrivialCofibrations : MorphismProperty Carrier.{u, v} :=
  (trivialCofibrations Spectrum.{u, v}).inverseImage
    PointedCGWH.SymmetricRightModulePresentation.rightModuleToOperator

/-- Weak equivalences on the D_R source carrier detected by the inverse presentation in sphere
modules. -/
def sourceWeak : MorphismProperty SourceCarrier.{u, v} :=
  moduleWeak.inverseImage presentation.inverse

/-- Cofibrations on the D_R source carrier detected by the inverse presentation in sphere modules. -/
def sourceCofibrations : MorphismProperty SourceCarrier.{u, v} :=
  moduleCofibrations.inverseImage presentation.inverse

/-- Fibrations on the D_R source carrier detected by the inverse presentation in sphere modules. -/
def sourceFibrations : MorphismProperty SourceCarrier.{u, v} :=
  moduleFibrations.inverseImage presentation.inverse

/-- Trivial fibrations on the D_R source carrier detected by the inverse presentation in sphere
modules. -/
def sourceTrivialFibrations : MorphismProperty SourceCarrier.{u, v} :=
  moduleTrivialFibrations.inverseImage presentation.inverse

/-- Trivial cofibrations on the D_R source carrier detected by the inverse presentation in sphere
modules. -/
def sourceTrivialCofibrations : MorphismProperty SourceCarrier.{u, v} :=
  moduleTrivialCofibrations.inverseImage presentation.inverse

instance sourceCofibrations_respectsIso : sourceCofibrations.{u, v}.RespectsIso := by
  unfold sourceCofibrations moduleCofibrations
  infer_instance

instance sourceFibrations_respectsIso : sourceFibrations.{u, v}.RespectsIso := by
  unfold sourceFibrations moduleFibrations
  infer_instance

instance sourceTrivialFibrations_respectsIso : sourceTrivialFibrations.{u, v}.RespectsIso := by
  unfold sourceTrivialFibrations moduleTrivialFibrations
  infer_instance

instance sourceTrivialCofibrations_respectsIso : sourceTrivialCofibrations.{u, v}.RespectsIso := by
  unfold sourceTrivialCofibrations moduleTrivialCofibrations
  infer_instance

theorem moduleWeak_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    moduleWeak f ↔ ∀ n : I, weakEquivalences PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  (CanonicalCarrierMigration.five_model_classes f).1.symm.trans
    (RightPresentationModel.weakEquivalences_iff f)

theorem moduleFibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    moduleFibrations f ↔ ∀ n : I, fibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  (CanonicalCarrierMigration.five_model_classes f).2.1.symm.trans
    (RightPresentationModel.fibrations_iff f)

theorem moduleTrivialFibrations_iff {M N : Carrier.{u, v}} (f : M ⟶ N) :
    moduleTrivialFibrations f ↔
      ∀ n : I, trivialFibrations PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  (CanonicalCarrierMigration.five_model_classes f).2.2.2.1.symm.trans
    (RightPresentationModel.trivialFibrations_iff f)

theorem moduleCofibrations_eq : moduleCofibrations.{u, v} = boundaryGenerators.{u, v}.rlp.llp := by
  funext M N f
  exact propext ((CanonicalCarrierMigration.five_model_classes f).2.2.1.symm.trans
    (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f)
      RightPresentationModel.standard_cofibrations_eq)))

theorem moduleTrivialCofibrations_eq :
    moduleTrivialCofibrations.{u, v} = hornGenerators.{u, v}.rlp.llp := by
  funext M N f
  exact propext ((CanonicalCarrierMigration.five_model_classes f).2.2.2.2.symm.trans
    (Iff.of_eq (congrArg (fun P : MorphismProperty Carrier.{u, v} => P f)
      RightPresentationModel.standard_trivialCofibrations_eq)))

private theorem property_roundtrip (P : MorphismProperty SourceCarrier.{u, v})
    [P.RespectsIso] :
    (P.inverseImage presentation.functor).inverseImage presentation.inverse = P := by
  funext X Y f
  exact propext (P.arrow_mk_iso_iff (Arrow.isoOfNatIso presentation.counitIso (Arrow.mk f)))

private theorem generic_module_weak_eq :
    (NativePresentation.modelCategory presentation).categoryWithWeakEquivalences.weakEquivalences =
      moduleWeak.{u, v} := by
  let _ : ModelCategory Carrier.{u, v} := NativePresentation.modelCategory presentation
  funext M N f
  exact propext ((NativePresentation.weakEquivalences_iff_original presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardEvaluation evaluationIso f).trans
      (moduleWeak_iff f).symm)

private theorem generic_module_fibrations_eq :
    (NativePresentation.modelCategory presentation).categoryWithFibrations.fibrations =
      moduleFibrations.{u, v} := by
  let _ : ModelCategory Carrier.{u, v} := NativePresentation.modelCategory presentation
  funext M N f
  refine propext ((NativePresentation.fibrations_iff_original presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardEvaluation evaluationIso f).trans ?_)
  exact (moduleFibrations_iff f).symm

private theorem generic_module_trivialFibrations_eq :
    (let _ : ModelCategory Carrier.{u, v} := NativePresentation.modelCategory presentation;
      trivialFibrations Carrier.{u, v}) = moduleTrivialFibrations.{u, v} := by
  let _ : ModelCategory Carrier.{u, v} := NativePresentation.modelCategory presentation
  funext M N f
  exact propext ((NativePresentation.trivialFibrations_iff_original presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardEvaluation evaluationIso f).trans
      (moduleTrivialFibrations_iff f).symm)

private theorem generic_module_cofibrations_eq :
    (NativePresentation.modelCategory presentation).categoryWithCofibrations.cofibrations =
      moduleCofibrations.{u, v} :=
  (NativePresentation.cofibrations_eq_originalGenerators presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardFreeAt RightPresentationModel.standardEvaluation
    RightPresentationModel.standardFreeAdjunction evaluationIso).trans moduleCofibrations_eq.symm

private theorem generic_module_trivialCofibrations_eq :
    (let _ : ModelCategory Carrier.{u, v} := NativePresentation.modelCategory presentation;
      trivialCofibrations Carrier.{u, v}) = moduleTrivialCofibrations.{u, v} :=
  (NativePresentation.trivialCofibrations_eq_originalGenerators presentation
    PointedCGWH.SymmetricDRight.obj sourceObj_surjective
    RightPresentationModel.standardFreeAt RightPresentationModel.standardEvaluation
    RightPresentationModel.standardFreeAdjunction evaluationIso).trans moduleTrivialCofibrations_eq.symm

theorem sourceWeak_eq_evaluation : sourceWeak.{u, v} =
    EvaluationTransfer.evaluationProperty
      (fun a : PointedCGWH.SymmetricDRight.Index => EnrichedFunctorCat.evaluation a)
      (weakEquivalences PointedCGWH.{u, v}) := by
  let _ : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
  calc
    sourceWeak.{u, v} = moduleWeak.inverseImage presentation.inverse := rfl
    _ = ((weakEquivalences SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
        presentation.inverse := by rw [← generic_module_weak_eq]; rfl
    _ = weakEquivalences SourceCarrier.{u, v} := property_roundtrip _
    _ = _ := Native.weakEquivalences_eq

theorem sourceFibrations_eq_evaluation : sourceFibrations.{u, v} =
    EvaluationTransfer.evaluationProperty
      (fun a : PointedCGWH.SymmetricDRight.Index => EnrichedFunctorCat.evaluation a)
      (fibrations PointedCGWH.{u, v}) := by
  let _ : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
  calc
    sourceFibrations.{u, v} = moduleFibrations.inverseImage presentation.inverse := rfl
    _ = ((fibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
        presentation.inverse := by rw [← generic_module_fibrations_eq]; rfl
    _ = fibrations SourceCarrier.{u, v} := property_roundtrip _
    _ = _ := Native.fibrations_eq

theorem sourceTrivialFibrations_eq_evaluation : sourceTrivialFibrations.{u, v} =
    EvaluationTransfer.evaluationProperty
      (fun a : PointedCGWH.SymmetricDRight.Index => EnrichedFunctorCat.evaluation a)
      (trivialFibrations PointedCGWH.{u, v}) := by
  let _ : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
  calc
    sourceTrivialFibrations.{u, v} = moduleTrivialFibrations.inverseImage presentation.inverse := rfl
    _ = ((trivialFibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
        presentation.inverse := by rw [← generic_module_trivialFibrations_eq]; rfl
    _ = trivialFibrations SourceCarrier.{u, v} := property_roundtrip _
    _ = _ := Native.trivialFibrations_eq

theorem sourceCofibrations_eq_generators : sourceCofibrations.{u, v} =
    (EnrichedProjective.generators (A := PointedCGWH.SymmetricDRight.Index)
      PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp := by
  let _ : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
  calc
    sourceCofibrations.{u, v} = moduleCofibrations.inverseImage presentation.inverse := rfl
    _ = ((cofibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
        presentation.inverse := by rw [← generic_module_cofibrations_eq]; rfl
    _ = cofibrations SourceCarrier.{u, v} := property_roundtrip _
    _ = _ := Native.cofibrations_eq

theorem sourceTrivialCofibrations_eq_generators : sourceTrivialCofibrations.{u, v} =
    (EnrichedProjective.generators (A := PointedCGWH.SymmetricDRight.Index)
      PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp := by
  let _ : ModelCategory SourceCarrier.{u, v} := Native.modelCategory
  calc
    sourceTrivialCofibrations.{u, v} = moduleTrivialCofibrations.inverseImage presentation.inverse := rfl
    _ = ((trivialCofibrations SourceCarrier.{u, v}).inverseImage presentation.functor).inverseImage
        presentation.inverse := by rw [← generic_module_trivialCofibrations_eq]; rfl
    _ = trivialCofibrations SourceCarrier.{u, v} := property_roundtrip _
    _ = _ := Native.trivialCofibrations_eq

end PointedCGWH.Spectra.Symmetric.DRightPresentation
