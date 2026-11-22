/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
public import MathlibExt.CategoryTheory.Enriched.FreeAdjunctionSource
public import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation

/-!
# Native and Day free functor comparisons

Uses the symmetric module/operator equivalence and the free-evaluation adjunctions to compare Day free modules with native enriched free objects. The evaluation comparison retains every underlying module component, and the resulting natural isomorphisms compare both free presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaPreparation.SymmetricNativeFree
attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj

set_option backward.isDefEq.respectTransparency false in
/-- The full original carrier functor keeps the actual original free/evaluation endpoint on every
module map. -/
def evaluationIso (n : Operad.SmallFinBijGroupoid) :
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor ⋙
      evaluation (PointedCGWH.symmetricOperatorObj.{u, v} n) ≅
    Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} n :=
  NatIso.ofComponents (fun M => Iso.refl (M.X.functor.obj n)) (by
    intro M N f
    change component
        (PointedCGWH.SymmetricModulePresentation.toOperatorMorphism f)
          (PointedCGWH.symmetricOperatorObj.{u, v} n) ≫ 𝟙 (N.X.functor.obj n) =
      𝟙 (M.X.functor.obj n) ≫ f.hom.natTrans.app n
    rw [PointedCGWH.SymmetricModulePresentation.toOperatorMorphism_component]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The original left Day free compares with the unchanged native free through the existing actual
carrier and chosen adjunctions. -/
def comparison (n : Operad.SmallFinBijGroupoid) :
    Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n ≅
      Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} n) ⋙
        PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse :=
  FreeAdjunctionSource.comparison
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    (PointedCGWH.symmetricOperatorObj.{u, v} n)
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n)
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} n)
    (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v} n) (evaluationIso n)

/-- The original free image in the actual complete operator carrier is the existing
arbitrary-coefficient native free functor. -/
def operatorComparison (n : Operad.SmallFinBijGroupoid) :
    Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n ⋙
      PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor ≅
    Free.functor (PointedCGWH.symmetricOperatorObj.{u, v} n) :=
  FreeAdjunctionSource.operatorIso
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
    (PointedCGWH.symmetricOperatorObj.{u, v} n)
    (Mod.dayFreeAt PointedCGWH.sphereSequence.{u, v} n)
    (Mod.dayEvaluation PointedCGWH.sphereSequence.{u, v} n)
    (Mod.dayFreeAtEvaluationAdjunction PointedCGWH.sphereSequence.{u, v} n) (evaluationIso n)

end NativeOmegaPreparation.SymmetricNativeFree
