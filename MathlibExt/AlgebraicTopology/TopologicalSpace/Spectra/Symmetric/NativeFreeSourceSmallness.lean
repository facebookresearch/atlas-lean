/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFree.Levels
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHGeneratorSourceSmallness
import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingInstances
import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingSmash
import MathlibExt.CategoryTheory.Enriched.PointwiseSizeInstances
import MathlibExt.CategoryTheory.SmallObject.AdjointFamilySourceSmallness
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CofibrantFree

/-!
# Compact realized sources for the original native free spectra

The original standard right sphere-module free functor and its literal
evaluation are used throughout. Its evaluated free maps are closed embeddings
by the actual coefficient tensor comparison. Pointwise colimits and closed
cell closure then give source Hom preservation for the caller's original
relative complexes at the chosen realized-generator cardinal.

This implements the closed-inclusion argument of Pavlov--Scholbach,
*Homotopy theory of symmetric powers*, §7.5, and its free/evaluation transfer
in *Symmetric operads in abstract symmetric spectra*, Appendix 9.1 and 9.3.
The adjunction transfer uses the same colimit, as in Schwede--Shipley,
*Algebras and modules in monoidal model categories*, Remark A.5.
-/

set_option autoImplicit false
noncomputable section

universe u v
open CategoryTheory Limits MonoidalCategory Topology HomotopicalAlgebra
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.NativeFreeSourceSmallness

open SymmetricStandardRightFreeEvaluation

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

/-- The actual underlying closed-inclusion property on pointed coefficients. -/
abbrev closedInclusions : MorphismProperty PointedCGWH.{u, v} :=
  TopCat.closedEmbeddings.inverseImage
    (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})

/-- The original free images keep their actual degree and realized-generator arrow. -/
def generators (K : MorphismProperty CGWH.{u, v}) : MorphismProperty Carrier.{u, v} :=
  MorphismProperty.adjointFamilyGenerators originalFreeFunctor
    (K.strictMap (Under.costar CGWH.point))

/-- Literal original evaluation preserves the same pointwise colimits. -/
theorem evaluationPreservesColimits (n : Operad.SmallFinBijGroupoid) :
    PreservesColimitsOfSize.{v, v} (originalEvaluationFunctor.{u, v} n) := by
  let _ : PreservesColimitsOfSize.{v, v} (nativeEvaluationFunctor.{u, v} n) := by
    rw [nativeEvaluationFunctor_eq]
    change PreservesColimitsOfSize.{v, v}
      (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor ⋙
        EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (symmetricOperatorObj n))
    infer_instance
  exact preservesColimits_of_natIso (evaluationIso n)

/-- The actual original free map evaluates to a closed inclusion in every degree. -/
theorem evaluatedFreeMapClosed (e n : Operad.SmallFinBijGroupoid)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (hf : closedInclusions f) :
    closedInclusions
      ((originalEvaluationFunctor n).map ((originalFreeFunctor e).map f)) := by
  let q := OriginalStandardRightFreeLevels.levelFunctorIso.{u, v} e n
  let a : Arrow.mk
      ((originalEvaluationFunctor n).map ((originalFreeFunctor e).map f)) ≅
      Arrow.mk (f ▷ OriginalStandardRightFreeLevels.coefficient e n) :=
    Arrow.isoMk (q.app X) (q.app Y) (q.hom.naturality f).symm
  exact (closedInclusions.arrow_mk_iso_iff a).mpr
    (isClosedEmbedding_whiskerRight f
      (OriginalStandardRightFreeLevels.coefficient e n) hf)

private theorem realizedGeneratorsClosed
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) :
    K.strictMap (Under.costar CGWH.point) ≤ closedInclusions := by
  intro X Y f hf
  cases hf with
  | map hg =>
      apply isClosedEmbedding_costarMap
      apply CGWH.coproducts_realizedGenerators_le_closedEmbeddings
      exact MorphismProperty.le_coproducts _ _ (hK _ hg)

/-- Generator evaluation uses the original coefficient maps, with no closed-class outcome input. -/
theorem generatorsEvaluateClosed
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    (n : Operad.SmallFinBijGroupoid) :
    generators K ≤ closedInclusions.inverseImage (originalEvaluationFunctor n) := by
  rw [generators, MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap]
  refine iSup_le fun e => ?_
  intro X Y f hf
  cases hf with
  | map hg =>
      exact evaluatedFreeMapClosed e n _ (realizedGeneratorsClosed K hK _ hg)

section OriginalClosedDiagram

variable (K : MorphismProperty CGWH.{u, v})
  (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
  {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
  (hg : (K.strictMap (Under.costar CGWH.point)) g)
  (n : Operad.SmallFinBijGroupoid)
  (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ Carrier.{u, v})
  [E.IsWellOrderContinuous]
  (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), closedInclusions ((originalEvaluationFunctor n).map (E.map φ)))

include K hK g hg hE

/-- Hom from the actual free realized source preserves the original supplied closed diagram. -/
theorem preservesOriginalClosedColimit :
    PreservesColimit E (coyoneda.obj (Opposite.op ((originalFreeFunctor n).obj Q))) := by
  let J := realizedGeneratorCardinal.{v}.ord.ToType
  let _ : PreservesColimitsOfSize.{v, v} (originalEvaluationFunctor.{u, v} n) :=
    evaluationPreservesColimits n
  let _ : PreservesWellOrderContinuousOfShape J (originalEvaluationFunctor.{u, v} n) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  let _ : (E ⋙ originalEvaluationFunctor n).IsWellOrderContinuous := inferInstance
  let _ : PreservesColimit (E ⋙ originalEvaluationFunctor n)
      (coyoneda.obj (Opposite.op Q)) :=
    PointedCGWH.realizedGeneratorSource_preservesClosedColimit
      K hK g hg (E ⋙ originalEvaluationFunctor n) hE
  exact (originalAdjunction n).preservesColimit_leftAdjointSource Q E

/-- Source Hom keeps each leg of the caller's original colimit cocone. -/
def mappedOriginalClosedCocone (c : Cocone E) (hc : IsColimit c) :
    IsColimit
      ((coyoneda.obj (Opposite.op ((originalFreeFunctor n).obj Q))).mapCocone c) := by
  let _ := preservesOriginalClosedColimit K hK g hg n E hE
  exact isColimitOfPreserves _ hc

end OriginalClosedDiagram

section ActualRelativeCells

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (K : MorphismProperty CGWH.{u, v})
  (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)

include hK

/-- Every evaluated transition of the caller's actual native free-cell history is closed. -/
theorem relativeCellTransitionsClosed
    {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators K).homFamily) f)
    (n : Operad.SmallFinBijGroupoid) :
    ∀ ⦃a b⦄ (φ : a ⟶ b), closedInclusions ((originalEvaluationFunctor n).map (c.F.map φ)) := by
  let _ : PreservesColimitsOfSize.{v, v} (originalEvaluationFunctor.{u, v} n) :=
    evaluationPreservesColimits n
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (originalEvaluationFunctor.{u, v} n) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  intro a b φ
  exact c.map_map_mem_of_le (originalEvaluationFunctor n) (generators K)
    closedInclusions (generatorsEvaluateClosed K hK n) φ

/-- An actual original free-generator source is small on the same native relative-cell history. -/
theorem preservesRelativeCellColimit
    {Q R X Y : Carrier.{u, v}} (i : Q ⟶ R) (hi : generators K i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators K).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op Q)) := by
  let _ (n : Operad.SmallFinBijGroupoid) :
      PreservesColimitsOfSize.{v, v} (originalEvaluationFunctor.{u, v} n) :=
    evaluationPreservesColimits n
  let _ (n : Operad.SmallFinBijGroupoid) :
      PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
        (originalEvaluationFunctor.{u, v} n) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  exact HomotopicalAlgebra.adjointFamilySource_preservesColimit
    originalFreeFunctor originalEvaluationFunctor originalAdjunction
    (K.strictMap (Under.costar CGWH.point)) closedInclusions
    (generatorsEvaluateClosed K hK)
    (fun g hg E _ hE =>
      PointedCGWH.realizedGeneratorSource_preservesClosedColimit K hK g hg E hE)
    i hi f c

/-- The caller's original relative endpoint and every original inclusion leg survive source Hom. -/
def mappedRelativeCellCocone
    {Q R X Y : Carrier.{u, v}} (i : Q ⟶ R) (hi : generators K i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => (generators K).homFamily) f) :
    IsColimit ((coyoneda.obj (Opposite.op Q)).mapCocone (Cocone.mk Y c.incl)) := by
  let _ := preservesRelativeCellColimit K hK i hi f c
  exact isColimitOfPreserves _ c.isColimit

end ActualRelativeCells

section OriginalOperatorPresentation

/-- The same native operator presentation of the actual original right sphere modules. -/
abbrev OperatorCarrier := EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}

/-- Keep the original standard RIGHT free functor before applying its genuine source equivalence. -/
def operatorOriginalFreeFunctor (n : Operad.SmallFinBijGroupoid) :
    PointedCGWH.{u, v} ⥤ OperatorCarrier.{u, v} :=
  originalFreeFunctor n ⋙ SymmetricRightModulePresentation.rightModuleOperatorEquivalence.functor

/-- The actual original right evaluation, through the same inverse equivalence, is native evaluation. -/
def operatorOriginalEvaluationIso (n : Operad.SmallFinBijGroupoid) :
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.inverse ⋙
        originalEvaluationFunctor n ≅
      EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (symmetricOperatorObj n) :=
  Functor.isoWhiskerLeft _ (evaluationIso n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SymmetricRightModulePresentation.rightModuleOperatorEquivalence.counitIso _ ≪≫
    Functor.leftUnitor _

/-- Compose the original standard right-free adjunction with the actual equivalence adjunction. -/
def operatorOriginalAdjunction (n : Operad.SmallFinBijGroupoid) :
    operatorOriginalFreeFunctor.{u, v} n ⊣
      EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (symmetricOperatorObj n) :=
  ((originalAdjunction n).comp
    SymmetricRightModulePresentation.rightModuleOperatorEquivalence.toAdjunction).ofNatIsoRight
      (operatorOriginalEvaluationIso n)

/-- The complete native free comparison is earned by the two actual free/evaluation adjunctions. -/
def operatorOriginalFreeIso (n : Operad.SmallFinBijGroupoid) :
    operatorOriginalFreeFunctor.{u, v} n ≅
      EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v}) (symmetricOperatorObj n) :=
  (operatorOriginalAdjunction n).leftAdjointUniq (EnrichedFunctorCat.Free.adjunction _)

/-- The same original realized free source preserves every supplied native closed-chain colimit. -/
theorem operatorOriginalSource_preservesClosedColimit
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (K.strictMap (Under.costar CGWH.point)) g) (n : Operad.SmallFinBijGroupoid)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ OperatorCarrier.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), closedInclusions
      ((EnrichedFunctorCat.evaluation (symmetricOperatorObj n)).map (E.map φ))) :
    PreservesColimit E (coyoneda.obj (Opposite.op ((operatorOriginalFreeFunctor n).obj Q))) := by
  let ev := EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (symmetricOperatorObj n)
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType ev :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  let _ : (E ⋙ ev).IsWellOrderContinuous := inferInstance
  let _ : PreservesColimit (E ⋙ ev) (coyoneda.obj (Opposite.op Q)) :=
    PointedCGWH.realizedGeneratorSource_preservesClosedColimit K hK g hg (E ⋙ ev) hE
  exact (operatorOriginalAdjunction n).preservesColimit_leftAdjointSource Q E

/-- Both original freely pointed realized families are cofibrations of their original native model. -/
theorem realizedGeneratorsCofibration
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) :
    K.strictMap (Under.costar CGWH.point) ≤ cofibrations PointedCGWH.{u, v} := by
  intro Q R g hg
  cases hg with
  | @map X Y f hf =>
      rcases (MorphismProperty.sup_iff _ _ _).mp (hK _ hf) with hB | hH
      · have h : PointedCGWH.realizedBoundaryInclusions ((Under.costar CGWH.point).map f) :=
          CGWH.realizedBoundaryInclusions.map_mem_strictMap (Under.costar CGWH.point) f hB
        have hl := PointedCGWH.realizedBoundaryInclusions.le_llp_rlp _ h
        have hRight : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
            trivialFibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.I_rlp
        rwa [hRight, trivialFibrations_llp] at hl
      · have h : PointedCGWH.realizedHornInclusions ((Under.costar CGWH.point).map f) :=
          CGWH.realizedHornInclusions.map_mem_strictMap (Under.costar CGWH.point) f hH
        have hl := PointedCGWH.realizedHornInclusions.le_llp_rlp _ h
        have hRight : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
            fibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.J_rlp
        rw [hRight, fibrations_llp] at hl
        exact hl.1

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Actual original standard RIGHT free realized maps are native cofibrations under the full Arrow comparison. -/
theorem operatorOriginalGeneratorCofibration
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (K.strictMap (Under.costar CGWH.point)) g) (n : Operad.SmallFinBijGroupoid) :
    cofibrations OperatorCarrier.{u, v} ((operatorOriginalFreeFunctor n).map g) := by
  let q := operatorOriginalFreeIso n
  let e : Arrow.mk ((operatorOriginalFreeFunctor n).map g) ≅
      Arrow.mk ((EnrichedFunctorCat.Free.functor (symmetricOperatorObj n)).map g) :=
    Arrow.isoMk (q.app Q) (q.app R) (q.hom.naturality g).symm
  exact ((cofibrations OperatorCarrier.{u, v}).arrow_mk_iso_iff e).mpr
    (HomotopicalAlgebra.EnrichedProjective.Native.freeAt_map_mem_cofibrations
      (symmetricOperatorObj n) g (realizedGeneratorsCofibration K hK _ hg))

end OriginalOperatorPresentation

end PointedCGWH.NativeFreeSourceSmallness
