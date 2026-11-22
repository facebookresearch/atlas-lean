/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentSharpIntervalRootEndpoint
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSharpRootMarkPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootCoordinateScalarFreeCells

/-!
# The SAME full original sharp interval is its genuine weak endpoint pushout

The actual original positive root enters the SAME sharp whole interval
through its original endpoint coefficient trivial cofibration. Its
genuine free map and unchanged original positive and sharp root free
legs retain the complete enriched square. At root both whole free legs
are marked self-path Isos; above root both free values are initial and
the entire original positive-to-sharp value is an Iso. Actual marked
evaluation proves the full enriched weak endpoint attachment.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq
  coefficientMarkedModelCategory

/-- The entire original positive interval cone enters the SAME sharp interval by its full original inclusion and
marking map. -/
def coneSharpEndpointDiagramMap : coneAfterDiagram (⊥ : Vertex.{u} 1) ⟶ sharpConeDiagram 1 :=
  coneAfterDiagramInclusion (⊥ : Vertex.{u} 1) ≫ coneSharp 1

/-- The SAME actual original endpoint coefficient cell is freed at the original interval root. -/
def coneSharpEndpointFreeMap :
    enrichedFreeDiagram (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (coneAfterWeight (⊥ : Vertex.{u} 1) ⊥) ⟶
    enrichedFreeDiagram (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) :=
  (enrichedFreeDiagramFunctor (Index.{u} 1)ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))).map coneSharpEndpointRootCell

/-- The actual original endpoint free map retains precisely its whole original positive and sharp root marking
factors. -/
theorem coneSharpEndpointFreeMap_factors :
    coneSharpEndpointFreeMap.{u} = coneRootBoundaryFreeMap 1 ≫ coneSharpRootMarkFreeMap :=
  (enrichedFreeDiagramFunctor (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))).map_comp
    (coneAfterInclusion (⊥ : Vertex.{u} 1) ⊥) coneSharpRootMarkCell

/-- The SAME whole original endpoint free square follows from its actual original positive and sharp marking unit
squares. -/
theorem coneSharpEndpoint_free_condition :
    coneSharpEndpointFreeMap.{u} ≫ coneSharpRootFreeLeg = coneAfterRootFreeMap 1 ≫ coneSharpEndpointDiagramMap := by
  have h₀ := congrArg (fun f => f ≫ coneSharpRootFreeLeg) coneSharpEndpointFreeMap_factors.{u}
  have h₁ := Category.assoc (coneRootBoundaryFreeMap.{u} 1) coneSharpRootMarkFreeMap coneSharpRootFreeLeg
  have h₂ := congrArg (fun f => coneRootBoundaryFreeMap 1 ≫ f) coneSharpRootMark_condition.{u}
  have h₃ := (Category.assoc (coneRootBoundaryFreeMap.{u} 1) (coneRootFreeMap 1) (coneSharp 1)).symm
  have h₄ := congrArg (fun f => f ≫ coneSharp 1) (coneRootCell_condition.{u} 1)
  have h₅ := Category.assoc (coneAfterRootFreeMap.{u} 1) (coneAfterDiagramInclusion (⊥ : Vertex.{u} 1)) (coneSharp 1)
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))))

/-- The SAME original endpoint free map has the genuine weak projective left class through the actual coefficient
WFS. -/
theorem coneSharpEndpointFreeMap_projectiveWeakLeft :
    (enrichedFreeGenerators (Index.{u} 1)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp coneSharpEndpointFreeMap.{u} := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  have hleft : coefficientGeneratingWeakMonos.rlp.llp coneSharpEndpointRootCell.{u} := by
    rw [coefficientGeneratingWeakMonos_rlp, fibrations_llp]
    exact coneSharpEndpointRootCell_trivialCofibration
  intro F G p hp
  exact (Adjunction.hasLiftingProperty_iff (enrichedFreeEvaluationAdjunction (Index.{u} 1)ᵒᵖ c)
    coneSharpEndpointRootCell p).mpr
      (hleft (p.app c) ((enrichedFreeGenerators_rlp_iff (Index.{u} 1)ᵒᵖ coefficientGeneratingWeakMonos p).mp hp c))

/-- Each entire original marked interval coefficient retains the SAME full positive-to-sharp endpoint square. -/
def coneSharpEndpointComponentCocone (i : Vertex.{u} 1) :
    PushoutCocone (coneSharpEndpointFreeMap.app (op (SimplicialThickening.mk i)))
      ((coneAfterRootFreeMap 1).app (op (SimplicialThickening.mk i))) :=
  PushoutCocone.mk (coneSharpRootFreeLeg.app (op (SimplicialThickening.mk i)))
    (coneSharpEndpointDiagramMap.app (op (SimplicialThickening.mk i)))
      (congrArg (fun f => f.app (op (SimplicialThickening.mk i))) coneSharpEndpoint_free_condition)

/-- Every SAME original full marked coefficient is the actual pushout of that original endpoint free cell. -/
def coneSharpEndpointComponentIsColimit (i : Vertex.{u} 1) :
    IsColimit (coneSharpEndpointComponentCocone i) := by
  let c := op (SimplicialThickening.mk i)
  let root : Vertex.{u} 1 := ⊥
  let f := coneSharpEndpointFreeMap.app c
  let g := (coneAfterRootFreeMap 1).app c
  let l := coneSharpRootFreeLeg.app c
  let r := coneSharpEndpointDiagramMap.app c
  have hw : CommSq f g l r := ⟨congrArg (fun x => x.app c) coneSharpEndpoint_free_condition⟩
  have hp : IsPushout f g l r := by
    by_cases hi : root < i
    · let ha := coherentFreeBeyondIsInitial hi (coneAfterWeight root root)
      let hb := coherentFreeBeyondIsInitial hi (max (coneWeight root).toSSet)
      let e := ha.uniqueUpToIso hb
      have he : f = e.hom := ha.hom_ext _ _
      let _ : IsIso f := Eq.mp (congrArg (fun f => IsIso f) he.symm) e.isIso_hom
      let _ : IsIso (coneAfterInclusion i root) := (coneAfterAboveIso hi).isIso_hom
      let _ : IsIso ((coneSharp 1).app c) := coneSharpInterval_positive_isIso i hi
      let ea := coneAfterAboveIso hi
      let eb := asIso ((coneSharp 1).app c)
      have hr : (ea ≪≫ eb).hom = r := rfl
      let _ : IsIso r := Eq.mp (congrArg (fun f => IsIso f) hr) (ea ≪≫ eb).isIso_hom
      exact IsPushout.of_horiz_isIso hw
    · have he : i = root := le_antisymm (le_of_not_gt hi) bot_le
      subst i
      let _ : IsIso g := coneAfterRootFreeMap_isIso_self 1
      let _ : IsIso l := coneSharpRootFreeLeg_isIso_self
      exact IsPushout.of_vert_isIso hw
  exact hp.isColimit

/-- The SAME complete original sharp interval has its whole original endpoint free cocone. -/
def coneSharpEndpointEnrichedCocone : PushoutCocone coneSharpEndpointFreeMap.{u} (coneAfterRootFreeMap 1) :=
  PushoutCocone.mk coneSharpRootFreeLeg coneSharpEndpointDiagramMap coneSharpEndpoint_free_condition

/-- Actual marked evaluation proves the genuine FULL original sharp interval enriched endpoint pushout. -/
def coneSharpEndpointEnrichedIsColimit : IsColimit coneSharpEndpointEnrichedCocone.{u} := by
  apply enrichedIsColimitOfEvaluation
  intro i
  refine (IsColimit.equivOfNatIsoOfIso
    (spanCompIso (enrichedDiagramEvaluation (Index.{u} 1)ᵒᵖ i) coneSharpEndpointFreeMap (coneAfterRootFreeMap 1))
    ((enrichedDiagramEvaluation (Index.{u} 1)ᵒᵖ i).mapCocone coneSharpEndpointEnrichedCocone)
    (coneSharpEndpointComponentCocone i.unop.as)
      (WalkingSpan.ext (Iso.refl _) ?_ ?_)).symm (coneSharpEndpointComponentIsColimit i.unop.as)
  · exact Category.comp_id _
  · exact Category.comp_id _

/-- The SAME entire original positive-to-sharp interval attachment has the actual weak projective left class through
its full original enriched pushout. -/
theorem coneSharpEndpointDiagramMap_projectiveWeakLeft :
    (enrichedFreeGenerators (Index.{u} 1)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp coneSharpEndpointDiagramMap.{u} :=
  MorphismProperty.of_isPushout (IsPushout.of_isColimit coneSharpEndpointEnrichedIsColimit).flip
    coneSharpEndpointFreeMap_projectiveWeakLeft

end SSet.Marked.CoherentWeight
