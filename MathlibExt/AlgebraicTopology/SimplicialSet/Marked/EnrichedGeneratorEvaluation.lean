/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeSmallObject
import MathlibExt.CategoryTheory.SmallObject.Image

/-!
# Actual evaluation of full marked enriched free-cell left classes

The whole free arrow evaluates to its original maximal Hom tensor.
Genuine source presentability supplies its native small-object cardinal.
The original evaluation preserves those pointwise colimits, so the
actual mapped cell endpoints and their retracts lie in the specified
closed coefficient class. No target model or left-acyclicity outcome is
an input to the coherent-base application.
-/

noncomputable section
universe u v
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C] [Small.{u} C]
    (P Q : MorphismProperty Marked.{u}) [P.IsSmall.{u}] [Q.RespectsIso]
    (hTensor : ∀ c x : C, ∀ {A D : Marked.{u}} (f : A ⟶ D),
      P f → Q (prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) f))

include hTensor

omit [Small.{u} C] [P.IsSmall.{u}] in
/-- Each entire free generator evaluates to its same original maximal Hom-tensor arrow. -/
theorem enrichedFreeGenerators_evaluation_le (x : C) :
    enrichedFreeGenerators C P ≤ Q.inverseImage (enrichedDiagramEvaluation C x) := by
  intro F G f hf
  let L := fun c : C => enrichedFreeDiagramFunctor C c
  let R := enrichedDiagramEvaluation C x
  obtain ⟨q, hq⟩ := (adjointFamilyGenerators_iff L P f).mp hf
  have hActual : Q (R.map ((L q.1).map q.2.1.hom)) := hTensor q.1 x q.2.1.hom q.2.2
  have hArrow := congrArg (fun a => R.mapArrow.obj a) hq
  exact (Q.arrow_mk_iso_iff (eqToIso hArrow)).mpr hActual

/-- Genuine source smallness, exact evaluation colimits and actual coefficient closure prove the full
  original free-cell left-class evaluation law. -/
theorem enrichedFreeGenerators_left_evaluation_le
    [Q.IsStableUnderRetracts] [Q.IsStableUnderCoproducts.{u}]
    [Q.IsStableUnderCobaseChange] [Q.IsStableUnderTransfiniteComposition.{u}] (x : C) :
    (enrichedFreeGenerators C P).rlp.llp ≤ Q.inverseImage (enrichedDiagramEvaluation C x) := by
  let _ : (enrichedFreeGenerators C P).HasSmallObjectArgument.{u} :=
    enrichedFreeGenerators_hasSmallObjectArgument C P
  obtain ⟨κ, hκ, hb, hI⟩ := (inferInstance :
    (enrichedFreeGenerators C P).HasSmallObjectArgument.{u}).exists_cardinal
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hb
  let _ : (enrichedFreeGenerators C P).IsCardinalForSmallObjectArgument κ := hI
  let _ : PreservesColimitsOfSize.{u, u} (enrichedDiagramEvaluation C x) :=
    enrichedEvaluation_preservesColimits C x
  let _ : PreservesWellOrderContinuousOfShape κ.ord.ToType (enrichedDiagramEvaluation C x) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  exact rlp_llp_le_inverseImage_of_cardinal_closure (enrichedFreeGenerators C P) Q
    (enrichedDiagramEvaluation C x) κ (enrichedFreeGenerators_evaluation_le C P Q hTensor x)

end SSet.Marked
