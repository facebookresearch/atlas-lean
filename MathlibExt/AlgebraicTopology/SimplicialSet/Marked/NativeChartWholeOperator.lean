/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeChartOperatorEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanComposition
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentUnit

/-!
# Whole original cone-operator readback of native chart maps

The whole coherent base operator gives the actual equality of
restricted coefficient diagrams. The original native chart map is
therefore the full cone-image map followed by the original target
unit, with exactly that coefficient transport. This strengthens
individual component readbacks to the same whole enriched map for
all original faces and degeneracies.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization CategoryTheory.SimplicialEnrichment
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual opposite coherent index and original base simplex compose to the same original restricted
  base simplex. -/
theorem nativeChartIndex_comp_simplex (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap)).comp SSet.{u}
        (EnrichedFunctor.opposite (simplexInto B σ)) =
      EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)) := by
  change EnrichedFunctor.opposite (coherentSimplexMap f ≫ simplexInto B σ) = _
  exact congrArg (fun a => EnrichedFunctor.opposite a) (simplexInto_operator B f σ)

/-- Whole native base restriction and original index restriction compose to precisely the original
  restricted-simplex functor. -/
theorem nativeChartBase_restriction_comp (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ)) ⋙
        enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap)) =
      enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ))) :=
  (enrichedDiagramRestrict_comp (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))
    (EnrichedFunctor.opposite (simplexInto B σ))).trans
    (congrArg (fun a : EnrichedFunctor SSet.{u} (Index.{u} n)ᵒᵖ (realization B)ᵒᵖ => enrichedDiagramRestrict a)
      (nativeChartIndex_comp_simplex B f σ))

/-- The whole original operator has exactly the actual restricted coefficient target of its native source chart. -/
theorem nativeChartWholeOperatorTargetEq (B : SSet.{u}) {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))).obj
        ((enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj (nativeSimplexChart B m σ)) =
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))).obj
        (nativeSimplexChart B m σ) :=
  congrArg (fun a : EnrichedDiagram (realization B)ᵒᵖ ⥤ EnrichedDiagram (Index.{u} n)ᵒᵖ =>
    a.obj (nativeSimplexChart B m σ)) (nativeChartBase_restriction_comp B f σ)

/-- The actual native chart restriction reads the whole original cone operator followed by the original
  target unit and its genuine coefficient-target transport. -/
theorem nativeChartRestriction_whole_operator (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    (coneOperator f.toOrderHom.uliftMap ≫
        (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))).map
          (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram m))) ≫
        eqToHom (nativeChartWholeOperatorTargetEq B f σ) =
      EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
        (coneDiagram n) (nativeSimplexChart B m σ) (nativeSimplexChartRestriction B f σ) := by
  let F := nativeSimplexChart B m σ
  let src := EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
    (coneDiagram n) F (nativeSimplexChartRestriction B f σ)
  let par := EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram m)
  let r := enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))
  let a := coneOperator f.toOrderHom.uliftMap ≫ r.map par
  have hl := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B n (B.map f.op σ) F
    (nativeSimplexChartRestriction B f σ))
  have hr := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B m σ F (𝟙 _))
  have hx : (⟨simplexInto B (B.map f.op σ), src⟩ : UnstraighteningSimplex F n) =
      (⟨simplexInto B σ, par⟩ : UnstraighteningSimplex F m).pull f.toOrderHom.uliftMap :=
    hl.symm.trans ((nativeChartRestriction_un_raw B f σ).trans
      (congrArg (fun b : UnstraighteningSimplex F m => b.pull f.toOrderHom.uliftMap) hr))
  let read := fun b : UnstraighteningSimplex F n =>
    (⟨b.base, b.sectionMap⟩ : Σ s : EnrichedFunctor SSet.{u} (Index.{u} n) (realization B),
      coneDiagram n ⟶ simplexCoefficient F s)
  have hh : HEq a src := (Sigma.mk.inj (congrArg read hx)).2.symm
  have transport {G H : EnrichedDiagram (Index.{u} n)ᵒᵖ} (h : G = H)
      (a : coneDiagram n ⟶ G) (b : coneDiagram n ⟶ H) (hab : HEq a b) : a ≫ eqToHom h = b := by
    cases h
    exact (Category.comp_id a).trans (eq_of_heq hab)
  exact transport (nativeChartWholeOperatorTargetEq B f σ) a src hh

end SSet.Marked
