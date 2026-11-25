/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanAdjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of actual native marked enriched left extensions

Whole restriction along two original enriched functors is restriction
along their actual composite. The existing composed adjunction and
canonical adjoint uniqueness give the corresponding whole left-
extension isomorphism, with its original unit and counit equations.
No model structure or left-extension outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C D : Type u} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    {E : Type v} [EnrichedCategory SSet.{u} E]
    (j : EnrichedFunctor SSet.{u} C D) (k : EnrichedFunctor SSet.{u} D E)

/-- The actual whole marked restriction functor composes along the original enriched index composite. -/
theorem enrichedDiagramRestrict_comp :
    enrichedDiagramRestrict k ⋙ enrichedDiagramRestrict j =
      enrichedDiagramRestrict (j.comp SSet.{u} k) := rfl

/-- The two actual native left-extension adjunctions compose to the same original composite restriction. -/
def enrichedLeftKanCompositionAdjunction :
    EnrichedLeftKan.leftExtension j ⋙ EnrichedLeftKan.leftExtension k ⊣
      enrichedDiagramRestrict (j.comp SSet.{u} k) :=
  ((EnrichedLeftKan.adjunction j).comp (EnrichedLeftKan.adjunction k)).ofNatIsoRight
    (eqToIso (enrichedDiagramRestrict_comp j k))

/-- Canonical uniqueness identifies the two actual native left extensions with the original composite left extension. -/
def enrichedLeftKanCompositionNatIso :
    EnrichedLeftKan.leftExtension j ⋙ EnrichedLeftKan.leftExtension k ≅
      EnrichedLeftKan.leftExtension (j.comp SSet.{u} k) :=
  Adjunction.leftAdjointUniq (enrichedLeftKanCompositionAdjunction j k)
    (EnrichedLeftKan.adjunction (j.comp SSet.{u} k))

/-- The whole forward composite comparison is the actual transpose of the original composite unit. -/
theorem enrichedLeftKanComposition_hom_unit (W : EnrichedDiagram C) :
    (enrichedLeftKanCompositionAdjunction j k).homEquiv _ _
      ((enrichedLeftKanCompositionNatIso j k).hom.app W) =
        (EnrichedLeftKan.adjunction (j.comp SSet.{u} k)).unit.app W :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ W

/-- The whole original unit square uses the actual composite restriction and comparison map. -/
theorem enrichedLeftKanComposition_unit_square (W : EnrichedDiagram C) :
    (enrichedLeftKanCompositionAdjunction j k).unit.app W ≫
      (enrichedDiagramRestrict (j.comp SSet.{u} k)).map ((enrichedLeftKanCompositionNatIso j k).hom.app W) =
        (EnrichedLeftKan.adjunction (j.comp SSet.{u} k)).unit.app W :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ W

/-- The whole original counit square retains the actual composed evaluation and left-extension counits. -/
theorem enrichedLeftKanComposition_counit_square (F : EnrichedDiagram E) :
    (enrichedLeftKanCompositionNatIso j k).hom.app
        ((enrichedDiagramRestrict (j.comp SSet.{u} k)).obj F) ≫
      (EnrichedLeftKan.adjunction (j.comp SSet.{u} k)).counit.app F =
        (enrichedLeftKanCompositionAdjunction j k).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ F

end SSet.Marked
