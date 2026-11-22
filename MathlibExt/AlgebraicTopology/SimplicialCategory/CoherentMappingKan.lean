/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomMapping
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveUniverseQuasicategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceKanW

/-!
# Actual Kan right mapping spaces of original locally Kan enrichments

The constructed coherent nerve is a quasicategory under genuine Kan
hypotheses on each original Hom. The existing right mapping-space horn
proof then gives its actual Kan mapping objects. Independent original
object and Hom universes are retained by the explicit common-universe
lift. This proves target fibrancy, not the comparison weak equivalence.
-/

noncomputable section
universe u v w
open CategoryTheory

namespace CategoryTheory.CoherentRealization.MappingKan
open SimplicialEnrichment HomSimplexEndpoints

/-- The actual original coherent right mapping space is Kan under genuine original locally Kan Hom hypotheses. -/
theorem rightMappingKan (C : Carrier.{u})
    (hKan : ∀ a b : C, SSet.KanComplex (a ⟶[SSet.{u}] b)) (x y : C) :
    SSet.KanComplex (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) := by
  let _ : SSet.Quasicategory (coherentNerveFunctor.obj C) := coherentNerve_quasicategory C hKan
  exact SSet.kanComplex_mappingSpaceRight _ _ _

/-- The same actual right mapping object is Kan for independent original object and Hom universes, without
  quotienting its supplied objects. -/
theorem liftedRightMappingKan (C : Type v) [EnrichedCategory SSet.{u} C]
    (hKan : ∀ a b : C, SSet.KanComplex (a ⟶[SSet.{u}] b)) (x y : C) :
    SSet.KanComplex (SSet.mappingSpaceRight (coherentNerveFunctor.obj (liftedCarrier.{u, v, w} C))
      (HomSimplexEndpoints.vertex (ULift.up x : liftedCarrier.{u, v, w} C))
      (HomSimplexEndpoints.vertex (ULift.up y : liftedCarrier.{u, v, w} C))) :=
  rightMappingKan (liftedCarrier.{u, v, w} C) (liftedCarrier_homKan C hKan) _ _

end CategoryTheory.CoherentRealization.MappingKan
