/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardUniversalProperty

/-! # The arbitrary-label enriched pushforward functor

The source functor followed by the presented unit defines its
Extension. The generator universal property gives both
ordinary functor laws and the full source and target naturality equations.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward

variable {A O : Type u} (a : A → O)

private theorem restriction_map_id (D : FixedObjects O) :
    LabelRestriction.map a (𝟙 D) = 𝟙 (LabelRestriction.object a D) :=
  (LabelRestriction.functor a).map_id D

private theorem restriction_map_comp {D E H : FixedObjects O} (F : D ⟶ E) (G : E ⟶ H) :
    LabelRestriction.map a (F ≫ G) = LabelRestriction.map a F ≫ LabelRestriction.map a G :=
  (LabelRestriction.functor a).map_comp F G

/-- Push forward the source functor by the presented extension. -/
def map {C E : FixedObjects A} (F : C ⟶ E) : object a C ⟶ object a E :=
  desc a C (F ≫ unit a E)

/-- The pushed-forward map retains the functor after the same unit. -/
theorem unit_naturality {C E : FixedObjects A} (F : C ⟶ E) :
    unit a C ≫ LabelRestriction.map a (map a F) = F ≫ unit a E :=
  unit_desc a C (F ≫ unit a E)

/-- The left functor on all enrichments with the prescribed source labels. -/
def functor : FixedObjects A ⥤ FixedObjects O where
  obj := object a
  map := map a
  map_id C := by
    apply (homEquiv a C (object a C)).injective
    rw [homEquiv_apply, homEquiv_apply, unit_naturality]
    rw [restriction_map_id, Category.id_comp, Category.comp_id]
  map_comp {C E H} F G := by
    apply (homEquiv a _ _).injective
    rw [homEquiv_apply, homEquiv_apply, unit_naturality]
    rw [restriction_map_comp]
    rw [← Category.assoc, unit_naturality]
    exact (Category.assoc F G (unit a H)).trans
      ((congrArg (fun k => F ≫ k) (unit_naturality a G).symm).trans
        (Category.assoc F (unit a E) (LabelRestriction.map a (map a G))).symm)

/-- Hom naturality in the source enrichment. -/
theorem homEquiv_source {C E : FixedObjects A} {D : FixedObjects O}
    (F : C ⟶ E) (G : object a E ⟶ D) :
    homEquiv a C D (map a F ≫ G) = F ≫ homEquiv a E D G := by
  rw [homEquiv_apply, homEquiv_apply, restriction_map_comp, ← Category.assoc, unit_naturality]
  exact Category.assoc _ _ _

/-- Hom naturality in the target enrichment. -/
theorem homEquiv_target {C : FixedObjects A} {D E : FixedObjects O}
    (F : object a C ⟶ D) (G : D ⟶ E) :
    homEquiv a C E (F ≫ G) = homEquiv a C D F ≫ LabelRestriction.map a G := by
  rw [homEquiv_apply, homEquiv_apply, restriction_map_comp]
  exact (Category.assoc _ _ _).symm

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
