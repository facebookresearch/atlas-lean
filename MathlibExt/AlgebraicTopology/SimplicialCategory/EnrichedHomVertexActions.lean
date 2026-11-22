/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentVertexFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
# Original full enriched Hom actions and their vertex dictionary

The supplied original unit-Hom map acts by the SAME enriched composition
on the entire original Hom simplicial set. The full parameter map is the
currying of that same composition. Its original zero vertex classifies
the actual full action map. Identity and composition retain every Hom
simplex; no Kan condition or weak-map conclusion is a premise.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomVertexActions

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The SAME full original Hom postcomposition action of a supplied original unit-Hom map. -/
def post (z : C) {x y : C} (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    (z ⟶[SSet.{u}] x) ⟶ (z ⟶[SSet.{u}] y) :=
  (ρ_ _).inv ≫ _ ◁ f ≫ eComp SSet.{u} z x y

/-- The actual entire parameter Hom maps to the full internal Hom by currying the SAME original composition. -/
def postParameter (z x y : C) :
    (x ⟶[SSet.{u}] y) ⟶ (ihom (z ⟶[SSet.{u}] x)).obj (z ⟶[SSet.{u}] y) :=
  MonoidalClosed.curry (eComp SSet.{u} z x y)

/-- The full original action's curry is exactly the supplied original unit map followed by the full parameter map. -/
theorem postParameter_unit (z : C) {x y : C} (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    f ≫ postParameter z x y = MonoidalClosed.curry' (post z f) := by
  unfold postParameter post MonoidalClosed.curry'
  rw [← MonoidalClosed.curry_natural_left]
  simp only [Iso.hom_inv_id_assoc]

/-- The SAME original parameter vertex classifies the actual full original Hom action. -/
theorem postParameter_vertex (z : C) {x y : C} (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    (postParameter z x y).app (op ⦋0⦌) (SSet.unitHomEquiv _ f) =
      SSet.ihomVertexEquiv (z ⟶[SSet.{u}] x) (z ⟶[SSet.{u}] y) (post z f) := by
  rw [SSet.ihomVertexEquiv_eq]
  change SSet.unitHomEquiv _ (f ≫ postParameter z x y) =
    SSet.unitHomEquiv _ (MonoidalClosed.curry' (post z f))
  exact congrArg (SSet.unitHomEquiv _) (postParameter_unit z f)

/-- The original unit identity acts as the SAME entire original Hom identity. -/
theorem post_identity (z x : C) : post z (eId SSet.{u} x) = 𝟙 (z ⟶[SSet.{u}] x) := by
  change eHomWhiskerLeft SSet.{u} (ForgetEnrichment.of SSet.{u} z)
    (ForgetEnrichment.homOf SSet.{u} (eId SSet.{u} x)) = _
  rw [ForgetEnrichment.homOf_eId]
  exact eHomWhiskerLeft_id SSet.{u} (ForgetEnrichment.of SSet.{u} z) (ForgetEnrichment.of SSet.{u} x)

/-- Whole original postcomposition actions preserve the supplied original unit-map composition. -/
theorem post_comp (z : C) {x y t : C}
    (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) (g : 𝟙_ SSet.{u} ⟶ (y ⟶[SSet.{u}] t)) :
    post z ((λ_ (𝟙_ SSet.{u})).inv ≫ (f ⊗ₘ g) ≫ eComp SSet.{u} x y t) =
      post z f ≫ post z g := by
  change eHomWhiskerLeft SSet.{u} (ForgetEnrichment.of SSet.{u} z)
    (ForgetEnrichment.homOf SSet.{u} ((λ_ _).inv ≫ (f ⊗ₘ g) ≫ eComp SSet.{u} x y t)) =
      eHomWhiskerLeft SSet.{u} (ForgetEnrichment.of SSet.{u} z) (ForgetEnrichment.homOf SSet.{u} f) ≫
        eHomWhiskerLeft SSet.{u} (ForgetEnrichment.of SSet.{u} z) (ForgetEnrichment.homOf SSet.{u} g)
  rw [ForgetEnrichment.homOf_comp]
  exact eHomWhiskerLeft_comp SSet.{u} (ForgetEnrichment.of SSet.{u} z)
    (ForgetEnrichment.homOf SSet.{u} f) (ForgetEnrichment.homOf SSet.{u} g)

end CategoryTheory.SimplicialEnrichment.EnrichedHomVertexActions
