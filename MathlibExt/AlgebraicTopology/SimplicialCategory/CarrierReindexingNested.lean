/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexing

/-!
# Exact nested object reindexing and full projections

Two consecutive label maps give the literal same enrichment
as their complete composite. All Homs, units and compositions
are retained, and both identityHom projections compose exactly.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.CarrierReindexing
open FixedObjects

variable {A O : Type u} (D : Carrier.{u}) (a : O → D) (b : A → O)

/-- Nested reindexing has the same literal individual labels and 
enrichment. -/
theorem nested_object :
    object (object D a).val (fun s => vertex (object D a) (b s)) =
      object D (fun s => a (b s)) := rfl

/-- Both identityHom projections compose to the same complete 
object function. -/
theorem nested_projection :
    toTarget (object D a).val (fun s => vertex (object D a) (b s)) ≫ toTarget D a =
      toTarget D (fun s => a (b s)) := by
  apply EnrichedFunctor.ext SSet.{u} (fun _ => rfl)
  intro x y
  change (𝟙 _ ≫ 𝟙 _) ≫ eqToHom rfl = 𝟙 _
  simp only [eqToHom_refl, Category.id_comp]

end CategoryTheory.SimplicialEnrichment.CarrierReindexing
