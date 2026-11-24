/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexing

/-!
# Exact original nested object reindexing and full projections

Two consecutive original label maps give the literal same enrichment
as their complete composite. All original Homs, units and compositions
are retained, and both entire identity-Hom projections compose exactly.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.CarrierReindexing
open FixedObjects

variable {A O : Type u} (D : Carrier.{u}) (a : O → D) (b : A → O)

/-- Nested original reindexing has the SAME literal individual labels and whole original
enrichment. -/
theorem nested_object :
    object (object D a).val (fun s => vertex (object D a) (b s)) =
      object D (fun s => a (b s)) := rfl

/-- Both whole original identity-Hom projections compose to the SAME complete original
object function. -/
theorem nested_projection :
    toTarget (object D a).val (fun s => vertex (object D a) (b s)) ≫ toTarget D a =
      toTarget D (fun s => a (b s)) := by
  apply EnrichedFunctor.ext SSet.{u} (fun _ => rfl)
  intro x y
  change (𝟙 _ ≫ 𝟙 _) ≫ eqToHom rfl = 𝟙 _
  simp only [eqToHom_refl, Category.id_comp]

end CategoryTheory.SimplicialEnrichment.CarrierReindexing
