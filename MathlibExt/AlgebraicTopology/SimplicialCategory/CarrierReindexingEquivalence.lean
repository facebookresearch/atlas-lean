/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexing
import MathlibExt.CategoryTheory.Enriched.ReindexingEquivalence

/-!
# The SAME carrier reindexing projection is an actual full isomorphism

A supplied equivalence of individual original object types gives the
genuine inverse of the existing projection. Both whole enriched maps
and all original full Hom maps are retained.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.CarrierReindexing

variable {O : Type u} (D : Carrier.{u}) (e : O ≃ D)

/-- The SAME original full inverse of the canonical object-equivalence projection. -/
def equivalenceInverse : D ⟶ (object D e).val :=
  EnrichedCategory.reindexInverse SSet.{u} e

/-- Its actual individual object map is the SAME original inverse equivalence. -/
theorem equivalenceInverse_obj (x : D) : (equivalenceInverse D e).obj x = e.symm x := rfl

/-- Both entire original enriched functors compose to the SAME reindexed identity. -/
theorem projection_equivalenceInverse : toTarget D e ≫ equivalenceInverse D e = 𝟙 (object D e).val :=
  EnrichedCategory.reindexProjection_inverse SSet.{u} e

/-- Both entire original enriched functors compose to the SAME original identity. -/
theorem equivalenceInverse_projection : equivalenceInverse D e ≫ toTarget D e = 𝟙 D :=
  EnrichedCategory.reindexInverse_projection SSet.{u} e

/-- The actual original projection and full inverse form a genuine carrier isomorphism. -/
def equivalenceIso : (object D e).val ≅ D where
  hom := toTarget D e
  inv := equivalenceInverse D e
  hom_inv_id := projection_equivalenceInverse D e
  inv_hom_id := equivalenceInverse_projection D e

end CategoryTheory.SimplicialEnrichment.CarrierReindexing
