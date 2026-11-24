/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelCarrierUnit

/-!
# The SAME entire original label-pushforward carrier unit is natural

The existing original fixed-label unit naturality is projected through
its genuine full reindexed carrier maps. Every original coefficient and
both original object functions are retained.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward

variable {A O : Type u} (a : A → O) {C D : FixedObjects A}

/-- The SAME full original carrier-unit square for every original fixed-label enriched functor. -/
theorem carrierUnit_naturality (F : C ⟶ D) :
    carrierUnit a C ≫ (map a F).val = F.val ≫ carrierUnit a D := by
  have h := congrArg (fun G : C ⟶ LabelRestriction.object a (object a D) =>
    G.val ≫ CarrierReindexing.toTarget (object a D).val (fun s => vertex (object a D) (a s)))
      (unit_naturality a F)
  exact (carrierUnit_projection a C (map a F)).symm.trans (h.trans (Category.assoc _ _ _))

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
