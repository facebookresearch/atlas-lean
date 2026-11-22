/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OrdinaryCoherentNerveMap

/-!
# Full postcomposition readback for the actual ordinary-to-coherent adapter
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OrdinaryNerveMap
open SimplicialEnrichment

/-- The canonical ordinary adapter preserves actual full enriched target postcomposition on every simplex. -/
theorem simplex_postcompose {C D : Carrier.{u}} {n : SimplexCategory}
    (F : Fin (n.len + 1) ⥤ ForgetEnrichment SSet.{u} C) (G : C ⟶ D) :
    simplex (F ⋙ G.forget) = (simplex F).comp SSet.{u} G := by
  refine EnrichedFunctor.ext SSet.{u} (fun _ => rfl) ?_
  intro i j
  change (simplex (F ⋙ G.forget)).map i j ≫ 𝟙 _ = (simplex F).map i j ≫ G.map _ _
  rw [Category.comp_id]
  ext q a
  rfl

/-- The SAME complete ordinary nerve map commutes with each genuine enriched model projection. -/
@[reassoc] theorem map_postcompose {A : Type v} [Category.{w} A]
    (C D : Carrier.{max v w}) (F : A ⥤ ForgetEnrichment SSet.{max v w} C) (G : C ⟶ D) :
    map C F ≫ coherentNerveFunctor.map G = map D (F ⋙ G.forget) := by
  ext q a
  exact (simplex_postcompose (a ⋙ F) G).symm

end CategoryTheory.CoherentRealization.OrdinaryNerveMap
