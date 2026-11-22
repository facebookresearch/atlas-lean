/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFilteredColimits

/-!
# Actual filtered-colimit comparison and the selected omega transformations
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits SSet.joyalInterval

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFilteredColimits

variable {J : Type u} [SmallCategory J] (F : J ⥤ SSet.{u})

/-- The original comparison is invertible and retains every original diagram inclusion. -/
theorem comparison [IsFiltered J] :
    IsIso (colimit.post F auxiliaryOmegaFreeFiller.{u}) ∧
      ∀ k, colimit.ι (F ⋙ auxiliaryOmegaFreeFiller.{u}) k ≫
        colimit.post F auxiliaryOmegaFreeFiller.{u} =
          auxiliaryOmegaFreeFiller.map (colimit.ι F k) :=
  ⟨inferInstance, fun k => colimit.ι_post F auxiliaryOmegaFreeFiller.{u} k⟩

/-- The actual selected omega unit is natural across the same canonical comparison. -/
theorem unit_restriction (k : J) :
    auxiliaryOmegaFreeFillerUnit.app (F.obj k) ≫
      colimit.ι (F ⋙ auxiliaryOmegaFreeFiller.{u}) k ≫
        colimit.post F auxiliaryOmegaFreeFiller.{u} =
          colimit.ι F k ≫ auxiliaryOmegaFreeFillerUnit.app (colimit F) := by
  rw [colimit.ι_post]
  exact (auxiliaryOmegaFreeFillerUnit.naturality (colimit.ι F k)).symm

/-- Every actual finite-stage inclusion retains its full naturality under the comparison. -/
theorem stage_restriction (k : J) (n : ℕ) :
    (colimit.ι auxiliaryOmegaStages.{u} n).app (F.obj k) ≫
      colimit.ι (F ⋙ auxiliaryOmegaFreeFiller.{u}) k ≫
        colimit.post F auxiliaryOmegaFreeFiller.{u} =
          (auxiliaryOmegaStages.obj n).map (colimit.ι F k) ≫
            (colimit.ι auxiliaryOmegaStages.{u} n).app (colimit F) := by
  let ι : auxiliaryOmegaStages.{u}.obj n ⟶ auxiliaryOmegaFreeFiller.{u} :=
    colimit.ι auxiliaryOmegaStages.{u} n
  change ι.app (F.obj k) ≫ colimit.ι (F ⋙ auxiliaryOmegaFreeFiller.{u}) k ≫
    colimit.post F auxiliaryOmegaFreeFiller.{u} =
      (auxiliaryOmegaStages.{u}.obj n).map (colimit.ι F k) ≫ ι.app (colimit F)
  rw [colimit.ι_post]
  exact (ι.naturality (colimit.ι F k)).symm

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFilteredColimits
