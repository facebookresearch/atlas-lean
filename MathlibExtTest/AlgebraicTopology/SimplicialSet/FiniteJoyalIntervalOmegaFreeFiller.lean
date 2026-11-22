/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFreeFiller

/-!
# Actual stages, unit and pointwise colimit of the chosen omega datum
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits SSet.joyalInterval

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFreeFiller

/-- The chosen unit retains its full all-map naturality equation. -/
theorem unit_naturality {X Y : SSet.{u}} (m : X ⟶ Y) :
    m ≫ auxiliaryOmegaFreeFillerUnit.{u}.app Y =
      auxiliaryOmegaFreeFillerUnit.{u}.app X ≫ auxiliaryOmegaFreeFiller.{u}.map m :=
  auxiliaryOmegaFreeFillerUnit.{u}.naturality m

/-- Every original stage inclusion is an actual natural transformation. -/
theorem stage_naturality {X Y : SSet.{u}} (m : X ⟶ Y) (n : ℕ) :
    (auxiliaryOmegaStages.{u}.obj n).map m ≫ (colimit.ι auxiliaryOmegaStages.{u} n).app Y =
      (colimit.ι auxiliaryOmegaStages.{u} n).app X ≫ auxiliaryOmegaFreeFiller.{u}.map m :=
  (colimit.ι auxiliaryOmegaStages.{u} n).naturality m

/-- A successor inclusion and the original whiskered unit keep both defining equations. -/
theorem successor_equations (X : SSet.{u}) (n : ℕ) :
    (auxiliaryOmegaStages.{u}.map (homOfLE (Nat.le_succ n))).app X ≫
        (colimit.ι auxiliaryOmegaStages.{u} (n + 1)).app X =
      (colimit.ι auxiliaryOmegaStages.{u} n).app X ∧
    (auxiliaryOmegaStages.{u}.map (homOfLE (Nat.le_succ n))).app X ≫
        (auxiliaryOmegaStagesSuccIso.{u} n).hom.app X =
      auxiliaryFreeFillerUnit.app ((auxiliaryOmegaStages.{u}.obj n).obj X) := by
  constructor
  · exact congrArg (fun m => m.app X) (colimit.w auxiliaryOmegaStages.{u} (homOfLE (Nat.le_succ n)))
  · exact congrArg (fun m => m.app X) (auxiliaryOmegaStages_map_succ.{u} n)

/-- The unit uses the actual zero-stage isomorphism and original inclusion. -/
theorem zero_unit (X : SSet.{u}) :
    auxiliaryOmegaFreeFillerUnit.{u}.app X =
      auxiliaryOmegaStagesZeroIso.{u}.inv.app X ≫ (colimit.ι auxiliaryOmegaStages.{u} 0).app X :=
  congrArg (fun m => m.app X) auxiliaryOmegaFreeFillerUnit_eq.{u}

/-- Evaluation gives the same pointwise colimit, with both actual stage equations. -/
theorem pointwise_colimit (X : SSet.{u}) :
    ∃ e : auxiliaryOmegaFreeFiller.{u}.obj X ≅
        colimit (auxiliaryOmegaStages.{u} ⋙ (evaluation _ _).obj X),
      (∀ n, (colimit.ι auxiliaryOmegaStages.{u} n).app X ≫ e.hom =
        colimit.ι (auxiliaryOmegaStages.{u} ⋙ (evaluation _ _).obj X) n) ∧
      (∀ n, colimit.ι (auxiliaryOmegaStages.{u} ⋙ (evaluation _ _).obj X) n ≫ e.inv =
        (colimit.ι auxiliaryOmegaStages.{u} n).app X) := by
  refine ⟨colimitObjIsoColimitCompEvaluation auxiliaryOmegaStages.{u} X, ?_, ?_⟩
  · exact fun n => colimitObjIsoColimitCompEvaluation_ι_app_hom auxiliaryOmegaStages.{u} n X
  · exact fun n => colimitObjIsoColimitCompEvaluation_ι_inv auxiliaryOmegaStages.{u} n X

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFreeFiller
