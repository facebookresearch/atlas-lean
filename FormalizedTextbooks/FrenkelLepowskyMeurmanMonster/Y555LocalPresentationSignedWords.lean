/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact signed-word evaluation for the independent local presentation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCoxeterRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- In the actual local quotient, the canonical quotient map is the lift of its generators. -/
theorem y322Quotient_eq_generator_lift :
    PresentedGroup.mk y322Relations =
      FreeGroup.lift (fun v => (PresentedGroup.of v : Y322Presentation)) := by
  apply FreeGroup.ext_hom
  intro v
  rfl

/-- Signed letters evaluate as their positive generator, using the genuine defining squares. -/
theorem y322SignedWord_value (w : List (Fin 8 × Bool)) :
    PresentedGroup.mk y322Relations (FreeGroup.mk w) =
      y322PositiveWord (w.map Prod.fst) := by
  rw [y322Quotient_eq_generator_lift, FreeGroup.lift_mk]
  unfold y322PositiveWord
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  rcases x with ⟨v, b⟩
  cases b with
  | false => exact inv_eq_of_mul_eq_one_right (y322Positive_generator_square v)
  | true => rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
