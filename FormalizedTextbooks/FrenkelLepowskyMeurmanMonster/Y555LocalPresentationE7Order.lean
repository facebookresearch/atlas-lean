/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source E7 order upper bound from a checked 126-representative D6 cover. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7D6Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationD6Order

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal cover labels are exactly the first seven original source generators. -/
theorem y322E7D6Generator_eq (g : Fin 7) : y322E7D6Generator g = g.castSucc := by
  fin_cases g <;> rfl

/-- Every literal cover representative belongs to the actual original E7 subgroup. -/
theorem y322E7D6Representative_mem (i : Fin 126) :
    y322PositiveWord (y322E7D6RepresentativeWord i) ∈ y322E7Parabolic := by
  apply y322PositiveWord_mem
  intro v hv
  exact y322E7Parabolic_generator_mem v (y322E7D6Representative_allowed i v hv)

/-- Every checked cover coefficient belongs to the actual original D6 subgroup. -/
theorem y322E7D6Coefficient_mem (i : Fin 882) :
    y322PositiveWord (y322E7D6Output i) ∈ y322D6Parabolic := by
  apply y322PositiveWord_mem
  intro v hv
  exact y322D6Parabolic_generator_mem v (y322E7D6Coefficient_allowed i v hv)

/-- Every original E7 right-generator transition has its exact actual D6 coefficient. -/
theorem y322E7D6Transition (i : Fin 126) (g : Fin 7) :
    y322PositiveWord (y322E7D6RepresentativeWord i) * PresentedGroup.of g.castSucc =
      y322PositiveWord (y322E7D6Output (y322E7D6Index i g)) *
        y322PositiveWord (y322E7D6RepresentativeWord (y322E7D6TargetData (y322E7D6Index i g))) := by
  have h := y322E7D6Value (y322E7D6Index i g)
  rw [y322E7D6Input_eq] at h
  rw [← y322E7D6Generator_eq g]
  exact y322PositiveWord_transition _ _ _ _ h

/-- The checked D6 cover proves actual source E7 finiteness and order at most 2903040. -/
theorem y322E7Parabolic_finite_card :
    Finite y322E7Parabolic ∧ Nat.card y322E7Parabolic ≤ 2903040 := by
  let := y322D6Parabolic_finite
  have hs (g : Fin 7) :
      (PresentedGroup.of g.castSucc : Y322Presentation) * PresentedGroup.of g.castSucc = 1 :=
    y322Positive_generator_square _
  have hb : y322PositiveWord (y322E7D6RepresentativeWord 0) = 1 := by
    rw [y322E7D6RepresentativeWord_zero]
    rfl
  have ht (i : Fin 126) (g : Fin 7) :
      ∃ h ∈ y322D6Parabolic, ∃ j : Fin 126,
        y322PositiveWord (y322E7D6RepresentativeWord i) * PresentedGroup.of g.castSucc =
          h * y322PositiveWord (y322E7D6RepresentativeWord j) :=
    ⟨_, y322E7D6Coefficient_mem _, _, y322E7D6Transition i g⟩
  have h := y322GeneratedSubgroup_finite_card
    (fun g : Fin 7 => (PresentedGroup.of g.castSucc : Y322Presentation))
    hs y322D6Parabolic (fun i => y322PositiveWord (y322E7D6RepresentativeWord i)) 0 hb
    y322D6Parabolic_le_E7 y322E7D6Representative_mem ht
  refine ⟨h.1, h.2.trans ?_⟩
  exact Nat.mul_le_mul_right 126 y322D6Parabolic_card_le

/-- The original source E7 parabolic is finite from actual checked generator transitions. -/
theorem y322E7Parabolic_finite : Finite y322E7Parabolic := y322E7Parabolic_finite_card.1

/-- The original source E7 parabolic has order at most 2903040. -/
theorem y322E7Parabolic_card_le : Nat.card y322E7Parabolic ≤ 2903040 :=
  y322E7Parabolic_finite_card.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
