/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source D6 order upper bound from a checked 32-representative A5 cover. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationD6A5Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationParabolicWords

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal cover generator list is exactly the actual source D6 list. -/
theorem y322D6A5Generator_eq : y322D6A5Generator = y322D6Generator := rfl

/-- Every literal cover representative is an actual element of the source D6 subgroup. -/
theorem y322D6A5Representative_mem (i : Fin 32) :
    y322PositiveWord (y322D6A5RepresentativeWord i) ∈ y322D6Parabolic := by
  apply y322PositiveWord_mem
  intro v hv
  exact y322D6Parabolic_generator_mem v (y322D6A5Representative_allowed i v hv)

/-- Every exact coefficient of the checked source cover lies in the actual A5 subgroup. -/
theorem y322D6A5Coefficient_mem (i : Fin 192) :
    y322PositiveWord (y322D6A5Output i) ∈ y322A5Parabolic := by
  apply y322PositiveWord_mem
  intro v hv
  exact y322A5Parabolic_generator_mem v (y322D6A5Coefficient_allowed i v hv)

/-- Every source D6 generator transition has its actual A5 coefficient and finite target. -/
theorem y322D6A5Transition (i : Fin 32) (g : Fin 6) :
    y322PositiveWord (y322D6A5RepresentativeWord i) * PresentedGroup.of (y322D6Generator g) =
      y322PositiveWord (y322D6A5Output (y322D6A5Index i g)) *
        y322PositiveWord (y322D6A5RepresentativeWord (y322D6A5TargetData (y322D6A5Index i g))) := by
  have h := y322D6A5Value (y322D6A5Index i g)
  rw [y322D6A5Input_eq] at h
  exact y322PositiveWord_transition _ _ _ _ h

/-- The checked source A5 cover proves actual D6 finiteness and its order bound 720*32. -/
theorem y322D6Parabolic_finite_card :
    Finite y322D6Parabolic ∧ Nat.card y322D6Parabolic ≤ 23040 := by
  let := y322A5Parabolic_finite
  have hs (g : Fin 6) :
      (PresentedGroup.of (y322D6Generator g) : Y322Presentation) *
        PresentedGroup.of (y322D6Generator g) = 1 := y322Positive_generator_square _
  have hb : y322PositiveWord (y322D6A5RepresentativeWord 0) = 1 := by
    rw [y322D6A5RepresentativeWord_zero]
    rfl
  have ht (i : Fin 32) (g : Fin 6) :
      ∃ h ∈ y322A5Parabolic, ∃ j : Fin 32,
        y322PositiveWord (y322D6A5RepresentativeWord i) *
          PresentedGroup.of (y322D6Generator g) =
            h * y322PositiveWord (y322D6A5RepresentativeWord j) :=
    ⟨_, y322D6A5Coefficient_mem _, _, y322D6A5Transition i g⟩
  have h := y322GeneratedSubgroup_finite_card
    (fun g : Fin 6 => (PresentedGroup.of (y322D6Generator g) : Y322Presentation))
    hs y322A5Parabolic (fun i => y322PositiveWord (y322D6A5RepresentativeWord i)) 0 hb
    y322A5Parabolic_le_D6 y322D6A5Representative_mem ht
  refine ⟨h.1, h.2.trans ?_⟩
  exact Nat.mul_le_mul_right 32 y322A5Parabolic_card_le

/-- The original source D6 parabolic is finite by its checked A5 cover. -/
theorem y322D6Parabolic_finite : Finite y322D6Parabolic := y322D6Parabolic_finite_card.1

/-- The original source D6 parabolic has order at most 23040. -/
theorem y322D6Parabolic_card_le : Nat.card y322D6Parabolic ≤ 23040 :=
  y322D6Parabolic_finite_card.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
