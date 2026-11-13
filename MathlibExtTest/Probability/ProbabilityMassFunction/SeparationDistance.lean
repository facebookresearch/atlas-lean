/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Alexei Kopylov
-/
module

public import MathlibExt.Probability.ProbabilityMassFunction.SeparationDistance

@[expose] public section

namespace MathlibExtTest.Probability.ProbabilityMassFunction.SeparationDistance

open MetaMathlibExt

-- Combinatorics 689: Separation distance between two PMFs

/-- Each likelihood-ratio gap on the support is bounded by separation. -/

theorem sub_one_div_le_separation  {α : Type*} [Fintype α] [DecidableEq α] (p q : PMF α) (a : α)
    (hq : pmfReal q a ≠ 0) :
    1 - pmfReal p a / pmfReal q a ≤ separationDistance p q := by
  have hmem : a ∈ Finset.univ.filter (fun a => pmfReal q a ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, hq⟩
  unfold separationDistance
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem
    (fun a => 1 - pmfReal p a / pmfReal q a) hmem)

/-- Separation distance from a PMF to itself is zero. -/

theorem separationDistance_self {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) : separationDistance p p = 0 := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    have hq : pmfReal p a ≠ 0 := (Finset.mem_filter.mp ha).2
    have h0 : 1 - pmfReal p a / pmfReal p a = 0 := by
      rw [div_self hq, sub_self]
    exact le_of_eq h0
  · obtain ⟨a0, ha0⟩ := pmfReal_support_nonempty p
    have hq0 : pmfReal p a0 ≠ 0 := (Finset.mem_filter.mp ha0).2
    have h0 : 1 - pmfReal p a0 / pmfReal p a0 = 0 := by
      rw [div_self hq0, sub_self]
    have hle := sub_one_div_le_separation p p a0 hq0
    rw [h0] at hle
    exact hle

end MathlibExtTest.Probability.ProbabilityMassFunction.SeparationDistance

end
