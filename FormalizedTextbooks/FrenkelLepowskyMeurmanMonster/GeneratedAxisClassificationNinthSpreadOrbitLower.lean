/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitActions

/-! The literal acyclic source letters give at least 960 images of an actual nine-system set.
The separate Ninth-axis marking comparison is not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- Every recorded state is reached by a genuine word in the entire actual section group. -/
theorem generatedNinth_spread_actual_mem_orbit (i : Fin 960) :
    generatedNinthSpreadActual i ∈ MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedNinthSpreadActual 0) := by
  classical
  have hc : ∀ n : ℕ, ∀ hn : n < 960,
      generatedNinthSpreadActual ⟨n, hn⟩ ∈
        MulAction.orbit generatedAxisE8FrameSystemSectionGroup (generatedNinthSpreadActual 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hz : n = 0
      · subst n
        have hi : (⟨0, hn⟩ : Fin 960) = 0 := Fin.ext rfl
        rw [hi]
        refine ⟨1, ?_⟩
        exact one_smul _ _
      let j : Fin 960 := ⟨n, hn⟩
      have hj : j ≠ 0 := fun he => hz (congrArg Fin.val he)
      obtain ⟨a, ha⟩ := ih (generatedNinthSpreadParent j).val
        (generatedNinth_spread_parent_lt j hj) (generatedNinthSpreadParent j).isLt
      change a • generatedNinthSpreadActual 0 =
        generatedNinthSpreadActual (generatedNinthSpreadParent j) at ha
      refine ⟨generatedAxisE8FrameSystemOrbitLetter (generatedNinthSpreadGenerator j) * a, ?_⟩
      change (generatedAxisE8FrameSystemOrbitLetter (generatedNinthSpreadGenerator j) * a) •
        generatedNinthSpreadActual 0 = generatedNinthSpreadActual ⟨n, hn⟩
      rw [mul_smul, ha]
      exact generatedNinth_spread_edge_actual j hj
  exact hc i.val i.isLt

/-- The genuine original-section orbit of this entire nine-system set has at least 960 elements. -/
theorem generatedNinth_spread_actual_orbit_card_lower :
    960 ≤ Nat.card (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedNinthSpreadActual 0)) := by
  classical
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let fG : generatedAxisE8FrameSystemSectionGroup →
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup (generatedNinthSpreadActual 0) :=
    fun g => ⟨g • generatedNinthSpreadActual 0, ⟨g, rfl⟩⟩
  have hfG : Function.Surjective fG := by
    rintro ⟨V, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedNinthSpreadActual 0)) := Finite.of_surjective fG hfG
  let f : Fin 960 → MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedNinthSpreadActual 0) := fun i =>
    ⟨generatedNinthSpreadActual i, generatedNinth_spread_actual_mem_orbit i⟩
  have hf : Function.Injective f := fun i j h =>
    generatedNinthSpreadActual_injective (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The actual Co0 stabilizer of the entire nine-system set in the full section group. -/
def generatedNinthSpreadSectionStabilizer : Subgroup generatedAxisE8FrameSystemSectionGroup :=
  MulAction.stabilizer _ (generatedNinthSpreadActual 0)

/-- The checked orbit bound limits the whole actual section stabilizer
to 185794560 elements. -/
theorem generatedNinth_spread_section_stabilizer_card_le :
    Nat.card generatedNinthSpreadSectionStabilizer ≤ 185794560 := by
  classical
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedAxisE8FrameSystemSectionGroup (generatedNinthSpreadActual 0))
  rw [Nat.card_prod, generatedAxisE8_sectionStabilizer_card generatedFifthFlagOctad] at hc
  have hm := Nat.mul_le_mul_right (Nat.card generatedNinthSpreadSectionStabilizer)
    generatedNinth_spread_actual_orbit_card_lower
  change 960 * Nat.card generatedNinthSpreadSectionStabilizer ≤
    Nat.card (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedNinthSpreadActual 0)) * Nat.card generatedNinthSpreadSectionStabilizer at hm
  change Nat.card (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
    (generatedNinthSpreadActual 0)) * Nat.card generatedNinthSpreadSectionStabilizer =
      178362777600 at hc
  rw [hc] at hm
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
