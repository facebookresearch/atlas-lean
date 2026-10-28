/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSelectedPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! Complete actual short-support transport by the ninth local word, with all central phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual preferred target of each original source row under the spatial word. -/
def generatedNinthMiddleShortSourceIndex
    (a : generatedNinthOriginalShortLabel) : GriessShortIndex :=
  griessShortPermutation generatedNinthLocalFiber.val.2 (generatedNinthOriginalShortIndex a)

/-- Every transported source coefficient retains its full original central phase and numerator. -/
theorem generatedNinth_middle_short_source_coefficient (a : generatedNinthOriginalShortLabel) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (generatedNinthMiddleShortSourceIndex a) =
        qSign (generatedNinthSelectedPhase (griessShortQ (generatedNinthOriginalShortIndex a))) *
          ((generatedNinthOriginalShortNumerator a : ℝ) / 16) := by
  rw [generatedFourth_local_short, generatedNinthMiddleShortSourceIndex,
    localShortOperator_image, generatedNinth_short_selected_phase,
    generatedNinth_original_short_numerator_actual]

/-- Every nonzero actual middle short coefficient is a transported nonzero original source row. -/
theorem generatedNinth_middle_short_nonzero_covered (r : GriessShortIndex)
    (hr : (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r ≠ 0) :
    ∃ a : generatedNinthOriginalShortLabel,
      generatedNinthMiddleShortSourceIndex a = r ∧ generatedNinthOriginalShortNumerator a ≠ 0 := by
  let u := (griessShortPermutation generatedNinthLocalFiber.val.2).symm r
  have hu : griessShortPermutation generatedNinthLocalFiber.val.2 u = r :=
    Equiv.apply_symm_apply _ r
  have hn : (griessConwayEncode generatedFifthAxis).2.1 u ≠ 0 := by
    intro h
    apply hr
    rw [generatedFourth_local_short, ← hu, localShortOperator_image, h, mul_zero]
  obtain ⟨a, ha⟩ := generatedNinth_original_short_nonzero_covered u hn
  refine ⟨a, ?_, ?_⟩
  · exact (congrArg (griessShortPermutation generatedNinthLocalFiber.val.2) ha).trans hu
  · apply generatedNinth_original_short_numerator_ne_zero
    simpa only [ha] using hn

/-- Every short row outside the transported nonzero original support is actually zero. -/
theorem generatedNinth_middle_short_zero_of_not_source (r : GriessShortIndex)
    (h : ¬∃ a : generatedNinthOriginalShortLabel,
      generatedNinthMiddleShortSourceIndex a = r ∧ generatedNinthOriginalShortNumerator a ≠ 0) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r = 0 := by
  apply not_ne_iff.mp
  intro hn
  exact h (generatedNinth_middle_short_nonzero_covered r hn)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
