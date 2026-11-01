/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortTargets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! The original lattice action identifies the genuine short label of every checked input. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Denominator-cleared physical checks determine the actual integral action exactly. -/
theorem generatedSeventhXiShortInput_integral_action (s : Fin 2) (p : Fin 276) :
    (leechIntegralAction generatedSeventhLocalFiber.val.2
      (griessShortLatticeVector (generatedSeventhXiShortInputLabel s p))).val =
      generatedSeventhXiShortPhysicalSign s p •
        griessShortIntegral (generatedSeventhXiShortOutputLabel s p) := by
  funext i
  have h := generatedSeventh_forward_integral_coordinate
    (griessShortLatticeVector (generatedSeventhXiShortInputLabel s p)) i
  change 8 * _ = ∑ j, generatedSeventhFrameVectorData 7 j i *
    griessShortIntegral (generatedSeventhXiShortInputLabel s p) j at h
  rw [generatedSeventhXiShortInputLabel_integral] at h
  have hc := (generatedSeventhXiShort_arithmetic_point s p).1 i
  change _ = generatedSeventhXiShortPhysicalSign s p *
    griessShortIntegral (generatedSeventhXiShortOutputLabel s p) i
  rw [generatedSeventhXiShortOutputLabel_integral]
  nlinarith only [h, hc]

/-- The original real Leech action retains the certified global physical sign. -/
theorem generatedSeventhXiShortInput_vector_action (s : Fin 2) (p : Fin 276) :
    generatedSeventhLocalFiber.val.2.val
      (griessShortVector (generatedSeventhXiShortInputLabel s p)) =
      (generatedSeventhXiShortPhysicalSign s p : ℝ) •
        griessShortVector (generatedSeventhXiShortOutputLabel s p) := by
  have he := leechIntegralAction_embedding generatedSeventhLocalFiber.val.2
    (griessShortLatticeVector (generatedSeventhXiShortInputLabel s p))
  change leechCoordinateEmbedding _ = generatedSeventhLocalFiber.val.2.val
    (griessShortVector (generatedSeventhXiShortInputLabel s p)) at he
  rw [← he, generatedSeventhXiShortInput_integral_action]
  funext i
  simp [leechCoordinateEmbedding, griessShortVector, mul_div_assoc]

/-- The actual preferred-label permutation agrees with the checked physical output. -/
theorem generatedSeventhXiShortInput_permutation (s : Fin 2) (p : Fin 276) :
    griessShortPermutation generatedSeventhLocalFiber.val.2
      (generatedSeventhXiShortInputLabel s p) = generatedSeventhXiShortOutputLabel s p := by
  have hp := generatedSeventhXiShortInput_vector_action s p
  rcases griessShortPermutation_vector generatedSeventhLocalFiber.val.2
    (generatedSeventhXiShortInputLabel s p) with h | h
  · apply centralizer_shortVector_line_unique _ _
      (generatedSeventhXiShortPhysicalSign s p : ℝ)
    exact h.symm.trans hp
  · apply centralizer_shortVector_line_unique _ _
      (-(generatedSeventhXiShortPhysicalSign s p : ℝ))
    have hn := congrArg Neg.neg (h.symm.trans hp)
    simpa only [neg_neg, neg_smul] using hn

/-- Every actual preferred short basis image includes its original extraspecial central phase. -/
theorem generatedSeventhXiShortInput_basis (s : Fin 2) (p : Fin 276) :
    localShortOperator generatedSeventhLocalFiber
      (Pi.single (generatedSeventhXiShortInputLabel s p) (1 : ℝ)) =
      qSign (generatedSeventhXiShortPhaseBit s p : ZMod 2) •
        Pi.single (generatedSeventhXiShortOutputLabel s p) 1 := by
  funext t
  obtain ⟨r, rfl⟩ := (griessShortPermutation generatedSeventhLocalFiber.val.2).surjective t
  rw [localShortOperator_image]
  rw [← generatedSeventhXiShortInput_permutation s p,
    ← generatedSeventhXiShortInputLabel_phase s p]
  by_cases h : r = generatedSeventhXiShortInputLabel s p
  · subst r
    simp
  · have hn : griessShortPermutation generatedSeventhLocalFiber.val.2 r ≠
        griessShortPermutation generatedSeventhLocalFiber.val.2
          (generatedSeventhXiShortInputLabel s p) :=
      fun he => h ((griessShortPermutation generatedSeventhLocalFiber.val.2).injective he)
    simp [h, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
