/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRawMatrix

/-! A complete exact starting packet for real fifth-family triality transition checks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Full explicit signed short coordinates of the actual fifth prototype. -/
def generatedAxisGlobalFifthRawShort : GriessShortIndex → ℝ
  | Sum.inl (s, p) => if s = 0 then
      (generatedAxisGlobalFifthMiddleMatrixQ
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ)
    else -(generatedAxisGlobalFifthMiddleMatrixQ
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ)
  | Sum.inr (Sum.inl (o, e)) => ∑ j : Fin 56,
      if generatedFifthEvenRootOctad j = o then
        trialityRealMatrix e (generatedFifthEvenRootSign j) *
          qSign (generatedFifthEvenCoefficientPhase j) else 0
  | Sum.inr (Sum.inr _) => 0

/-- Every short coordinate, including all outside the displayed packets, is exact. -/
theorem generatedAxisGlobalFifthRawShort_eq :
    (griessConwayEncode generatedFifthAxis).2.1 = generatedAxisGlobalFifthRawShort := by
  funext r
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · fin_cases s
    · simpa [generatedAxisGlobalFifthRawShort] using
        generatedAxisGlobalFifthRaw_pair_minus p
    · simpa [generatedAxisGlobalFifthRawShort] using
        generatedAxisGlobalFifthRaw_pair_plus p
  · by_cases ho : ∃ j : Fin 56, generatedFifthEvenRootOctad j = o
    · obtain ⟨j, rfl⟩ := ho
      rw [generatedFifth_final_octad_coordinate]
      change _ = ∑ k : Fin 56, if generatedFifthEvenRootOctad k =
        generatedFifthEvenRootOctad j then _ else 0
      rw [Finset.sum_eq_single j]
      · simp only [↓reduceIte]
      · intro k _ hkj
        have hn : generatedFifthEvenRootOctad k ≠ generatedFifthEvenRootOctad j :=
          fun h => hkj (generatedFifth_even_octads_injective h)
        simp only [hn, ↓reduceIte]
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    · rw [generatedFifth_final_octad_zero o e ho]
      change 0 = ∑ j : Fin 56, if generatedFifthEvenRootOctad j = o then _ else 0
      symm
      apply Finset.sum_eq_zero
      intro j _
      simp only [show generatedFifthEvenRootOctad j ≠ o from fun h => ho ⟨j, h⟩,
        ↓reduceIte]
  · exact generatedFifth_final_odd_zero d i

/-- Complete original Conway coordinates of the actual fifth prototype. -/
def generatedAxisGlobalFifthRawPacket : ConwayRawSpace :=
  (Matrix.diagonal (fun i : Fin 24 => if Nat.testBit 0x0f000f i.val then
      (1 / 2 : ℝ) else 1 / 4),
    (generatedAxisGlobalFifthRawShort,
      ∑ j : Fin 64, qSign (generatedFifthOddCoefficientPhaseData j) •
        trialityYTensor (generatedFifthOddRootOutputData j).1
          (generatedFifthOddRootOutputData j).2))

/-- The complete packet is the actual real coordinate image, with all original phases. -/
theorem generatedAxisGlobalFifthRawPacket_eq :
    griessConwayEncode generatedFifthAxis = generatedAxisGlobalFifthRawPacket := by
  apply Prod.ext
  · exact generatedFifth_matrix
  · apply Prod.ext
    · exact generatedAxisGlobalFifthRawShort_eq
    · exact generatedFifth_tensor_sum

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
