/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorShortCertificates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixCertificates

/-! Complete actual-coordinate rational triality of the two entire intermediate states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The entire first corrected-Xi state, including every original short label and zero tensor. -/
def generatedFeasibleContainingZeroOutsideAnchorFirstPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedFeasibleContainingZeroOutsideAnchorMatrix1Q,
    (generatedFeasibleContainingZeroOutsideAnchorShortQ 1, 0))

/-- The entire forward-triality state, including all physical coordinates and zero tensor. -/
def generatedFeasibleContainingZeroOutsideAnchorSecondPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedFeasibleContainingZeroOutsideAnchorMatrix2Q,
    (generatedFeasibleContainingZeroOutsideAnchorShortQ 2, 0))

private theorem first_fst :
    generatedFeasibleContainingZeroOutsideAnchorFirstPacket.1 =
      generatedFeasibleContainingZeroOutsideAnchorMatrix1Q := rfl

private theorem first_snd_fst :
    generatedFeasibleContainingZeroOutsideAnchorFirstPacket.2.1 =
      generatedFeasibleContainingZeroOutsideAnchorShortQ 1 := rfl

private theorem first_snd_snd :
    generatedFeasibleContainingZeroOutsideAnchorFirstPacket.2.2 = 0 := rfl

private theorem second_fst :
    generatedFeasibleContainingZeroOutsideAnchorSecondPacket.1 =
      generatedFeasibleContainingZeroOutsideAnchorMatrix2Q := rfl

private theorem second_snd_fst :
    generatedFeasibleContainingZeroOutsideAnchorSecondPacket.2.1 =
      generatedFeasibleContainingZeroOutsideAnchorShortQ 2 := rfl

private theorem second_snd_snd :
    generatedFeasibleContainingZeroOutsideAnchorSecondPacket.2.2 = 0 := rfl

private theorem triality_fst (a : GeneratedAxisGlobalRationalPacket) :
    (generatedAxisGlobalRationalTriality a).1 = generatedAxisGlobalTrialityMatrixQ a := rfl

private theorem triality_snd_fst (a : GeneratedAxisGlobalRationalPacket) :
    (generatedAxisGlobalRationalTriality a).2.1 = generatedAxisGlobalTrialityShortQ a := rfl

private theorem triality_snd_snd (a : GeneratedAxisGlobalRationalPacket) :
    (generatedAxisGlobalRationalTriality a).2.2 =
      generatedAxisGlobalTrialityScaledTensorQ a.2.1 a.2.2 := rfl

private theorem matrixQ_apply (a : GeneratedAxisGlobalRationalPacket) (i j : Fin 24) :
    generatedAxisGlobalTrialityMatrixQ a i j =
      if i = j then a.1 i i else
        (a.2.1 (Sum.inl (0, generatedAxisGlobalFinitePairIndex i j)) +
          a.2.1 (Sum.inl (1, generatedAxisGlobalFinitePairIndex i j))) / 2 := rfl

private theorem shortQ_pair (a : GeneratedAxisGlobalRationalPacket) (s : Fin 2) (p : Fin 276) :
    generatedAxisGlobalTrialityShortQ a (Sum.inl (s, p)) =
      if s = 0 then
        a.1 (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
          (a.2.1 (Sum.inl (0, p)) - a.2.1 (Sum.inl (1, p))) / 2
      else
        (a.2.1 (Sum.inl (0, p)) - a.2.1 (Sum.inl (1, p))) / 2 -
          a.1 (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 :=
  rfl

private theorem shortQ_octad (a : GeneratedAxisGlobalRationalPacket) (o : Fin 759) (e : Fin 64) :
    generatedAxisGlobalTrialityShortQ a (Sum.inr (Sum.inl (o, e))) =
      ∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 * a.2.1 (Sum.inr (Sum.inl (o, f))) :=
  rfl

private theorem shortQ_odd (a : GeneratedAxisGlobalRationalPacket) (d : Fin 2048) (i : Fin 24) :
    generatedAxisGlobalTrialityShortQ a (Sum.inr (Sum.inr (d, i))) =
      (generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) *
        (a.2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          a.2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / 2 := rfl

private theorem packet_pair (k : Fin 4) (s : Fin 2) (p : Fin 276) :
    generatedFeasibleContainingZeroOutsideAnchorShortQ k (Sum.inl (s, p)) =
      generatedFeasibleContainingZeroOutsideAnchorPairQ k s p := rfl

private theorem packet_octad (k : Fin 4) (o : Fin 759) (e : Fin 64) :
    generatedFeasibleContainingZeroOutsideAnchorShortQ k (Sum.inr (Sum.inl (o, e))) =
      generatedFeasibleContainingZeroOutsideAnchorOctadQ k (golayOctadLabel o) e := rfl

private theorem packet_odd (k : Fin 4) (d : Fin 2048) (i : Fin 24) :
    generatedFeasibleContainingZeroOutsideAnchorShortQ k (Sum.inr (Sum.inr (d, i))) = 0 := rfl

/-- Every physical matrix, preferred short, and tensor coordinate follows from the whole
original operator. All encoder rows outside the full realized support are included symbolically. -/
theorem generatedFeasibleContainingZeroOutsideAnchorTriality_packet :
    generatedAxisGlobalRationalTriality generatedFeasibleContainingZeroOutsideAnchorFirstPacket =
      generatedFeasibleContainingZeroOutsideAnchorSecondPacket := by
  apply Prod.ext
  · rw [triality_fst, second_fst, ← generatedFeasibleContainingZeroOutsideAnchorMatrix_triality]
    funext i j
    rw [matrixQ_apply, first_fst, first_snd_fst, packet_pair, packet_pair,
      generatedFeasibleContainingZeroOutsideAnchorPairQ_one,
      generatedFeasibleContainingZeroOutsideAnchorPairQ_one]
    rfl
  · apply Prod.ext
    · rw [triality_snd_fst, second_snd_fst]
      funext r
      rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
      · rw [shortQ_pair, first_fst, first_snd_fst, packet_pair, packet_pair, packet_pair,
          generatedFeasibleContainingZeroOutsideAnchorPairQ_one,
          generatedFeasibleContainingZeroOutsideAnchorPairQ_one,
          generatedFeasibleContainingZeroOutsideAnchorPairQ_two]
        exact generatedFeasibleContainingZeroOutsideAnchorPairQ_triality s p
      · rw [shortQ_octad, first_snd_fst, packet_octad]
        simp only [packet_octad]
        by_cases hj : ∃ j : Fin 14,
            golayOctadLabel o = generatedFeasibleContainingZeroOutsideAnchorCode j
        · obtain ⟨j, hj⟩ := hj
          rw [hj]
          simp only [generatedFeasibleContainingZeroOutsideAnchorOctadQ_one j]
          rw [generatedFeasibleContainingZeroOutsideAnchorOctadQ_two j]
          exact generatedFeasibleContainingZeroOutsideAnchorOctadQ_fourier j e
        · have hd : ∀ j : Fin 14,
              golayOctadLabel o ≠ generatedFeasibleContainingZeroOutsideAnchorCode j :=
            not_exists.mp hj
          simp only [generatedFeasibleContainingZeroOutsideAnchorOctadQ_zero_outside 1 _ _ hd,
            generatedFeasibleContainingZeroOutsideAnchorOctadQ_zero_outside 2 _ _ hd,
            mul_zero, Finset.sum_const_zero]
      · rw [packet_odd, shortQ_odd, first_snd_snd]
        simp
    · rw [triality_snd_snd, second_snd_snd, first_snd_fst, first_snd_snd]
      funext t j
      simp only [generatedAxisGlobalTrialityScaledTensorQ, packet_odd]
      simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
