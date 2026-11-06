/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionNormalizer

/-! The actual matrix projection of forward triality conjugates of source code lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The C row of the actual source code action is its physical sign character. -/
theorem sourceQCode_blocks_C (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 2 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 2 p := by
  have he := localGriessRepresentation_encode (localFiberIncl (sourceQCode d ε)) x
  have h0 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (0,p))) he
  have h1 := congrArg (fun b : ConwayRawSpace => b.2.1 (Sum.inl (1,p))) he
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 (Sum.inl (0,p)) =
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) (griessConwayEncode x).2.1
      (Sum.inl (0,p)) at h0
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode d ε)) x)).2.1 (Sum.inl (1,p)) =
    localShortRepresentation (localFiberIncl (sourceQCode d ε)) (griessConwayEncode x).2.1
      (Sum.inl (1,p)) at h1
  rw [sourceQCode_short_pair] at h0 h1
  simp only [griessConwayEncode, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h0 h1
  linarith

/-- Forward triality reads the A dictionary row from C. -/
theorem generatedForwardExtra_blocks_A (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra x)).2.1 0 p = (trialityBlocksEquiv x).2.1 2 p := by
  rw [generatedExtra_blocks]
  change trialityCycleAction 276 (trialityBlocksEquiv x).2.1 0 p = _
  simp only [trialityCycleAction, LinearEquiv.piCongrLeft'_apply]
  rfl

/-- Inverse triality reads the C dictionary row from A. -/
theorem generatedForwardExtra_inverse_blocks_C (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra⁻¹ x)).2.1 2 p = (trialityBlocksEquiv x).2.1 0 p := by
  rw [generatedExtra_inverse_blocks]
  change (trialityCycleAction 276).symm (trialityBlocksEquiv x).2.1 2 p = _
  rw [trialityCycleAction_inverse_apply]
  rfl

/-- The forward conjugate fixes all physical diagonal matrix entries. -/
theorem generatedForwardCode_blocks_diagonal (d : Fin 4096) (ε : ZMod 2)
    (x : GriessSpace) :
    (trialityBlocksEquiv (sExtra (rhoLocal (inclQ (sourceQCode d ε)) (sExtra⁻¹ x)))).1 =
      (trialityBlocksEquiv x).1 := by
  rw [generatedExtra_blocks_diagonal, sourceQCode_blocks_diagonal,
    generatedExtra_inverse_blocks_diagonal]

/-- The forward conjugate multiplies A by the actual encoded Golay pair character. -/
theorem generatedForwardCode_blocks_A (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace)
    (p : Fin 276) :
    (trialityBlocksEquiv (sExtra
      (rhoLocal (inclQ (sourceQCode d ε)) (sExtra⁻¹ x)))).2.1 0 p =
      qSign (golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients d) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 0 p := by
  rw [generatedForwardExtra_blocks_A, sourceQCode_blocks_C,
    generatedForwardExtra_inverse_blocks_C]

/-- The entire A matrix block of the forward triality conjugate is the actual Golay sign action.
The local membership and quotient projection are separate consequences of the
full centralizer identification and the matrix-action kernel. -/
theorem generatedForwardCode_matrix (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    (griessConwayEncode (sExtra (rhoLocal (inclQ (sourceQCode d ε)) (sExtra⁻¹ x)))).1 =
      conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode d))
        (griessConwayEncode x).1 := by
  ext i j
  rw [sourceGeneratedSign_matrix_apply]
  by_cases hij : i = j
  · subst j
    simp only [griessConwayEncode, dite_true, generatedForwardCode_blocks_diagonal,
      CharTwo.add_self_eq_zero, qSign_zero, one_mul]
  · have hp : golayEncoder (golayLabelCoefficients d)
        (griessCoordinatePair (griessPairIndex i j hij)).1 +
        golayEncoder (golayLabelCoefficients d)
          (griessCoordinatePair (griessPairIndex i j hij)).2 =
        golayEncoder (golayLabelCoefficients d) i + golayEncoder (golayLabelCoefficients d) j := by
      rw [griessPairIndex_coordinates]
      split_ifs
      · rfl
      · exact add_comm _ _
    simp only [griessConwayEncode, hij, dite_false]
    rw [generatedForwardCode_blocks_A, hp]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
