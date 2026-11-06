/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingPairNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Every final original pair coefficient retains the actual matrix
and both incoming short terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact rational original minus or plus pair coefficient after actual triality. -/
def generatedTwelfthFinalPairQ (s : Fin 2) (p : Fin 276) : ℚ :=
  (if s = 0 then 1 else -1) *
      generatedTwelfthIncomingMatrixQ (griessCoordinatePair p).1 (griessCoordinatePair p).2 +
    ((generatedTwelfthIncomingPairNumerator 0 p : ℚ) -
      (generatedTwelfthIncomingPairNumerator 1 p : ℚ)) / 32

/-- Every outgoing original pair coefficient equals the complete rational source formula. -/
theorem generatedTwelfth_final_pair_q (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedTwelfthAxis).2.1 (Sum.inl (s, p)) =
      (generatedTwelfthFinalPairQ s p : ℝ) := by
  rw [generatedTwelfthAxis_local_expression]
  fin_cases s
  · change (griessConwayEncode (sExtra (rhoLocal generatedTwelfthLocal generatedFifthAxis))).2.1
        (Sum.inl (0, p)) = (generatedTwelfthFinalPairQ 0 p : ℝ)
    rw [generatedFourthQShortBasis_triality_pair_minus,
      generatedTwelfth_incoming_matrix_coordinate,
      generatedTwelfth_incoming_pair_numerator, generatedTwelfth_incoming_pair_numerator]
    simp only [generatedTwelfthFinalPairQ, ite_true, one_mul]
    push_cast
    ring
  · change (griessConwayEncode (sExtra (rhoLocal generatedTwelfthLocal generatedFifthAxis))).2.1
        (Sum.inl (1, p)) = (generatedTwelfthFinalPairQ 1 p : ℝ)
    rw [generatedFourthQShortBasis_triality_pair_plus,
      generatedTwelfth_incoming_matrix_coordinate,
      generatedTwelfth_incoming_pair_numerator, generatedTwelfth_incoming_pair_numerator]
    norm_num only [generatedTwelfthFinalPairQ, Fin.reduceEq, ite_false]
    push_cast
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
