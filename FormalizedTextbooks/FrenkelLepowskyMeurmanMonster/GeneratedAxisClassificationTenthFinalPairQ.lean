/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthIncomingPairNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Every final original pair coefficient retains the actual matrix
and both incoming short terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact rational original minus or plus pair coefficient after actual triality. -/
def generatedTenthFinalPairQ (s : Fin 2) (p : Fin 276) : ℚ :=
  (if s = 0 then 1 else -1) *
      generatedTenthIncomingMatrixQ (griessCoordinatePair p).1 (griessCoordinatePair p).2 +
    ((generatedTenthIncomingPairNumerator 0 p : ℚ) -
      (generatedTenthIncomingPairNumerator 1 p : ℚ)) / 32

/-- Every outgoing original pair coefficient equals the complete rational source formula. -/
theorem generatedTenth_final_pair_q (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedTenthAxis).2.1 (Sum.inl (s, p)) =
      (generatedTenthFinalPairQ s p : ℝ) := by
  rw [generatedTenthAxis_local_expression]
  fin_cases s
  · change (griessConwayEncode (sExtra (rhoLocal generatedTenthLocal generatedFifthAxis))).2.1
        (Sum.inl (0, p)) = (generatedTenthFinalPairQ 0 p : ℝ)
    rw [generatedFourthQShortBasis_triality_pair_minus,
      generatedTenth_incoming_matrix_coordinate,
      generatedTenth_incoming_pair_numerator, generatedTenth_incoming_pair_numerator]
    simp only [generatedTenthFinalPairQ, ite_true, one_mul]
    push_cast
    ring
  · change (griessConwayEncode (sExtra (rhoLocal generatedTenthLocal generatedFifthAxis))).2.1
        (Sum.inl (1, p)) = (generatedTenthFinalPairQ 1 p : ℝ)
    rw [generatedFourthQShortBasis_triality_pair_plus,
      generatedTenth_incoming_matrix_coordinate,
      generatedTenth_incoming_pair_numerator, generatedTenth_incoming_pair_numerator]
    norm_num only [generatedTenthFinalPairQ, Fin.reduceEq, ite_false]
    push_cast
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
