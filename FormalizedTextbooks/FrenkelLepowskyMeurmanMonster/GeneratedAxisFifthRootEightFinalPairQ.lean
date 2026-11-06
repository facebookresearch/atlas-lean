/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightIncomingPairNumerator
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Every final original pair coefficient retains the actual matrix
and both incoming short terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact rational original minus or plus pair coefficient after actual triality. -/
def generatedFifthRootEightFinalPairQ (s : Fin 2) (p : Fin 276) : ℚ :=
  (if s = 0 then 1 else -1) *
      generatedFifthRootEightIncomingMatrixQ (griessCoordinatePair p).1 (griessCoordinatePair p).2 +
    ((generatedFifthRootEightIncomingPairNumerator 0 p : ℚ) -
      (generatedFifthRootEightIncomingPairNumerator 1 p : ℚ)) / 32

/-- Every outgoing original pair coefficient equals the complete rational source formula. -/
theorem generatedFifthRootEight_final_pair_q (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedFifthRootEightAxis).2.1 (Sum.inl (s, p)) =
      (generatedFifthRootEightFinalPairQ s p : ℝ) := by
  rw [generatedFifthRootEightAxis_local_expression]
  fin_cases s
  · change (griessConwayEncode
        (sExtra (rhoLocal generatedFifthRootEightLocal generatedFifthAxis))).2.1
        (Sum.inl (0, p)) = (generatedFifthRootEightFinalPairQ 0 p : ℝ)
    rw [generatedFourthQShortBasis_triality_pair_minus,
      generatedFifthRootEight_incoming_matrix_coordinate,
      generatedFifthRootEight_incoming_pair_numerator,
      generatedFifthRootEight_incoming_pair_numerator]
    simp only [generatedFifthRootEightFinalPairQ, ite_true, one_mul]
    push_cast
    ring
  · change (griessConwayEncode
        (sExtra (rhoLocal generatedFifthRootEightLocal generatedFifthAxis))).2.1
        (Sum.inl (1, p)) = (generatedFifthRootEightFinalPairQ 1 p : ℝ)
    rw [generatedFourthQShortBasis_triality_pair_plus,
      generatedFifthRootEight_incoming_matrix_coordinate,
      generatedFifthRootEight_incoming_pair_numerator,
      generatedFifthRootEight_incoming_pair_numerator]
    norm_num only [generatedFifthRootEightFinalPairQ, Fin.reduceEq, ite_false]
    push_cast
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
