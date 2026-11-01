/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairPhaseCache

/-! Every exact rational matrix entry of the genuine original Fourth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual diagonal projector and original signed preferred pair line. -/
def generatedAxisGlobalCanonicalFourthMatrixQ (i j : Fin 24) : ℚ :=
  if hij : i = j then (generatedFourthProjectionDiagonal i : ℚ) / 16 else
    if griessCoordinatePair (griessPairIndex i j hij) = (8, 11) then -1 / 2 else 0

/-- Every displayed entry equals the actual full original matrix coefficient. -/
theorem generatedAxisGlobalCanonicalFourthMatrixQ_actual (i j : Fin 24) :
    (generatedAxisGlobalCanonicalFourthMatrixQ i j : ℝ) =
      (griessConwayEncode generatedFourthAxis).1 i j := by
  by_cases hij : i = j
  · subst j
    rw [generatedFourth_matrix_diagonal]
    simp [generatedAxisGlobalCanonicalFourthMatrixQ]
  · rw [generatedFourth_matrix_off_diagonal i j hij, generatedFourth_pair_phase_zero,
      qSign_zero]
    by_cases hp : griessCoordinatePair (griessPairIndex i j hij) = (8, 11) <;>
      simp [generatedAxisGlobalCanonicalFourthMatrixQ, hij, hp]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
