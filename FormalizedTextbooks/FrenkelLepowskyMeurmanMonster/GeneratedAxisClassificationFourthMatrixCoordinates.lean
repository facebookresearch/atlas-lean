/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthDiagonal

/-! Original matrix coordinates of the literal generated-group representative.
The local and triality actions here are the original representation, not a
modular discovery representation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The actual local matrix block is the genuine Leech congruence action. -/
theorem generatedFourth_local_matrix (f : localFiberSubgroup) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (localFiberIntoH f) x)).1 =
      conwayMatrixAction f.val.2 (griessConwayEncode x).1 := by
  exact congrArg Prod.fst (localGriessRepresentation_encode f x)

/-- The actual local short block is its phase-correct preferred short operator. -/
theorem generatedFourth_local_short (f : localFiberSubgroup) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (localFiberIntoH f) x)).2.1 =
      localShortOperator f (griessConwayEncode x).2.1 := by
  exact congrArg (fun y : ConwayRawSpace => y.2.1) (localGriessRepresentation_encode f x)

/-- Every original diagonal entry of the literal representative. -/
theorem generatedFourth_matrix_diagonal (i : Fin 24) :
    (griessConwayEncode generatedFourthAxis).1 i i =
      (generatedFourthProjectionDiagonal i : ℝ) / 16 := by
  rw [generatedFourthAxis_local_expression, generatedFourth_triality_matrix_diagonal,
    generatedFourth_local_matrix, generatedAxis_triality_octad_matrix,
    generatedFourthOctad_mask]
  exact generatedFourth_projection_diagonal i

/-- Every original off-diagonal entry, expressed by the one verified preferred pair line. -/
theorem generatedFourth_matrix_off_diagonal (i j : Fin 24) (hij : i ≠ j) :
    (griessConwayEncode generatedFourthAxis).1 i j =
      if griessCoordinatePair (griessPairIndex i j hij) = (8, 11) then
        -qSign generatedFourthPairPhase / 2 else 0 := by
  rw [generatedFourthAxis_local_expression,
    generatedFourth_triality_matrix_off_diagonal _ i j hij, generatedFourth_local_short,
    generatedFourth_transported_pair_coordinate, generatedFourth_transported_pair_coordinate]
  by_cases h : griessCoordinatePair (griessPairIndex i j hij) = (8, 11)
  · simp [h]
  · simp [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
