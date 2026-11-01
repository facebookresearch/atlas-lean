/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMiddleMatrixInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairCoefficients

/-! The final signed-pair coordinates retain every original preferred-Q phase and matrix column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original exact integer numerator of each final signed-pair coefficient. -/
def generatedNinthFinalPairInteger (s : Fin 2) (p : Fin 276) : ℤ :=
  let i := (griessCoordinatePair p).1
  let j := (griessCoordinatePair p).2
  8 * (generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 0 i j) -
      generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 1 i j)) +
    (if s = 0 then generatedNinthMiddleMatrixInteger i j
      else -generatedNinthMiddleMatrixInteger i j)

/-- Every actual final signed-pair coefficient is the original numerator divided by256. -/
theorem generatedNinth_final_pair_integer (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inl (s, p)) =
      (generatedNinthFinalPairInteger s p : ℝ) / 256 := by
  rw [generatedNinthAxis_local_expression, generatedNinth_final_triality_pair_coordinate,
    generatedNinth_middle_pair, generatedNinth_middle_pair,
    generatedNinth_middle_matrix_integer]
  simp only [generatedNinthFinalPairInteger, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_sub, Int.cast_ite, Int.cast_neg]
  split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
