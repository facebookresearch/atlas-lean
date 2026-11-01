/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrixData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthDiagonal

/-! Every full actual ninth matrix entry follows the original generator
and preferred-Q certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The finite original matrix in real Conway coordinates. -/
def generatedNinthAxisMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  fun i j => (generatedNinthMatrixNumerator i j : ℝ) / 32

/-- All ordered off-diagonal entries have their exact signed source numerator. -/
theorem generatedNinth_matrix_ordered (i j : Fin 24) (hij : i < j) :
    (griessConwayEncode generatedNinthAxis).1 i j = generatedNinthAxisMatrix i j := by
  rw [generatedNinthAxis_local_expression,
    generatedFourth_triality_matrix_off_diagonal _ i j (ne_of_lt hij),
    generatedNinth_middle_pair, generatedNinth_middle_pair,
    griessPairIndex_coordinates, ite_eq_left hij]
  have hc : (generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 0 i j) : ℝ) +
      (generatedNinthPairCoefficientNumerator (generatedNinthPairLookup 1 i j) : ℝ) =
        (generatedNinthMatrixNumerator i j : ℝ) := by
    exact_mod_cast generatedNinth_matrix_pair_certificate i j hij
  change ((_ / 16 + _ / 16) / 2 : ℝ) = _ / 32
  rw [← add_div, hc]
  ring

/-- The entire actual ninth prototype matrix is certified entry by entry. -/
theorem generatedNinth_axis_matrix :
    (griessConwayEncode generatedNinthAxis).1 = generatedNinthAxisMatrix := by
  ext i j
  by_cases he : i = j
  · subst j
    rw [generatedNinth_matrix_diagonal]
    simp only [generatedNinthAxisMatrix, generatedNinthMatrixNumerator_diagonal]
  · by_cases h : i < j
    · exact generatedNinth_matrix_ordered i j h
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt h) (fun hji => he hji.symm)
      rw [griessConwayEncode_symmetric generatedNinthAxis i j,
        generatedNinth_matrix_ordered j i hji]
      simp only [generatedNinthAxisMatrix, generatedNinthMatrixNumerator_symmetric j i]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
