/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7XiCorrectionData

/-! Actual real and lattice actions of the correcting Xi move. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The move is a product of three genuine original Co0 lattice isometries. -/
def generatedTenthE7XiCorrection : leechIsomSubgroup :=
  golaySignIsometry generatedTenthE7XiCode *
    golayPermutationIsometry generatedTenthE7XiAutomorphism * co1XiIsometry

private theorem sign_cast (i : Fin 24) :
    qSign (generatedTenthE7XiCode.val i) =
      ((if generatedTenthE7XiCode.val i = 0 then 1 else -1 : ℤ) : ℝ) := by
  by_cases hi : generatedTenthE7XiCode.val i = 0 <;> simp [qSign, hi]

/-- The entire genuine action equals the certified physical numerator divided by two. -/
theorem generatedTenth_e7_xi_correction_apply (x : Fin 24 → ℝ) :
    generatedTenthE7XiCorrection.val x =
      (1 / 2 : ℝ) • (generatedTenthE7XiCorrectedNumerator.map (Int.castRingHom ℝ) *ᵥ x) := by
  ext i
  change qSign (generatedTenthE7XiCode.val i) *
    (co1XiMatrix *ᵥ x) (generatedTenthE7XiInverse i) = _
  have hc (j : Fin 24) : co1XiMatrix (generatedTenthE7XiInverse i) j =
      (co1XiNumerator (generatedTenthE7XiInverse i) j : ℝ) / 2 := by
    simp [co1XiMatrix, co1XiMatrixQ]
  rw [sign_cast]
  change _ * (∑ j, co1XiMatrix (generatedTenthE7XiInverse i) j * x j) =
    (1 / 2 : ℝ) * ∑ j, (generatedTenthE7XiCorrectedNumerator i j : ℝ) * x j
  simp_rw [hc, generatedTenthE7XiCorrectedNumerator, Int.cast_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem embedding_image (u v : Fin 24 → ℤ)
    (h : generatedTenthE7XiCorrectedNumerator *ᵥ u = (2 : ℤ) • v) :
    generatedTenthE7XiCorrection.val (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding v := by
  rw [generatedTenth_e7_xi_correction_apply, ← leechCoordinateEmbedding_mulVec, h]
  ext i
  change (1 / 2 : ℝ) * (((2 * v i : ℤ) : ℝ) / Real.sqrt 8) =
    (v i : ℝ) / Real.sqrt 8
  push_cast
  ring

/-- The complete original norm-twelve line is fixed with its positive orientation. -/
theorem generatedTenth_e7_xi_correction_line :
    generatedTenthE7XiCorrection.val (leechCoordinateEmbedding generatedTenthE7XiLine) =
      leechCoordinateEmbedding generatedTenthE7XiLine :=
  embedding_image _ _ generatedTenth_e7_xi_corrected_vectors.1

/-- The complete perpendicular norm-four root is fixed with its positive orientation. -/
theorem generatedTenth_e7_xi_correction_normal :
    generatedTenthE7XiCorrection.val (leechCoordinateEmbedding generatedTenthE7XiNormal) =
      leechCoordinateEmbedding generatedTenthE7XiNormal :=
  embedding_image _ _ generatedTenth_e7_xi_corrected_vectors.2.1

/-- The genuine move attains the distinct displayed E7 root with its exact sign. -/
theorem generatedTenth_e7_xi_correction_root :
    generatedTenthE7XiCorrection.val (leechCoordinateEmbedding generatedTenthE7XiRoot) =
      leechCoordinateEmbedding generatedTenthE7XiNextRoot :=
  embedding_image _ _ generatedTenth_e7_xi_corrected_vectors.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
