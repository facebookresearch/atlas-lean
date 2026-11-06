/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual short-coordinate square determines its positive matrix outer-product sum. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerPlusCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem matrixDiagonalSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (F : ι → Matrix (Fin 24) (Fin 24) ℝ) :
    (∑ s, if r = s then F s else 0) = F r := by
  simp only [Finset.sum_ite_eq]
  simp

/-- The matrix part of two short coordinates is their diagonal weighted outer-product sum. -/
theorem generatedCentral_short_matrix_product (X Y : GriessShortIndex → ℝ) :
    conwayShortShortMatrix X Y = ∑ r, (X r * Y r) •
      Matrix.vecMulVec (griessShortVector r) (griessShortVector r) := by
  unfold conwayShortShortMatrix
  apply Finset.sum_congr rfl
  intro r _
  simp only [griessShortQ_product_base_one_iff]
  rw [matrixDiagonalSum]
  rw [griessShortQ_square]
  have hc : Multiplicative.toAdd (1 : Q).coeff = 0 := rfl
  simp only [hc, qSign_zero, one_mul]

/-- The short-coordinate square has the positive coefficients needed for line recognition. -/
theorem generatedCentral_short_matrix_square (X : GriessShortIndex → ℝ) :
    conwayShortShortMatrix X X = ∑ r, (X r) ^ 2 •
      Matrix.vecMulVec (griessShortVector r) (griessShortVector r) := by
  simpa only [pow_two] using generatedCentral_short_matrix_product X X

/-- The actual Griess square's matrix coordinate is the positive short-vector sum. -/
theorem generatedCentral_short_square_encode (X : GriessShortIndex → ℝ) :
    (griessConwayEncode (griessProd (generatedCentralPlusEmbed 0 X).val
      (generatedCentralPlusEmbed 0 X).val)).1 =
      ∑ r, X r ^ 2 • Matrix.vecMulVec (griessShortVector r) (griessShortVector r) := by
  rw [griessProd_encode, generatedCentralPlusEmbed_encode, conwayRawProduct_eq_blocks]
  simp only [Submodule.coe_zero, conwayMatrixMatrixProduct, mul_zero,
    add_zero, smul_zero, map_zero, zero_add]
  exact generatedCentral_short_matrix_square X

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
