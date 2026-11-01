/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisMatrixTransposition

/-! Applying the matrix transposition calculation to the genuine Conway multiplication. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem axisMatrixContraction_short (r : GriessShortIndex)
    (M : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayShortPairing M r = axisMatrixContraction (griessShortVector r) M := by
  dsimp only [conwayShortPairing, axisMatrixContraction]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual raw matrix row is the row used in the polynomial calculation. -/
theorem conwayShortAxisRaw_matrix_row (r : GriessShortIndex) (c : ZMod 2)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ)
    (T : ConwayTensorSpace) :
    (conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T))).1 =
      axisMatrixRow (griessShortVector r) (qSign c) M (X r) := by
  ext i j
  exact conwayShortAxisRaw_product_matrix r c M X T i j

/-- The actual on-axis short row is the coupled row used in the calculation. -/
theorem conwayShortAxisRaw_short_row_on_axis (r : GriessShortIndex) (c : ZMod 2)
    (M : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ)
    (T : ConwayTensorSpace) :
    (conwayRawProduct (conwayShortAxisRaw r c) (M, (X, T))).2.1 r =
      axisMatrixShortRow (griessShortVector r) (qSign c) M (X r) := by
  rw [conwayShortAxisRaw_product_short, griessShortVector_self_pairing,
    conwayShortTranslation_self, axisMatrixContraction_short]
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
    mul_zero, add_zero, axisMatrixShortRow]
  ring

/-- Actual double axial multiplication satisfies the matrix transposition
polynomial for every actual short label and both signs. -/
theorem conwayShortAxisRaw_matrix_transposition_polynomial
    (r : GriessShortIndex) (c : ZMod 2) (U : ConwayRawSpace) (i j : Fin 24) :
    14 * U.1 i j -
      24 * (2 * axisMatrixContraction (griessShortVector r) U.1 - 8 * qSign c * U.2.1 r) *
        (2 * griessShortVector r i * griessShortVector r j) -
      16 * (conwayRawProduct (conwayShortAxisRaw r c) U).1 i j +
      (conwayRawProduct (conwayShortAxisRaw r c)
        (conwayRawProduct (conwayShortAxisRaw r c) U)).1 i j = 14 * U.1 i j := by
  rw [conwayShortAxisRaw_matrix_row, conwayShortAxisRaw_matrix_row,
    conwayShortAxisRaw_short_row_on_axis, conwayShortAxisRaw_matrix_row]
  exact axisMatrix_transposition_polynomial _ _ _ _ (griessShortVector_norm_sq r)
    (qSign_sq c) i j

/-- Actual double axial multiplication satisfies the transposition polynomial
on its on-axis short coordinate, including the actual rank-one term. -/
theorem conwayShortAxisRaw_short_on_axis_transposition_polynomial
    (r : GriessShortIndex) (c : ZMod 2) (U : ConwayRawSpace) :
    14 * U.2.1 r -
      24 * (2 * axisMatrixContraction (griessShortVector r) U.1 - 8 * qSign c * U.2.1 r) *
        (-8 * qSign c) -
      16 * (conwayRawProduct (conwayShortAxisRaw r c) U).2.1 r +
      (conwayRawProduct (conwayShortAxisRaw r c)
        (conwayRawProduct (conwayShortAxisRaw r c) U)).2.1 r = 14 * U.2.1 r := by
  rw [conwayShortAxisRaw_short_row_on_axis, conwayShortAxisRaw_short_row_on_axis,
    conwayShortAxisRaw_matrix_row, conwayShortAxisRaw_short_row_on_axis]
  exact axisMatrixShort_transposition_polynomial _ _ _ _ (griessShortVector_norm_sq r)
    (qSign_sq c)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
