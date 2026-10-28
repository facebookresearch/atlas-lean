/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Matrix-unit square and triangle relations for Jordan sign coherence. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanPeirce

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Products of ordinary coordinate matrix units. -/
theorem sym24_single_mul (i j k l : Fin 24) :
    Matrix.single i j (1 : ℝ) * Matrix.single k l 1 =
      if j = k then Matrix.single i l 1 else 0 := by
  rw [Matrix.single_eq_single_vecMulVec_single, Matrix.single_eq_single_vecMulVec_single,
    Matrix.vecMulVec_mul_vecMulVec]
  have hd : (Pi.single j (1 : ℝ) : Fin 24 → ℝ) ⬝ᵥ Pi.single k 1 =
      if j = k then 1 else 0 := by
    simp [dotProduct, Pi.single_apply, eq_comm]
  rw [hd]
  split_ifs
  · rw [one_smul, ← Matrix.single_eq_single_vecMulVec_single]
  · ext a b
    simp [Matrix.vecMulVec, Matrix.of_apply]

/-- The off-diagonal square is the sum of its two endpoint projectors. -/
theorem sym24OffDiagonalUnit_square (i j : Fin 24) (hij : i ≠ j) :
    (sym24OffDiagonalUnit i j).val * (sym24OffDiagonalUnit i j).val =
      (sym24DiagonalUnit i).val + (sym24DiagonalUnit j).val := by
  change (Matrix.single i j (1 : ℝ) + Matrix.single j i 1) *
    (Matrix.single i j 1 + Matrix.single j i 1) =
      Matrix.diagonal (Pi.single i 1) + Matrix.diagonal (Pi.single j 1)
  simp [add_mul, mul_add, hij, hij.symm, Matrix.diagonal_single, add_comm]

/-- The square relation in the Jordan algebra. -/
theorem sym24OffDiagonalUnit_jordan_square (i j : Fin 24) (hij : i ≠ j) :
    sym24Jordan (sym24OffDiagonalUnit i j) (sym24OffDiagonalUnit i j) =
      (2 : ℝ) • (sym24DiagonalUnit i + sym24DiagonalUnit j) := by
  apply Subtype.ext
  change (sym24OffDiagonalUnit i j).val * (sym24OffDiagonalUnit i j).val +
    (sym24OffDiagonalUnit i j).val * (sym24OffDiagonalUnit i j).val = _
  rw [sym24OffDiagonalUnit_square i j hij]
  simp only [two_smul]
  rfl

/-- The triangle product of three distinct indices. -/
theorem sym24OffDiagonalUnit_triangle (i j k : Fin 24)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    sym24Jordan (sym24OffDiagonalUnit i j) (sym24OffDiagonalUnit j k) =
      sym24OffDiagonalUnit i k := by
  apply Subtype.ext
  change (Matrix.single i j (1 : ℝ) + Matrix.single j i 1) *
      (Matrix.single j k 1 + Matrix.single k j 1) +
    (Matrix.single j k 1 + Matrix.single k j 1) *
      (Matrix.single i j 1 + Matrix.single j i 1) =
    Matrix.single i k 1 + Matrix.single k i 1
  simp [add_mul, mul_add, hij, hij.symm, hjk, hjk.symm, hik, hik.symm]

/-- Scalar bilinearity of the Jordan product. -/
theorem sym24Jordan_smul (a b : ℝ) (A B : Sym24) :
    sym24Jordan (a • A) (b • B) = (a * b) • sym24Jordan A B := by
  apply Subtype.ext
  change (a • A.val) * (b • B.val) + (b • B.val) * (a • A.val) =
    (a * b) • (A.val * B.val + B.val * A.val)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm b a, smul_add]

/-- The coefficient of a normalized off-diagonal image has square one. -/
theorem sym24Jordan_fixed_diagonal_coefficient_square (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hD : ∀ i, φ (sym24DiagonalUnit i) = sym24DiagonalUnit i)
    (i j : Fin 24) (hij : i ≠ j) :
    ((φ (sym24OffDiagonalUnit i j)).val i j) ^ 2 = 1 := by
  let c : ℝ := (φ (sym24OffDiagonalUnit i j)).val i j
  have hF : φ (sym24OffDiagonalUnit i j) = c • sym24OffDiagonalUnit i j :=
    sym24Jordan_fixed_diagonal_offDiagonal_image φ hJ hD i j hij
  have he := hJ (sym24OffDiagonalUnit i j) (sym24OffDiagonalUnit i j)
  rw [sym24OffDiagonalUnit_jordan_square i j hij, map_smul, map_add, hD, hD,
    hF, sym24Jordan_smul, sym24OffDiagonalUnit_jordan_square i j hij] at he
  have hi := congrArg (fun A : Sym24 => A.val i i) he
  change 2 * ((sym24DiagonalUnit i).val i i + (sym24DiagonalUnit j).val i i) =
    (c * c) * (2 * ((sym24DiagonalUnit i).val i i + (sym24DiagonalUnit j).val i i)) at hi
  simp [sym24DiagonalUnit, hij.symm] at hi
  change c ^ 2 = 1
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
