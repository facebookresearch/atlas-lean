/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Coordinate Peirce spaces of the actual symmetric Jordan constituent. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanProjectorImages

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The symmetric off-diagonal matrix unit. -/
def sym24OffDiagonalUnit (i j : Fin 24) : Sym24 :=
  ⟨Matrix.single i j 1 + Matrix.single j i 1, by
    change (Matrix.single i j (1 : ℝ) + Matrix.single j i 1).transpose = _
    rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]⟩

/-- Left and right multiplication by a coordinate projector select its row and column. -/
theorem sym24DiagonalUnit_jordan_apply (i : Fin 24)
    (X : Matrix (Fin 24) (Fin 24) ℝ) (k l : Fin 24) :
    ((sym24DiagonalUnit i).val * X + X * (sym24DiagonalUnit i).val) k l =
      (if i = k then 1 else 0) * X k l + X k l * (if i = l then 1 else 0) := by
  change (Matrix.diagonal (Pi.single i (1 : ℝ)) * X +
    X * Matrix.diagonal (Pi.single i (1 : ℝ))) k l = _
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.single_apply, eq_comm]

/-- The intersection of the two eigenvalue-one Peirce spaces is the off-diagonal line. -/
theorem sym24_peirce_eq_scalar (X : Sym24) (i j : Fin 24) (hij : i ≠ j)
    (hi : sym24Jordan (sym24DiagonalUnit i) X = X)
    (hj : sym24Jordan (sym24DiagonalUnit j) X = X) :
    X = X.val i j • sym24OffDiagonalUnit i j := by
  apply Subtype.ext
  ext k l
  have hki := congrArg (fun A : Sym24 => A.val k l) hi
  have hkj := congrArg (fun A : Sym24 => A.val k l) hj
  change ((sym24DiagonalUnit i).val * X.val + X.val * (sym24DiagonalUnit i).val) k l =
    X.val k l at hki
  change ((sym24DiagonalUnit j).val * X.val + X.val * (sym24DiagonalUnit j).val) k l =
    X.val k l at hkj
  rw [sym24DiagonalUnit_jordan_apply] at hki hkj
  have hSym (a b : Fin 24) : X.val a b = X.val b a := by
    have hs : X.val.transpose = X.val := X.property
    exact congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A b a) hs
  change X.val k l = X.val i j *
    ((if i = k ∧ j = l then 1 else 0) + (if j = k ∧ i = l then 1 else 0))
  by_cases hik : i = k
  · subst k
    by_cases hil : i = l
    · subst l
      simp only [ite_true, one_mul, mul_one] at hki
      simp only [hij.symm, and_false, false_and, ite_false, zero_add, mul_zero]
      linarith
    · by_cases hjl : j = l
      · subst l
        simp [hij]
      · simp only [hij.symm, hjl, ite_false, zero_mul, mul_zero, add_zero] at hkj
        simpa only [eq_self_iff_true, true_and, hjl, hil, hij.symm, false_and,
          ite_false, zero_add, mul_zero] using hkj.symm
  · by_cases hil : i = l
    · subst l
      by_cases hjk : j = k
      · subst k
        simpa [hij, hij.symm] using hSym j i
      · simp only [hjk, hij.symm, ite_false, zero_mul, mul_zero, add_zero] at hkj
        simpa only [hik, hjk, false_and, and_false, ite_false, add_zero, mul_zero]
          using hkj.symm
    · simp only [hik, hil, ite_false, zero_mul, mul_zero, add_zero] at hki
      simpa only [hik, hil, false_and, and_false, ite_false, add_zero, mul_zero]
        using hki.symm

/-- The standard off-diagonal unit lies in both corresponding eigenvalue-one Peirce spaces. -/
theorem sym24OffDiagonalUnit_peirce (i j : Fin 24) (hij : i ≠ j) :
    sym24Jordan (sym24DiagonalUnit i) (sym24OffDiagonalUnit i j) =
      sym24OffDiagonalUnit i j := by
  apply Subtype.ext
  ext k l
  change ((sym24DiagonalUnit i).val * (sym24OffDiagonalUnit i j).val +
    (sym24OffDiagonalUnit i j).val * (sym24DiagonalUnit i).val) k l = _
  rw [sym24DiagonalUnit_jordan_apply]
  change (if i = k then (1 : ℝ) else 0) *
      ((if i = k ∧ j = l then 1 else 0) + (if j = k ∧ i = l then 1 else 0)) +
    ((if i = k ∧ j = l then 1 else 0) + (if j = k ∧ i = l then 1 else 0)) *
      (if i = l then 1 else 0) =
      ((if i = k ∧ j = l then 1 else 0) + (if j = k ∧ i = l then 1 else 0))
  by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l
  all_goals simp_all

/-- Swapping the two indices leaves the symmetric matrix unit unchanged. -/
theorem sym24OffDiagonalUnit_swap (i j : Fin 24) :
    sym24OffDiagonalUnit i j = sym24OffDiagonalUnit j i := by
  apply Subtype.ext
  exact add_comm _ _

/-- Fixing diagonal projectors forces every off-diagonal image to be a scalar multiple. -/
theorem sym24Jordan_fixed_diagonal_offDiagonal_image (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hD : ∀ i, φ (sym24DiagonalUnit i) = sym24DiagonalUnit i)
    (i j : Fin 24) (hij : i ≠ j) :
    φ (sym24OffDiagonalUnit i j) =
      (φ (sym24OffDiagonalUnit i j)).val i j • sym24OffDiagonalUnit i j := by
  apply sym24_peirce_eq_scalar _ i j hij
  · rw [← hD i, ← hJ, sym24OffDiagonalUnit_peirce i j hij]
  · rw [← hD j, ← hJ, sym24OffDiagonalUnit_swap i j,
      sym24OffDiagonalUnit_peirce j i hij.symm, sym24OffDiagonalUnit_swap j i]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
