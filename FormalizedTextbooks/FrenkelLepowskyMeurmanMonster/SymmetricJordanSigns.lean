/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Coherent column signs for Jordan automorphisms fixing the coordinate projectors. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanUnits

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The off-diagonal coefficient of the image of the symmetric matrix unit. -/
def sym24JordanCoefficient (φ : Sym24 ≃ₗ[ℝ] Sym24) (i j : Fin 24) : ℝ :=
  (φ (sym24OffDiagonalUnit i j)).val i j

theorem sym24JordanCoefficient_swap (φ : Sym24 ≃ₗ[ℝ] Sym24) (i j : Fin 24) :
    sym24JordanCoefficient φ i j = sym24JordanCoefficient φ j i := by
  unfold sym24JordanCoefficient
  rw [← sym24OffDiagonalUnit_swap i j]
  have hs : (φ (sym24OffDiagonalUnit i j)).val.transpose =
      (φ (sym24OffDiagonalUnit i j)).val := (φ (sym24OffDiagonalUnit i j)).property
  exact congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A j i) hs

theorem sym24JordanCoefficient_triangle (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hD : ∀ i, φ (sym24DiagonalUnit i) = sym24DiagonalUnit i)
    (i j k : Fin 24) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    sym24JordanCoefficient φ i k = sym24JordanCoefficient φ i j * sym24JordanCoefficient φ j k := by
  have hFij : φ (sym24OffDiagonalUnit i j) =
      sym24JordanCoefficient φ i j • sym24OffDiagonalUnit i j :=
    sym24Jordan_fixed_diagonal_offDiagonal_image φ hJ hD i j hij
  have hFjk : φ (sym24OffDiagonalUnit j k) =
      sym24JordanCoefficient φ j k • sym24OffDiagonalUnit j k :=
    sym24Jordan_fixed_diagonal_offDiagonal_image φ hJ hD j k hjk
  have hFik : φ (sym24OffDiagonalUnit i k) =
      sym24JordanCoefficient φ i k • sym24OffDiagonalUnit i k :=
    sym24Jordan_fixed_diagonal_offDiagonal_image φ hJ hD i k hik
  have he := hJ (sym24OffDiagonalUnit i j) (sym24OffDiagonalUnit j k)
  rw [sym24OffDiagonalUnit_triangle i j k hij hjk hik, hFik, hFij, hFjk,
    sym24Jordan_smul, sym24OffDiagonalUnit_triangle i j k hij hjk hik] at he
  have hi := congrArg (fun A : Sym24 => A.val i k) he
  simpa [sym24OffDiagonalUnit, Matrix.single_apply, hik.symm] using hi

theorem sym24OffDiagonalUnit_same (i : Fin 24) :
    sym24OffDiagonalUnit i i = (2 : ℝ) • sym24DiagonalUnit i := by
  apply Subtype.ext
  change Matrix.single i i (1 : ℝ) + Matrix.single i i 1 =
    (2 : ℝ) • Matrix.diagonal (Pi.single i 1)
  rw [Matrix.diagonal_single, two_smul]

/-- The triangle relations make every normalized image sign a product of column signs. -/
theorem sym24Jordan_fixed_diagonal_signs (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hD : ∀ i, φ (sym24DiagonalUnit i) = sym24DiagonalUnit i) :
    ∃ ε : Fin 24 → ℝ, (∀ i, ε i ^ 2 = 1) ∧ ∀ i j,
      φ (sym24OffDiagonalUnit i j) = (ε i * ε j) • sym24OffDiagonalUnit i j := by
  let ε : Fin 24 → ℝ := fun i => if i = 0 then 1 else sym24JordanCoefficient φ 0 i
  have hsq (i : Fin 24) : ε i ^ 2 = 1 := by
    by_cases hi : i = 0
    · simp [ε, hi]
    · simpa only [ε, hi, ite_false, sym24JordanCoefficient] using
        sym24Jordan_fixed_diagonal_coefficient_square φ hJ hD 0 i (Ne.symm hi)
  have hc (i j : Fin 24) (hij : i ≠ j) :
      sym24JordanCoefficient φ i j = ε i * ε j := by
    by_cases hi : i = 0
    · subst i; simp [ε, hij.symm]
    · by_cases hj : j = 0
      · subst j
        rw [sym24JordanCoefficient_swap]
        simp [ε, hi]
      · rw [sym24JordanCoefficient_triangle φ hJ hD i 0 j hi (Ne.symm hj) hij,
          sym24JordanCoefficient_swap φ i 0]
        simp [ε, hi, hj]
  refine ⟨ε, hsq, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    have hm : ε i * ε i = 1 := by simpa only [pow_two] using hsq i
    rw [hm, one_smul, sym24OffDiagonalUnit_same, map_smul, hD]
  · rw [← hc i j hij]
    exact sym24Jordan_fixed_diagonal_offDiagonal_image φ hJ hD i j hij

/-- Symmetric off-diagonal units span every real symmetric matrix. -/
theorem sym24_sum_offDiagonalUnits (A : Sym24) :
    (∑ i, ∑ j, A.val i j • sym24OffDiagonalUnit i j) = (2 : ℝ) • A := by
  apply Subtype.ext
  change (∑ i, ∑ j, A.val i j • (Matrix.single i j 1 + Matrix.single j i 1)) =
    (2 : ℝ) • A.val
  simp only [smul_add, Finset.sum_add_distrib, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [← Matrix.matrix_eq_sum_single A.val]
  have ht : (∑ i, ∑ j, Matrix.single j i (A.val i j)) = A.val.transpose := by
    rw [Finset.sum_comm]
    exact (Matrix.matrix_eq_sum_single A.val.transpose).symm
  rw [ht, show A.val.transpose = A.val from A.property, two_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
