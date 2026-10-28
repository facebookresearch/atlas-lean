/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Orthogonal conjugation maps on the actual symmetric Jordan constituent. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanSigns

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Conjugation by a real matrix preserves symmetry. -/
def sym24ConjugationLinear (O : Matrix (Fin 24) (Fin 24) ℝ) : Sym24 →ₗ[ℝ] Sym24 where
  toFun A := ⟨O * A.val * O.transpose, by
    change (O * A.val * O.transpose).transpose = O * A.val * O.transpose
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      show A.val.transpose = A.val from A.property]
    simp only [mul_assoc]⟩
  map_add' A B := by
    apply Subtype.ext
    change O * (A.val + B.val) * O.transpose = _
    rw [mul_add, add_mul]
    rfl
  map_smul' c A := by
    apply Subtype.ext
    change O * (c • A.val) * O.transpose = c • (O * A.val * O.transpose)
    rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem sym24ConjugationLinear_val (O : Matrix (Fin 24) (Fin 24) ℝ) (A : Sym24) :
    (sym24ConjugationLinear O A).val = O * A.val * O.transpose := rfl

/-- Orthogonal column normalization gives an actual linear equivalence on the constituent. -/
def sym24ConjugationEquiv (O : Matrix (Fin 24) (Fin 24) ℝ)
    (hL : O.transpose * O = 1) (hR : O * O.transpose = 1) : Sym24 ≃ₗ[ℝ] Sym24 where
  toFun := sym24ConjugationLinear O
  invFun := sym24ConjugationLinear O.transpose
  left_inv A := by
    apply Subtype.ext
    change O.transpose * (O * A.val * O.transpose) * O.transpose.transpose = A.val
    rw [Matrix.transpose_transpose]
    calc
      _ = (O.transpose * O) * A.val * (O.transpose * O) := by noncomm_ring
      _ = A.val := by rw [hL]; simp
  right_inv A := by
    apply Subtype.ext
    change O * (O.transpose * A.val * O.transpose.transpose) * O.transpose = A.val
    rw [Matrix.transpose_transpose]
    calc
      _ = (O * O.transpose) * A.val * (O * O.transpose) := by noncomm_ring
      _ = A.val := by rw [hR]; simp
  map_add' := (sym24ConjugationLinear O).map_add
  map_smul' := (sym24ConjugationLinear O).map_smul

/-- Orthogonal conjugation preserves ordinary matrix multiplication. -/
theorem sym24Conjugation_matrix_mul (O : Matrix (Fin 24) (Fin 24) ℝ)
    (hL : O.transpose * O = 1) (A B : Matrix (Fin 24) (Fin 24) ℝ) :
    (O * A * O.transpose) * (O * B * O.transpose) = O * (A * B) * O.transpose := by
  calc
    _ = O * A * (O.transpose * O) * B * O.transpose := by noncomm_ring
    _ = _ := by rw [hL]; simp only [mul_one, mul_assoc]

/-- Orthogonal conjugation preserves the actual Jordan product. -/
theorem sym24Conjugation_jordan (O : Matrix (Fin 24) (Fin 24) ℝ)
    (hL : O.transpose * O = 1) (A B : Sym24) :
    sym24ConjugationLinear O (sym24Jordan A B) =
      sym24Jordan (sym24ConjugationLinear O A) (sym24ConjugationLinear O B) := by
  apply Subtype.ext
  change O * (A.val * B.val + B.val * A.val) * O.transpose =
    (O * A.val * O.transpose) * (O * B.val * O.transpose) +
      (O * B.val * O.transpose) * (O * A.val * O.transpose)
  rw [sym24Conjugation_matrix_mul O hL, sym24Conjugation_matrix_mul O hL]
  rw [mul_add, add_mul]

/-- The diagonal sign conjugation has the expected entry formula. -/
theorem sym24DiagonalConjugation_apply (ε : Fin 24 → ℝ) (A : Sym24) (i j : Fin 24) :
    (sym24ConjugationLinear (Matrix.diagonal ε) A).val i j = ε i * A.val i j * ε j := by
  simp [sym24ConjugationLinear, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Diagonal conjugation acts on every symmetric matrix unit by the product of its column signs. -/
theorem sym24DiagonalConjugation_offDiagonalUnit (ε : Fin 24 → ℝ) (i j : Fin 24) :
    sym24ConjugationLinear (Matrix.diagonal ε) (sym24OffDiagonalUnit i j) =
      (ε i * ε j) • sym24OffDiagonalUnit i j := by
  apply Subtype.ext
  ext k l
  rw [sym24DiagonalConjugation_apply]
  change ε k * ((if i = k ∧ j = l then 1 else 0) +
      (if j = k ∧ i = l then 1 else 0)) * ε l =
    (ε i * ε j) * ((if i = k ∧ j = l then 1 else 0) +
      (if j = k ∧ i = l then 1 else 0))
  by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l
  all_goals simp_all <;> ring

/-- Agreement on the symmetric matrix units gives agreement everywhere. -/
theorem sym24Linear_ext_offDiagonalUnits (f g : Sym24 →ₗ[ℝ] Sym24)
    (h : ∀ i j, f (sym24OffDiagonalUnit i j) = g (sym24OffDiagonalUnit i j)) : f = g := by
  apply LinearMap.ext
  intro A
  have hh : (2 : ℝ) • f A = (2 : ℝ) • g A := by
    rw [← map_smul, ← map_smul, ← sym24_sum_offDiagonalUnits A]
    simp only [map_sum, map_smul, h]
  apply Subtype.ext
  ext i j
  have hi := congrArg (fun B : Sym24 => B.val i j) hh
  change 2 * (f A).val i j = 2 * (g A).val i j at hi
  linarith

/-- A Jordan automorphism fixing every coordinate projector is a diagonal sign conjugation. -/
theorem sym24Jordan_fixed_diagonal_conjugation (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hD : ∀ i, φ (sym24DiagonalUnit i) = sym24DiagonalUnit i) :
    ∃ ε : Fin 24 → ℝ, (∀ i, ε i ^ 2 = 1) ∧
      ∀ A, (φ A).val = Matrix.diagonal ε * A.val * (Matrix.diagonal ε).transpose := by
  obtain ⟨ε, hε, hF⟩ := sym24Jordan_fixed_diagonal_signs φ hJ hD
  have he : φ.toLinearMap = sym24ConjugationLinear (Matrix.diagonal ε) := by
    apply sym24Linear_ext_offDiagonalUnits
    intro i j
    rw [sym24DiagonalConjugation_offDiagonalUnit]
    exact hF i j
  refine ⟨ε, hε, ?_⟩
  intro A
  exact congrArg (fun f : Sym24 →ₗ[ℝ] Sym24 => (f A).val) he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
