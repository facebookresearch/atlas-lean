/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Diagonal projector images under actual real symmetric Jordan automorphisms. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SymmetricJordanAutomorphism
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A standard rank-one diagonal projector in the symmetric constituent. -/
def sym24DiagonalUnit (i : Fin 24) : Sym24 :=
  ⟨Matrix.diagonal (Pi.single i 1), by simp⟩

theorem sym24DiagonalUnit_square (i : Fin 24) :
    (sym24DiagonalUnit i).val * (sym24DiagonalUnit i).val = (sym24DiagonalUnit i).val := by
  change Matrix.diagonal (Pi.single i (1 : ℝ)) * Matrix.diagonal (Pi.single i (1 : ℝ)) = _
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  ext j
  by_cases h : i = j <;> simp [h]

theorem sym24DiagonalUnit_trace (i : Fin 24) : Matrix.trace (sym24DiagonalUnit i).val = 1 := by
  simp [sym24DiagonalUnit, Matrix.trace]

/-- Jordan preservation transports all symmetric idempotents. -/
theorem sym24Jordan_image_idempotent (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (A : Sym24) (hA : A.val * A.val = A.val) : (φ A).val * (φ A).val = (φ A).val := by
  have hh : sym24Jordan A A = (2 : ℝ) • A := by
    apply Subtype.ext
    change A.val * A.val + A.val * A.val = (2 : ℝ) • A.val
    rw [hA]
    simp only [two_smul]
  have he := hJ A A
  rw [hh, map_smul] at he
  ext i j
  have hi := congrArg (fun B : Sym24 => B.val i j) he
  change 2 * (φ A).val i j = ((φ A).val * (φ A).val) i j +
    ((φ A).val * (φ A).val) i j at hi
  linarith

/-- Every diagonal-unit image is a genuine rank-one unit-vector projector. -/
theorem sym24Jordan_diagonalUnit_image (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hT : ∀ A B, Matrix.trace ((φ A).val * (φ B).val) = Matrix.trace (A.val * B.val))
    (i : Fin 24) : ∃ v : Fin 24 → ℝ, (∑ k, v k ^ 2 = 1) ∧
      (φ (sym24DiagonalUnit i)).val = Matrix.vecMulVec v v := by
  have hid := sym24Jordan_image_idempotent φ hJ (sym24DiagonalUnit i)
    (sym24DiagonalUnit_square i)
  have ht := hT (sym24DiagonalUnit i) (sym24DiagonalUnit i)
  rw [hid, sym24DiagonalUnit_square, sym24DiagonalUnit_trace] at ht
  exact symmetric_idempotent_trace_one_eq_vecMulVec _ (φ (sym24DiagonalUnit i)).property hid ht

/-- The Frobenius pairing of unit-vector projectors is the square of the vector pairing. -/
theorem sym24_projector_trace_product (v w : Fin 24 → ℝ) :
    Matrix.trace (Matrix.vecMulVec v v * Matrix.vecMulVec w w) = (v ⬝ᵥ w) ^ 2 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec]
  simp only [dotProduct_smul, smul_eq_mul, pow_two]

/-- Distinct diagonal units have zero Frobenius pairing. -/
theorem sym24DiagonalUnit_trace_product_of_ne (i j : Fin 24) (hij : i ≠ j) :
    Matrix.trace ((sym24DiagonalUnit i).val * (sym24DiagonalUnit j).val) = 0 := by
  change Matrix.trace (Matrix.diagonal (Pi.single i (1 : ℝ)) *
    Matrix.diagonal (Pi.single j (1 : ℝ))) = 0
  rw [Matrix.diagonal_mul_diagonal]
  have hf : (Pi.single i (1 : ℝ) : Fin 24 → ℝ) * Pi.single j 1 = 0 := by
    ext k
    by_cases hk : i = k
    · subst k; simp [hij.symm]
    · simp [hk]
  change Matrix.trace (Matrix.diagonal
    ((Pi.single i (1 : ℝ) : Fin 24 → ℝ) * Pi.single j 1)) = 0
  rw [hf]
  simp

/-- The diagonal unit is the projector onto its coordinate vector. -/
theorem sym24DiagonalUnit_vecMulVec (i : Fin 24) :
    (sym24DiagonalUnit i).val = Matrix.vecMulVec (Pi.single i 1) (Pi.single i 1) := by
  change Matrix.diagonal (Pi.single i (1 : ℝ)) = _
  rw [Matrix.diagonal_single, Matrix.single_eq_single_vecMulVec_single]

/-- Jordan and Frobenius preservation give orthogonal columns realizing all diagonal-unit images. -/
theorem sym24Jordan_diagonalUnit_images_orthogonal (φ : Sym24 ≃ₗ[ℝ] Sym24)
    (hJ : ∀ A B, φ (sym24Jordan A B) = sym24Jordan (φ A) (φ B))
    (hT : ∀ A B, Matrix.trace ((φ A).val * (φ B).val) = Matrix.trace (A.val * B.val)) :
    ∃ O : Matrix (Fin 24) (Fin 24) ℝ, O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      ∀ i : Fin 24, (φ (sym24DiagonalUnit i)).val =
        O * (sym24DiagonalUnit i).val * O.transpose := by
  choose v hv using fun i => sym24Jordan_diagonalUnit_image φ hJ hT i
  have ho (i j : Fin 24) : v i ⬝ᵥ v j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true, dotProduct, pow_two] using (hv i).1
    · have ht := hT (sym24DiagonalUnit i) (sym24DiagonalUnit j)
      rw [(hv i).2, (hv j).2, sym24_projector_trace_product,
        sym24DiagonalUnit_trace_product_of_ne i j hij] at ht
      simpa only [hij, ite_false] using sq_eq_zero_iff.mp ht
  let O : Matrix (Fin 24) (Fin 24) ℝ := fun k i => v i k
  have hleft : O.transpose * O = 1 := by
    ext i j
    change (∑ k, v i k * v j k) = if i = j then 1 else 0
    exact ho i j
  refine ⟨O, hleft, mul_eq_one_comm.mp hleft, ?_⟩
  intro i
  rw [(hv i).2, sym24DiagonalUnit_vecMulVec, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  have hu : O *ᵥ Pi.single i 1 = v i := by
    ext k
    simp [Matrix.mulVec, dotProduct, O, Pi.single_apply, mul_ite]
  rw [hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
