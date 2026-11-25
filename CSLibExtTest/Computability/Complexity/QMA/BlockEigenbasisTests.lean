/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QMA.BlockEigenbasis

@[expose] public section

namespace Cslib.Complexity.Classes.QMA.BlockEigenbasisTests

open scoped Matrix
open Cslib.Complexity.Classes
open Cslib.Complexity.Classes.QMA

/-- For one block, reading the sole digit recovers the input index. -/
theorem blockDigit_one_apply (m : ℕ) (s : Fin (2 ^ (1 * m))) :
    blockDigit 1 m 0 s =
      Fin.cast (by rw [one_mul]) s := by
  have hs : s.val < 2 ^ m := by
    have h := s.isLt
    simpa [one_mul] using h
  have hmod : s.val % 2 ^ m = s.val := by
    first
      | exact Nat.mod_eq_of_lt _ _ hs
      | exact Nat.mod_eq_of_lt _ hs
      | exact Nat.mod_eq_of_lt hs
  ext
  simp [blockDigit, Nat.div_one, hmod]

/-- For one block, the block product is the given vector after the index
cast. -/
theorem blockProd_one_apply {m : ℕ}
    (ψ : Fin 1 → Fin (2 ^ m) → ℂ) (s : Fin (2 ^ (1 * m))) :
    blockProd ψ s = ψ 0 (Fin.cast (by rw [one_mul]) s) := by
  first
    | simp only [blockProd, Fin.prod_univ_one, blockDigit_one_apply]
    | simp only [blockProd, Fin.univ_one, Finset.prod_singleton,
      blockDigit_one_apply]

/-- For two one-qubit blocks, the block product agrees with Atlas
`tensorProd` on every index. -/
theorem blockProd_two_one_apply
    (φ ψ : Fin (2 ^ 1) → ℂ) (s : Fin (2 ^ (2 * 1))) :
    blockProd ![φ, ψ] s =
      tensorProd φ ψ
        (Fin.cast (by norm_num) s) := by
  have hs4 : s.val < 4 := s.isLt
  have hdiv2 : s.val / 2 < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hmod2 : s.val / 2 % 2 = s.val / 2 := by
    first
      | exact Nat.mod_eq_of_lt _ _ hdiv2
      | exact Nat.mod_eq_of_lt _ hdiv2
      | exact Nat.mod_eq_of_lt hdiv2
  have hd0 : blockDigit 2 1 0 s
      = ⟨s.val % 2 ^ 1, Nat.mod_lt _ (by positivity)⟩ := by
    ext
    simp [blockDigit, Nat.div_one]
  have hd1 : blockDigit 2 1 1 s
      = ⟨s.val / 2 ^ 1, by simpa using hdiv2⟩ := by
    ext
    simp only [blockDigit]
    rw [show ((1 : Fin 2).val * 1) = 1 by simp, pow_one (2 : ℕ)]
    exact hmod2
  simp only [blockProd, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, hd0, hd1, tensorProd]
  congr 1

/-- The squared norm of an explicit two-block product of basis vectors. -/
theorem sqNorm_blockProd_basis :
    sqNorm
      (blockProd
        ![fun s : Fin (2 ^ 1) => if s = 0 then 1 else 0,
          fun s : Fin (2 ^ 1) => if s = 1 then 1 else 0]) = 1 := by
  rw [sqNorm_blockProd_eq_one]
  intro i
  fin_cases i <;>
    simp [sqNorm, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]

theorem diag01_isHermitian :
    (Matrix.diagonal ![0, 1] :
      Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).IsHermitian := by
  show (Matrix.diagonal ![0, 1] :
    Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)ᴴ =
    (Matrix.diagonal ![0, 1] :
      Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The threshold action instantiated for an explicit diagonal Hermitian
matrix. -/
theorem thresholdBlockOp_diagonal_apply
    (b : Fin 2 → Bool) (j : Fin 2 → Fin (2 ^ 1)) :
    thresholdBlockOp
        (Matrix.diagonal ![0, 1] : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) b *ᵥ
      productEigenvector diag01_isHermitian j =
      (∏ i, if b i then
          ((diag01_isHermitian.eigenvalues (j i) : ℝ) : ℂ)
        else 1 - ((diag01_isHermitian.eigenvalues (j i) : ℝ) : ℂ)) •
        productEigenvector diag01_isHermitian j :=
  thresholdBlockOp_mulVec_productEigenvector diag01_isHermitian b j

#print axioms blockOp_mulVec_blockProd
#print axioms star_blockProd_dotProduct_blockProd
#print axioms blockExpectation_blockProd
#print axioms sqNorm_blockProd
#print axioms orthonormal_productEigenvector
#print axioms thresholdBlockOp_mulVec_productEigenvector

end Cslib.Complexity.Classes.QMA.BlockEigenbasisTests
