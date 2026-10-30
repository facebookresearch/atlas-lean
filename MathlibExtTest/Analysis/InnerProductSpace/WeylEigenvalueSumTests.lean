/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.WeylEigenvalueSum

/-!
# Tests for Weyl's eigenvalue inequalities for a sum
-/

open MathlibExt.Analysis.InnerProductSpace.WeylEigenvalueSum

namespace WeylEigenvalueSumTests

/-- Antitonicity of a two-entry diagonal `![a, b]` with `b ≤ a`. -/
private lemma antitone_pair {a b : ℝ} (h : b ≤ a) : Antitone (![a, b] : Fin 2 → ℝ) := by
  rw [Antitone]
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro _; exact le_refl _
  · intro _; simpa using h
  · intro hij; exact absurd hij (by decide)
  · intro _; exact le_refl _

/-- The two diagonal matrices used in the concrete tests. -/
private noncomputable abbrev Adiag : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => ((![2, 0] i : ℝ) : ℂ))

/-- The two diagonal matrices used in the concrete tests. -/
private noncomputable abbrev Bdiag : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => ((![1, 0] i : ℝ) : ℂ))

private lemma isSelfAdjoint_ofReal_fun {n : ℕ} (d : Fin n → ℝ) :
    IsSelfAdjoint (fun i => (d i : ℂ)) := by
  funext i
  rw [Pi.star_apply, RCLike.star_def]
  exact RCLike.conj_ofReal _

private lemma isHermitian_diagonal_ofReal {n : ℕ} (d : Fin n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian :=
  Matrix.isHermitian_diagonal_of_self_adjoint _ (isSelfAdjoint_ofReal_fun d)

private lemma hermitian_Adiag : Adiag.IsHermitian :=
  isHermitian_diagonal_ofReal ![2, 0]

private lemma hermitian_Bdiag : Bdiag.IsHermitian :=
  isHermitian_diagonal_ofReal ![1, 0]

/-- `Adiag + Bdiag` is the diagonal matrix with entries `![3, 0]`. -/
private lemma Adiag_add_Bdiag :
    Adiag + Bdiag = Matrix.diagonal (fun i => ((![3, 0] i : ℝ) : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Adiag, Bdiag]
  norm_num

/-- Eigenvalues of `Adiag` are `![2, 0]`. -/
private lemma eigenvalues₀_Adiag (i : Fin (Fintype.card (Fin 2))) :
    Matrix.IsHermitian.eigenvalues₀ hermitian_Adiag i =
      ![2, 0] ⟨i.val, by simpa using i.isLt⟩ :=
  Matrix.IsHermitian.eigenvalues₀_diagonal_of_antitone
    (antitone_pair (by norm_num)) i

/-- Eigenvalues of `Bdiag` are `![1, 0]`. -/
private lemma eigenvalues₀_Bdiag (i : Fin (Fintype.card (Fin 2))) :
    Matrix.IsHermitian.eigenvalues₀ hermitian_Bdiag i =
      ![1, 0] ⟨i.val, by simpa using i.isLt⟩ :=
  Matrix.IsHermitian.eigenvalues₀_diagonal_of_antitone
    (antitone_pair (by norm_num)) i

/-- Eigenvalues of `Adiag + Bdiag = diag(3, 0)` are `![3, 0]`. -/
private lemma eigenvalues₀_Adiag_add_Bdiag (i : Fin (Fintype.card (Fin 2))) :
    Matrix.IsHermitian.eigenvalues₀
        (Matrix.IsHermitian.add hermitian_Adiag hermitian_Bdiag) i =
      ![3, 0] ⟨i.val, by simpa using i.isLt⟩ := by
  calc Matrix.IsHermitian.eigenvalues₀
          (Matrix.IsHermitian.add hermitian_Adiag hermitian_Bdiag) i
      = Matrix.IsHermitian.eigenvalues₀ (isHermitian_diagonal_ofReal ![3, 0]) i :=
        congrFun (Matrix.IsHermitian.eigenvalues₀_congr Adiag_add_Bdiag _ _) i
    _ = ![3, 0] ⟨i.val, by simpa using i.isLt⟩ :=
        Matrix.IsHermitian.eigenvalues₀_diagonal_of_antitone
          (antitone_pair (by norm_num)) i

/-- Weyl upper bound, instantiated: `λ₁(diag(3, 0)) = 0 ≤ λ₁(diag(2, 0)) +
λ₀(diag(1, 0)) = 0 + 1`. -/
example : (0 : ℝ) ≤ 0 + 1 := by
  have h := Matrix.IsHermitian.eigenvalues₀_add_le hermitian_Adiag hermitian_Bdiag
    (a := 1) (b := 0) (by norm_num) (by norm_num) (by norm_num)
  rw [eigenvalues₀_Adiag_add_Bdiag, eigenvalues₀_Adiag, eigenvalues₀_Bdiag] at h
  exact h

/-- Weyl upper bound at `a = b = 0`: `λ₀(diag(3, 0)) = 3 ≤ 2 + 1`. -/
example : (3 : ℝ) ≤ 2 + 1 := by
  have h := Matrix.IsHermitian.eigenvalues₀_add_le hermitian_Adiag hermitian_Bdiag
    (a := 0) (b := 0) (by norm_num) (by norm_num) (by norm_num)
  rw [eigenvalues₀_Adiag_add_Bdiag, eigenvalues₀_Adiag, eigenvalues₀_Bdiag] at h
  exact h

/-- Weyl lower bound at `a = 0, b = 1`: `λ₀(diag(2, 0)) + λ₁(diag(1, 0)) =
2 + 0 ≤ λ₀(diag(3, 0)) = 3`. -/
example : (2 : ℝ) + 0 ≤ 3 := by
  have h := Matrix.IsHermitian.le_eigenvalues₀_add hermitian_Adiag hermitian_Bdiag
    (a := 0) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  rw [eigenvalues₀_Adiag_add_Bdiag, eigenvalues₀_Adiag, eigenvalues₀_Bdiag] at h
  exact h

/-- Weyl lower bound at `a = b = 1`: `λ₁(diag(2, 0)) + λ₁(diag(1, 0)) =
0 + 0 ≤ λ₁(diag(3, 0)) = 0`, a sharp instance. -/
example : (0 : ℝ) + 0 ≤ 0 := by
  have h := Matrix.IsHermitian.le_eigenvalues₀_add hermitian_Adiag hermitian_Bdiag
    (a := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  rw [eigenvalues₀_Adiag_add_Bdiag, eigenvalues₀_Adiag, eigenvalues₀_Bdiag] at h
  exact h

/-- Operator form: the top eigenvalue is subadditive for symmetric operators. -/
example {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T S : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (h0 : 0 < n) :
    (hT.add hS).eigenvalues hn ⟨0, h0⟩ ≤
      hT.eigenvalues hn ⟨0, h0⟩ + hS.eigenvalues hn ⟨0, h0⟩ :=
  weyl_eigenvalue_add_le hT hS hn h0 h0 h0

/-- Operator form, lower bound: the bottom eigenvalue is superadditive. -/
example {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T S : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (h0 : 0 < n) :
    hT.eigenvalues hn ⟨n - 1, by omega⟩ + hS.eigenvalues hn ⟨n - 1, by omega⟩ ≤
      (hT.add hS).eigenvalues hn ⟨(n - 1) + (n - 1) - (n - 1), by omega⟩ :=
  le_weyl_eigenvalue_add hT hS hn (by omega) (by omega) (by omega)

end WeylEigenvalueSumTests
