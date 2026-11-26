/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Determinant of the MAX/MIN matrix pencil

The first and last columns of the MIN matrix are respectively constant and equal to the
sample vector. Factoring out the MIN matrix therefore leaves a correction to a scalar
matrix supported in two rows. Reordering those rows and the matching columns isolates a
`2 × 2` block whose determinant gives the two endpoint-dependent roots.
-/

open Matrix Polynomial

namespace MetaMathlibExt

/-- Put the first and last sample indices before the interior ones. -/
private def endpointOrder (k : ℕ) : Fin 2 ⊕ Fin k ≃ Fin (k + 2) where
  toFun := Sum.elim (fun i => if i = 0 then 0 else (Fin.last k).succ)
    (fun i => i.castSucc.succ)
  invFun := Fin.cases (Sum.inl 0) (Fin.lastCases (Sum.inl 1) Sum.inr)
  left_inv := by
    rintro (i | i)
    · have h1 : (1 : Fin 2) ≠ 0 := by decide
      fin_cases i
      · rfl
      · change Fin.cases (Sum.inl 0) (Fin.lastCases (Sum.inl 1) Sum.inr)
          (if (1 : Fin 2) = 0 then 0 else (Fin.last k).succ) = Sum.inl 1
        simp only [ite_eq_right h1, Fin.cases_succ, Fin.lastCases_last]
    · simp
  right_inv := by
    refine Fin.cases (by simp) (Fin.lastCases ?_ ?_)
    · have h1 : (1 : Fin 2) ≠ 0 := by decide
      simp only [Fin.cases_succ, Fin.lastCases_last, Sum.elim_inl, ite_eq_right h1]
    · intro i
      simp

/-- The factor multiplying the MIN matrix on the right. -/
private noncomputable def pencilEndFactor (k : ℕ) (s : Fin (k + 2) → ℝ) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ[X] :=
  of fun i j => (if i = 0 then C (s j / s 0) else 0) +
    (if i = Fin.last (k + 1) then 1 else 0) - (if i = j then X + 1 else 0)

private theorem pencil_eq_mul (k : ℕ) (s : Fin (k + 2) → ℝ) (hmono : Monotone s)
    (hs : 0 < s 0) :
    let N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ := of fun i j => min (s i) (s j)
    let M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ := of fun i j => max (s i) (s j)
    M.map C - (X : ℝ[X]) • N.map C = N.map C * pencilEndFactor k s := by
  -- Multiplication picks out the first and last columns of the MIN matrix.
  dsimp only
  apply Matrix.ext
  intro i j
  simp only [pencilEndFactor, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.of_apply, smul_eq_mul, Matrix.mul_apply, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_one]
  rw [min_eq_right (hmono (Fin.zero_le i)), min_eq_left (hmono (Fin.le_last i)),
    ← C_mul, mul_comm (s 0), div_mul_cancel₀ _ hs.ne']
  have hsum : C (max (s i) (s j)) + C (min (s i) (s j)) = C (s i) + C (s j) := by
    rw [← C_add, ← C_add, max_add_min]
  linear_combination hsum

private theorem det_pencilEndFactor (k : ℕ) (s : Fin (k + 2) → ℝ) (hs : 0 < s 0) :
    (pencilEndFactor k s).det = (X ^ 2 - C (s (Fin.last (k + 1)) / s 0)) * (-(X + 1)) ^ k := by
  have hzero : (0 : Fin (k + 2)) ≠ Fin.last (k + 1) := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
  have hfirst (i : Fin k) : i.castSucc.succ ≠ 0 := Fin.succ_ne_zero _
  have hlast (i : Fin k) : i.castSucc.succ ≠ Fin.last (k + 1) := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega
  let A : Matrix (Fin 2) (Fin 2) ℝ[X] := !![-X, C (s (Fin.last (k + 1)) / s 0); 1, -X]
  let B : Matrix (Fin 2) (Fin k) ℝ[X] := of fun i j =>
    pencilEndFactor k s (endpointOrder k (.inl i)) (endpointOrder k (.inr j))
  let D : Matrix (Fin k) (Fin k) ℝ[X] := diagonal fun _ => -(X + 1)
  -- After the reindexing, the interior block is scalar and the lower-left block vanishes.
  have hblocks : (pencilEndFactor k s).submatrix (endpointOrder k) (endpointOrder k) =
      fromBlocks A B 0 D := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j <;>
        simp [pencilEndFactor, A, submatrix_apply, endpointOrder, Fin.succ_last, hzero,
          Ne.symm hzero, hs.ne']
    · rfl
    · fin_cases j <;>
        simp [pencilEndFactor, submatrix_apply, endpointOrder, Fin.succ_last, hfirst, hlast]
    · by_cases hij : i = j <;>
        simp [pencilEndFactor, D, submatrix_apply, endpointOrder, hfirst, hlast, hij]
  rw [← det_submatrix_equiv_self (endpointOrder k), hblocks, det_fromBlocks_zero₂₁]
  rw [show A.det = X ^ 2 - C (s (Fin.last (k + 1)) / s 0) by
    simp [A, det_fin_two]; ring]
  simp [D]

private theorem maxMinPencil_det_succ (k : ℕ) (s : Fin (k + 2) → ℝ)
    (hmono : Monotone s) (hs : 0 < s 0) :
    let N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ := of fun i j => min (s i) (s j)
    let M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ := of fun i j => max (s i) (s j)
    let ρ := Real.sqrt (s (Fin.last (k + 1)) / s 0)
    (M.map C - (X : ℝ[X]) • N.map C).det =
      C ((-1) ^ (k + 2) * N.det) * ((X - C ρ) * (X + 1) ^ k * (X + C ρ)) := by
  intro N M ρ
  rw [pencil_eq_mul k s hmono hs, det_mul, det_pencilEndFactor k s hs]
  have hN : (N.map C).det = C N.det := (C.map_det N).symm
  rw [hN]
  have hr : ρ ^ 2 = s (Fin.last (k + 1)) / s 0 :=
    Real.sq_sqrt (div_nonneg (hs.le.trans (hmono (Fin.zero_le _))) hs.le)
  rw [← hr, C_mul, map_pow, map_pow, map_neg, map_one, neg_pow, pow_add _ k 2]
  ring

@[expose] public section

/-- **Generalized eigenvalues of a MAX matrix to a MIN matrix.** Let $n > 2$ and let
$0 < s_1 < s_2 < \dots < s_n$ be real numbers. Let $M$ be the $n \times n$ matrix with entries
$M_{ij} = \max(s_i, s_j)$, let $N$ be the $n \times n$ matrix with entries
$N_{ij} = \min(s_i, s_j)$, and put $\rho = \sqrt{s_n / s_1}$. Then, as polynomials in $X$ with
real coefficients,
$$\det(M - XN) = (-1)^n \det(N) \, (X - \rho)(X + 1)^{n-2}(X + \rho).$$

The roots of $\det(M - XN)$ are the generalized eigenvalues of $M$ to $N$.

Source: Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki, and Timo Tossavainen, *On
Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices*,
Journal of Integer Sequences 28 (2025), Article 25.7.1, Theorem 1 (`jis-2025-25.7.1-thm-1`). -/
public theorem det_maxMatrix_sub_X_smul_minMatrix (n : ℕ) (hn : 2 < n)
    (s : Fin n → ℝ) (hs : StrictMono s) (hpos : 0 < s ⟨0, by omega⟩) :
    ((Matrix.of fun i j => max (s i) (s j)).map C -
        (X : ℝ[X]) • (Matrix.of fun i j => min (s i) (s j)).map C).det =
      C ((-1) ^ n * (Matrix.of fun i j => min (s i) (s j)).det) *
        ((X - C (Real.sqrt (s ⟨n - 1, by omega⟩ / s ⟨0, by omega⟩))) *
          (X + 1) ^ (n - 2) *
          (X + C (Real.sqrt (s ⟨n - 1, by omega⟩ / s ⟨0, by omega⟩)))) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have hl : (⟨k + 2 - 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) := by
    apply Fin.ext
    simp
  rw [hl]
  simpa using maxMinPencil_det_succ k s hs.monotone hpos

end

end MetaMathlibExt
