/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Banded Hessenberg–Toeplitz determinants

The determinant of the banded Hessenberg–Toeplitz matrix with subdiagonal entries
`-1` gives the normalized solution of the linear recurrence with the same coefficients.
-/

namespace MetaMathlibExt

variable {R : Type*} [CommRing R]

namespace det_hessenbergToeplitz_eq_recurrence

private def entry (k : ℕ) (c : ℕ → R) (a b : ℕ) : R :=
  if a ≤ b ∧ b - a < k then c (b - a + 1) else if a = b + 1 then -1 else 0

/-- In column `j`, the weighted entries on and above the diagonal sum to the next term. -/
private theorem band_sum {k n j : ℕ} (hj : j < n) (c β : ℕ → R)
    (hβ : ∀ i, 1 ≤ i → i < k → β i = 0)
    (hrec : ∀ m, k < m → β m = ∑ l ∈ Finset.Icc 1 k, c l * β (m - l)) :
    (∑ i ∈ Finset.range n, if i ≤ j ∧ j - i < k then c (j - i + 1) * β (i + k) else 0) =
      β (j + 1 + k) := by
  rw [hrec _ (by omega), ← Finset.sum_filter]
  calc
    _ = ∑ l ∈ Finset.Icc 1 (min k (j + 1)), c l * β (j + 1 + k - l) := by
      refine Finset.sum_bij (fun i _ => j - i + 1) ?_ ?_ ?_ ?_
      · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, le_min_iff]
        omega
      · simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro l hl
        obtain ⟨hl₁, hlk, hlj⟩ := (Finset.mem_Icc.mp hl).imp_right le_min_iff.mp
        refine ⟨j + 1 - l, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, ?_⟩ <;> omega
      · intro i hi
        obtain ⟨_, hij, _⟩ := Finset.mem_filter.mp hi
        rw [show j + 1 + k - (j - i + 1) = i + k by omega]
    _ = _ := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right (min_le_left _ _))
      intro l hl hl'
      simp only [Finset.mem_Icc, le_min_iff] at hl hl'
      rw [hβ _ (by omega) (by omega), mul_zero]

end det_hessenbergToeplitz_eq_recurrence

open det_hessenbergToeplitz_eq_recurrence

set_option linter.unusedVariables false in
/-- **Banded Hessenberg–Toeplitz determinants and linear recurrences.** Let $R$ be a commutative
ring, let $k \ge 1$, and let $(c_j)_{j \ge 1}$ and $(\beta_m)_{m \ge 1}$ be sequences in $R$ such
that $\beta_1 = \cdots = \beta_{k-1} = 0$, $\beta_k = 1$ and
$\beta_m = \sum_{j=1}^{k} c_j \beta_{m-j}$ for every $m > k$. For $n \ge 0$ let $H_n$ be the
$n \times n$ upper Hessenberg Toeplitz matrix whose $(i, j)$ entry is $c_{j-i+1}$ if
$0 \le j - i \le k - 1$, is $-1$ if $i = j + 1$, and is $0$ otherwise. Then
$\det H_n = \beta_{n+k}$.

Unlike the paper, this is stated over any commutative ring, without the assumption $c_k \ne 0$,
and also for $n = 0$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 7
(`jis-2026-26.5.4-thm-7`). -/
public theorem det_hessenbergToeplitz_eq_recurrence (k : ℕ) (hk : 1 ≤ k) (c β : ℕ → R)
    (hβ : ∀ i, 1 ≤ i → i < k → β i = 0) (hβk : β k = 1)
    (hrec : ∀ m, k < m → β m = ∑ j ∈ Finset.Icc 1 k, c j * β (m - j)) (n : ℕ) :
    (Matrix.of fun a b : Fin n =>
        if (a : ℕ) ≤ b ∧ (b : ℕ) - a < k then c ((b : ℕ) - a + 1)
        else if (a : ℕ) = b + 1 then -1 else 0).det = β (n + k) := by
  cases n with
  | zero => simpa using hβk.symm
  | succ n =>
    let M := Matrix.of fun a b : Fin (n + 1) => entry k c a b
    let w (a : Fin (n + 1)) := β (a + k)
    change M.det = β (n + 1 + k)
    have hrow (j : Fin (n + 1)) : (∑ a, w a • M a) j =
        if j = Fin.last n then β (n + 1 + k) else 0 := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, Matrix.of_apply, w]
      rw [Fin.sum_univ_eq_sum_range (fun i => β (i + k) * entry k c i j)]
      calc
        _ = ∑ i ∈ Finset.range (n + 1),
              ((if i ≤ j ∧ (j : ℕ) - i < k then c (j - i + 1) * β (i + k) else 0) -
                (if i = (j : ℕ) + 1 then β (i + k) else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          unfold entry
          split_ifs <;> first | omega | simp_all [mul_comm]
        _ = _ := by
          rw [Finset.sum_sub_distrib, band_sum j.isLt c β hβ hrec, Finset.sum_ite_eq']
          by_cases h : j = Fin.last n
          · subst j
            simp
          · have hlt : (j : ℕ) + 1 < n + 1 := Nat.succ_lt_succ (Fin.lt_last_iff_ne_last.mpr h)
            simp [h, hlt]
    have hminor : (M.submatrix Fin.succ Fin.castSucc).det = (-1 : R) ^ n := by
      rw [Matrix.det_of_isUpperTriangular]
      · simp [M, entry, Matrix.submatrix_apply]
      · intro i j hji
        have hlt : (j : ℕ) < i := hji
        simp [M, entry, Matrix.submatrix_apply, hlt.ne', (show ¬i < j from hji.asymm)]
    -- The first row has weight one, so replacing it by the weighted sum preserves the determinant.
    have hdet := Matrix.det_updateRow_sum M 0 w
    rw [show w 0 = 1 by simpa [w] using hβk, one_smul] at hdet
    rw [← hdet, Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last n)]
    · simp only [Matrix.updateRow_self, hrow, ite_true, Fin.val_last, Fin.succAbove_last]
      rw [← Fin.succAbove_zero, Matrix.submatrix_updateRow_succAbove, Fin.succAbove_zero,
        hminor, mul_right_comm, ← mul_pow]
      simp
    · intro j _ hj
      simp [hrow, hj]
    · simp

end MetaMathlibExt
