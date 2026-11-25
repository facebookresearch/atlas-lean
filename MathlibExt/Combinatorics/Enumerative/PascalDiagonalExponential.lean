/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# Exponential of a Pascal diagonal matrix

Theorem 3 of Moghaddamfar–Salehy–Salehy, *A Generalization of the Pascal and Stirling
Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4.
-/

open scoped Matrix

namespace MetaMathlibExt

@[expose] public section

/-- **Pascal diagonal matrices.** For $m, n \ge 0$, $\mathsf{L}_{d^{(m)}}(n)$ is the $n \times n$
real matrix that carries the $m$-th diagonal $d^{(m)}_b = \binom{m+b}{b}$ ($b \ge 0$) of Pascal's
triangle on its $m$-th subdiagonal: with rows and columns indexed from $0$, its $(b + m, b)$ entry
is $\binom{m+b}{b}$ for every $b$ with $b + m < n$, and all its other entries are $0$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
def pascalDiagonalMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => if (a : ℕ) = b + m then ((m + b).choose b : ℝ) else 0

/-- **The zeroth Pascal diagonal matrix is the identity.** For $m, n \ge 0$ let
$\mathsf{L}_{d^{(m)}}(n)$ be the $n \times n$ real matrix whose $(b + m, b)$ entry is
$\binom{m+b}{b}$ for each $b$ with $b + m < n$ and whose other entries are $0$, with rows and
columns indexed from $0$. Then $\mathsf{L}_{d^{(0)}}(n) = I_n$, the $n \times n$ identity matrix,
for every $n \ge 0$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
theorem pascalDiagonalMatrix_zero (n : ℕ) : pascalDiagonalMatrix 0 n = 1 := by
  ext a b
  simp [pascalDiagonalMatrix, Matrix.one_apply, Fin.val_inj]

/-- **First-column sequence for exponentials of Pascal diagonal matrices.** For $k \ge 0$, the
sequence of natural numbers $\alpha^{(k)} = (\alpha^{(k)}_i)_{i \ge 0}$ is defined by
$\alpha^{(k)}_0 = 0$, $\alpha^{(k)}_1 = 1$ and, for $i \ge 2$,
$\alpha^{(k)}_i = \binom{i-2}{k-1} \alpha^{(k)}_{i-k}$ if $1 \le k < i$ and $\alpha^{(k)}_i = 0$
otherwise. Thus $\alpha^{(k)}_i = 0$ for $2 \le i \le k$, and $\alpha^{(0)}_i = 0$ for all
$i \ne 1$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
def pascalExpFirstColumn (k i : ℕ) : ℕ :=
  if i = 1 then 1
  else if _h : 0 < k ∧ k < i then (i - 2).choose (k - 1) * pascalExpFirstColumn k (i - k)
  else 0
termination_by i
decreasing_by omega

/-- **First term of the Pascal first-column sequence.** For every $k \ge 0$, the first-column
sequence $\alpha^{(k)}$ satisfies $\alpha^{(k)}_1 = 1$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
theorem pascalExpFirstColumn_one (k : ℕ) : pascalExpFirstColumn k 1 = 1 := by
  rw [pascalExpFirstColumn]
  simp

/-- **Vanishing terms of the Pascal first-column sequence.** For all natural numbers $k$ and $i$
with $2 \le i \le k$, the first-column sequence $\alpha^{(k)}$ satisfies $\alpha^{(k)}_i = 0$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
theorem pascalExpFirstColumn_of_le {k i : ℕ} (h2 : 2 ≤ i) (hik : i ≤ k) :
    pascalExpFirstColumn k i = 0 := by
  rw [pascalExpFirstColumn]
  split_ifs <;> omega

/-- **Recurrence for the Pascal first-column sequence.** For all natural numbers $k$ and $i$ with
$1 \le k < i$, the first-column sequence $\alpha^{(k)}$ satisfies
$\alpha^{(k)}_i = \binom{i-2}{k-1} \alpha^{(k)}_{i-k}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3. -/
theorem pascalExpFirstColumn_of_lt {k i : ℕ} (hk : 1 ≤ k) (hki : k < i) :
    pascalExpFirstColumn k i = (i - 2).choose (k - 1) * pascalExpFirstColumn k (i - k) := by
  rw [pascalExpFirstColumn]
  split_ifs <;> first | rfl | omega

private theorem pascalDiagonalMatrix_mul (m l n : ℕ) :
    pascalDiagonalMatrix m n * pascalDiagonalMatrix l n =
      ((m + l).choose l : ℝ) • pascalDiagonalMatrix (m + l) n := by
  ext a b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hab : (a : ℕ) = b + (m + l)
  · -- The only possible intermediate index is on the `l`-th subdiagonal of the right factor.
    let c : Fin n := ⟨b + l, by have := a.isLt; omega⟩
    have hcb : (c : ℕ) = b + l := rfl
    have hac : (a : ℕ) = c + m := by omega
    rw [Finset.sum_eq_single c]
    · simp only [pascalDiagonalMatrix, Matrix.of_apply, ite_eq_left hac, ite_eq_left hcb,
        ite_eq_left hab]
      rw [hcb, Nat.add_comm (b : ℕ) l, ← Nat.add_assoc]
      have h := Nat.choose_mul (n := m + (l + (b : ℕ))) (k := l + (b : ℕ))
        (s := (b : ℕ)) (by omega)
      rw [← Nat.add_assoc, show m + l + (b : ℕ) - b = m + l by omega,
        show l + (b : ℕ) - b = l by omega, Nat.mul_comm ((m + l + (b : ℕ)).choose b)] at h
      exact_mod_cast h
    · intro d _ hdc
      have hdb : (d : ℕ) ≠ b + l := fun hd => hdc (Fin.ext (hd.trans hcb.symm))
      simp [pascalDiagonalMatrix, hdb]
    · simp
  · rw [show pascalDiagonalMatrix (m + l) n a b = 0 by simp [pascalDiagonalMatrix, hab], mul_zero]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hcb : (c : ℕ) = b + l
    · have hac : (a : ℕ) ≠ c + m := by omega
      simp [pascalDiagonalMatrix, hac]
    · simp [pascalDiagonalMatrix, hcb]

private theorem pascalDiagonalMatrix_pow (k : ℕ) (hk : 1 ≤ k) (n i : ℕ) :
    pascalDiagonalMatrix k n ^ i =
      ((i.factorial : ℝ) * (pascalExpFirstColumn k (k * i + 1) : ℝ)) •
        pascalDiagonalMatrix (k * i) n := by
  induction i with
  | zero => simp [pascalExpFirstColumn_one, pascalDiagonalMatrix_zero]
  | succ i ih =>
    have hki : k < k * (i + 1) + 1 := by rw [Nat.mul_succ]; omega
    have hα := pascalExpFirstColumn_of_lt hk hki
    rw [Nat.mul_succ, show k * i + k + 1 - k = k * i + 1 by omega,
      show k * i + k + 1 - 2 = k * i + k - 1 by omega] at hα
    -- The factor `i + 1` in the binomial coefficient accounts for the factorial in the series.
    have hchoose : (k * i + k).choose k = (i + 1) * (k * i + k - 1).choose (k - 1) := by
      simpa only [Nat.succ_mul, Nat.mul_comm i k] using
        (Nat.choose_mul_right (m := i + 1) (n := k) (by omega))
    rw [pow_succ, ih, smul_mul_assoc, pascalDiagonalMatrix_mul, smul_smul, Nat.mul_succ,
      Nat.factorial_succ, hα, hchoose]
    push_cast
    congr 1
    ring

/-- **Exponential of a Pascal diagonal matrix.** Let $k \ge 1$ and $n \ge 0$. For $m \ge 0$ let
$\mathsf{L}_{d^{(m)}}(n)$ be the $n \times n$ real matrix whose $(b + m, b)$ entry is
$\binom{m+b}{b}$ for each $b$ with $b + m < n$ and whose other entries are $0$ (indices from
$0$). Let $\alpha^{(k)} = (\alpha^{(k)}_i)_{i \ge 1}$ be given by $\alpha^{(k)}_1 = 1$,
$\alpha^{(k)}_i = 0$ for $2 \le i \le k$ and
$\alpha^{(k)}_i = \binom{i-2}{k-1} \alpha^{(k)}_{i-k}$ for $i > k$, and let
$T_{\alpha^{(k)}, \beta}(n)$ be the $n \times n$ lower triangular Toeplitz matrix with first
column $\alpha^{(k)}$ and first row $\beta = (1, 0, 0, \ldots)$, that is, with $(a, b)$ entry
$\alpha^{(k)}_{a-b+1}$ for $b \le a$ and $0$ for $b > a$. Then $\exp(\mathsf{L}_{d^{(k)}}(n))$
equals the Hadamard (entrywise) product
$T_{\alpha^{(k)}, \beta}(n) \odot \sum_{i=0}^{n-1} \mathsf{L}_{d^{(ki)}}(n)$.

The paper sums over all $i \ge 0$; the terms with $i \ge n$ are zero matrices, since then
$ki \ge n$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 3
(`jis-2026-26.5.4-thm-3`). -/
theorem exp_pascalDiagonalMatrix (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    NormedSpace.exp (pascalDiagonalMatrix k n) =
      (Matrix.of fun a b : Fin n =>
          if (b : ℕ) ≤ a then (pascalExpFirstColumn k ((a : ℕ) - b + 1) : ℝ) else 0) ⊙
        ∑ i ∈ Finset.range n, pascalDiagonalMatrix (k * i) n := by
  have hzero (i : ℕ) (hi : i ∉ Finset.range n) :
      pascalDiagonalMatrix k n ^ i = 0 := by
    have hin : n ≤ i := Nat.le_of_not_lt fun h => hi (Finset.mem_range.mpr h)
    have hik : i ≤ k * i := by simpa only [one_mul] using Nat.mul_le_mul_right i hk
    rw [pascalDiagonalMatrix_pow k hk]
    have hD : pascalDiagonalMatrix (k * i) n = 0 := by
      ext a b
      have ha := a.isLt
      simp [pascalDiagonalMatrix, show (a : ℕ) ≠ b + k * i by omega]
    rw [hD, smul_zero]
  simp only [NormedSpace.exp_eq_tsum ℝ]
  rw [tsum_eq_sum (s := Finset.range n)]
  · ext a b
    rw [Matrix.hadamard_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hf : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    rw [pascalDiagonalMatrix_pow k hk, smul_smul, inv_mul_cancel_left₀ hf,
      Matrix.smul_apply, smul_eq_mul]
    by_cases hab : (a : ℕ) = b + k * i
    · rw [ite_eq_left (show (b : ℕ) ≤ a by omega), show (a : ℕ) - b + 1 = k * i + 1 by omega]
    · have hD : pascalDiagonalMatrix (k * i) n a b = 0 := by simp [pascalDiagonalMatrix, hab]
      rw [hD, mul_zero, mul_zero]
  · intro i hi
    rw [hzero i hi, smul_zero]

end

end MetaMathlibExt
