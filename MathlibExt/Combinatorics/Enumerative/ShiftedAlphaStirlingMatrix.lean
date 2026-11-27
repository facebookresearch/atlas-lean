/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AlphaUpperMatrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The shifted α-Stirling matrix

The product of the α-Stirling and α-upper matrices has the same first row, first column,
and entry recurrence as the shifted α-Stirling matrix. The α-Stirling factor is lower
triangular with constant diagonal `α 1`, so when `α 1 = 1` the shifted matrix has the
determinant of the α-upper factor.
-/

namespace MetaMathlibExt

@[expose] public section

variable {R : Type*} [CommRing R]

/-- **Entries of the α-Stirling matrix.** Let $R$ be a commutative ring and let
$\alpha_0, \alpha_1, \alpha_2, \dots$ be a sequence in $R$ ($\alpha_0$ is never used). The
α-Stirling entries $s_{i,j} \in R$, for $i, j \ge 0$, are defined recursively by
$s_{i,0} = \alpha_1$ for all $i$, $s_{0,j} = 0$ for $j \ge 1$, and
$s_{i+1,j+1} = s_{i,j} + \alpha_{j+2} s_{i,j+1}$ for all $i, j \ge 0$.

These are the entries of the paper's matrix $S_\alpha(n)$ with indices shifted to start at $0$.
Writing $\hat S_{i,j}$ for the entries of $S_\alpha(n)$ in the paper's $1$-based indexing, the
first column is $\alpha_1$, the rest of the first row is $0$, and
$\hat S_{i,j} = \hat S_{i-1,j-1} + \alpha_j \hat S_{i-1,j}$ for $i, j \ge 2$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4,
equation (2). -/
def alphaStirlingEntry (α : ℕ → R) : ℕ → ℕ → R
  | _, 0 => α 1
  | 0, _ + 1 => 0
  | i + 1, j + 1 => alphaStirlingEntry α i j + α (j + 2) * alphaStirlingEntry α i (j + 1)

/-- **Entries of the shifted α-Stirling matrix.** Let $R$ be a commutative ring and let
$\alpha = (\alpha_j)_{j \ge 1}$ be a sequence in $R$. The entries $\mathsf{S}_{i,j} \in R$ of the
shifted $\alpha$-Stirling matrix of $\alpha$, for natural numbers $i$ and $j$ counted from $0$, are
defined by $\mathsf{S}_{i,0} = \alpha_1$ for all $i$, $\mathsf{S}_{0,j} = \alpha_1$ for all $j$,
and
$$\mathsf{S}_{i+1,j+1} = \mathsf{S}_{i+1,j} + \alpha_{j+2} \mathsf{S}_{i,j+1}.$$

The paper indexes from $1$: its entry $(i, j)$ is $P_{i,j} = \mathsf{S}_{i-1,j-1}$ for
$i, j \ge 1$. In this indexing the first row and the first column equal $\alpha_1$, and
$P_{i,j} = P_{i,j-1} + \alpha_j P_{i-1,j}$ for $i, j \ge 2$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
def shiftedAlphaStirlingEntry (α : ℕ → R) : ℕ → ℕ → R
  | _, 0 => α 1
  | 0, _ + 1 => α 1
  | i + 1, j + 1 =>
      shiftedAlphaStirlingEntry α (i + 1) j + α (j + 2) * shiftedAlphaStirlingEntry α i (j + 1)

/-- **Recurrence for the α-Stirling entries.** Let $R$ be a commutative ring, let $\alpha$ be a
sequence in $R$, and let $s_{i,j}$ ($i, j \ge 0$) be the α-Stirling entries of $\alpha$. Then for
all $i, j \ge 0$, $s_{i+1,j+1} = s_{i,j} + \alpha_{j+2} s_{i,j+1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (2). -/
theorem alphaStirlingEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    alphaStirlingEntry α (i + 1) (j + 1) =
      alphaStirlingEntry α i j + α (j + 2) * alphaStirlingEntry α i (j + 1) := rfl

/-- **First column of the α-Stirling entries.** Let $R$ be a commutative ring, let $\alpha$ be a
sequence in $R$, and let $s_{i,j}$ ($i, j \ge 0$) be the α-Stirling entries of $\alpha$. Then
$s_{i,0} = \alpha_1$ for every $i \ge 0$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (2). -/
theorem alphaStirlingEntry_zero_right (α : ℕ → R) (i : ℕ) : alphaStirlingEntry α i 0 = α 1 := by
  cases i <;> rfl

/-- **Recurrence for the shifted α-Stirling entries.** Let $R$ be a commutative ring, let
$\alpha = (\alpha_j)_{j \ge 1}$ be a sequence in $R$, and write $\mathsf{S}_{i,j}$ for the entries
of the shifted $\alpha$-Stirling matrix of $\alpha$, indexed from $0$. For all natural numbers $i$
and $j$,
$$\mathsf{S}_{i+1,j+1} = \mathsf{S}_{i+1,j} + \alpha_{j+2} \mathsf{S}_{i,j+1}.$$

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
theorem shiftedAlphaStirlingEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    shiftedAlphaStirlingEntry α (i + 1) (j + 1) =
      shiftedAlphaStirlingEntry α (i + 1) j +
        α (j + 2) * shiftedAlphaStirlingEntry α i (j + 1) := by
  rw [shiftedAlphaStirlingEntry]

/-- **First row of the shifted α-Stirling matrix.** Let $R$ be a commutative ring, let
$\alpha = (\alpha_j)_{j \ge 1}$ be a sequence in $R$, and write $\mathsf{S}_{i,j}$ for the entries
of the shifted $\alpha$-Stirling matrix of $\alpha$, indexed from $0$. For every natural number
$j$, $\mathsf{S}_{0,j} = \alpha_1$; that is, the first row is constant, equal to $\alpha_1$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
theorem shiftedAlphaStirlingEntry_zero_left (α : ℕ → R) (j : ℕ) :
    shiftedAlphaStirlingEntry α 0 j = α 1 := by
  cases j <;> rw [shiftedAlphaStirlingEntry]

/-- **The α-Stirling matrix.** Let $R$ be a commutative ring, let $\alpha$ be a sequence in $R$,
and let $s_{i,j}$ ($i, j \ge 0$) be the α-Stirling entries of $\alpha$. For $n \ge 0$, the matrix
$S_\alpha(n)$ is the $n \times n$ matrix over $R$, with rows and columns indexed by
$0, 1, \dots, n - 1$, whose $(i, j)$ entry is $s_{i,j}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
def alphaStirlingMatrix (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => alphaStirlingEntry α a b

/-- **Shifted α-Stirling matrix.** Let $R$ be a commutative ring, let
$\alpha = (\alpha_j)_{j \ge 1}$ be a sequence in $R$, and let $n$ be a natural number. The shifted
$\alpha$-Stirling matrix $\mathsf{S}_\alpha(n)$ is the $n \times n$ matrix over $R$ whose entry in
row $i$ and column $j$ (counted from $0$) is the shifted $\alpha$-Stirling entry
$\mathsf{S}_{i,j}$, given by $\mathsf{S}_{i,0} = \mathsf{S}_{0,j} = \alpha_1$ and
$\mathsf{S}_{i+1,j+1} = \mathsf{S}_{i+1,j} + \alpha_{j+2} \mathsf{S}_{i,j+1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 1.4. -/
def shiftedAlphaStirlingMatrix (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => shiftedAlphaStirlingEntry α a b

private lemma alphaStirlingEntry_eq_zero (α : ℕ → R) {i j : ℕ} (h : i < j) :
    alphaStirlingEntry α i j = 0 := by
  induction i generalizing j with
  | zero => cases j <;> simp_all only [Nat.lt_irrefl, alphaStirlingEntry]
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j => rw [alphaStirlingEntry_succ_succ, ih (by omega), ih (by omega), mul_zero, add_zero]

private lemma alphaStirlingEntry_diag (α : ℕ → R) (i : ℕ) : alphaStirlingEntry α i i = α 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [alphaStirlingEntry_succ_succ, ih, alphaStirlingEntry_eq_zero α (Nat.lt_succ_self i),
      mul_zero, add_zero]

private def alphaProductEntry (α : ℕ → R) (i j : ℕ) : R :=
  ∑ k ∈ Finset.range (i + 1), alphaStirlingEntry α i k * alphaUpperEntry α k j

-- Split the recurrence for the next row into its two contributions, shifting the sum
-- with the second term back by one. The correction from the zeroth entry is independent of j.
private lemma alphaProductEntry_succ (α : ℕ → R) (i j : ℕ) :
    alphaProductEntry α (i + 1) j = α 1 - α 1 * α 1 +
      ∑ k ∈ Finset.range (i + 1), alphaStirlingEntry α i k *
        (alphaUpperEntry α (k + 1) j + α (k + 1) * alphaUpperEntry α k j) := by
  let g (k : ℕ) := alphaStirlingEntry α i k * α (k + 1) * alphaUpperEntry α k j
  have hg : (∑ k ∈ Finset.range (i + 1), g (k + 1)) + α 1 * α 1 =
      ∑ k ∈ Finset.range (i + 1), g k := by
    calc
      _ = ∑ k ∈ Finset.range (i + 2), g k := by
        rw [Finset.sum_range_succ' g (i + 1)]
        simp only [g, alphaStirlingEntry_zero_right, zero_add, alphaUpperEntry.eq_1, mul_one]
      _ = _ := by
        rw [Finset.sum_range_succ g (i + 1)]
        simp [g, alphaStirlingEntry_eq_zero α (Nat.lt_succ_self i)]
  unfold alphaProductEntry
  rw [Finset.sum_range_succ']
  simp only [alphaStirlingEntry_zero_right, alphaUpperEntry.eq_1, mul_one,
    alphaStirlingEntry_succ_succ, add_mul, mul_add, Finset.sum_add_distrib]
  have he : (∑ k ∈ Finset.range (i + 1),
      α (k + 2) * alphaStirlingEntry α i (k + 1) * alphaUpperEntry α (k + 1) j) =
      ∑ k ∈ Finset.range (i + 1), g (k + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp [g]
    rw [mul_comm (α (k + 2))]
  have he' : (∑ k ∈ Finset.range (i + 1),
      alphaStirlingEntry α i k * (α (k + 1) * alphaUpperEntry α k j)) =
      ∑ k ∈ Finset.range (i + 1), g k := by
    apply Finset.sum_congr rfl
    intro k _
    exact (mul_assoc _ _ _).symm
  rw [he, he']
  linear_combination hg

private lemma alphaProductEntry_recurrence (α : ℕ → R) (i j : ℕ) :
    alphaProductEntry α (i + 1) (j + 1) =
      alphaProductEntry α (i + 1) j + α (j + 2) * alphaProductEntry α i (j + 1) := by
  rw [alphaProductEntry_succ α i (j + 1), alphaProductEntry_succ α i j]
  unfold alphaProductEntry
  rw [Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [alphaUpperEntry_succ_succ]
  ring

private lemma shiftedAlphaStirlingEntry_eq_product (α : ℕ → R) (i j : ℕ) :
    shiftedAlphaStirlingEntry α i j = alphaProductEntry α i j := by
  induction i generalizing j with
  | zero =>
    rw [shiftedAlphaStirlingEntry_zero_left]
    simp [alphaProductEntry, alphaStirlingEntry_zero_right, alphaUpperEntry.eq_1]
  | succ i ih =>
    induction j with
    | zero =>
      unfold alphaProductEntry
      rw [shiftedAlphaStirlingEntry, Finset.sum_range_succ']
      simp [alphaUpperEntry.eq_1, alphaUpperEntry.eq_2, alphaStirlingEntry_zero_right]
    | succ j ihj => rw [shiftedAlphaStirlingEntry_succ_succ, ihj, ih, alphaProductEntry_recurrence]

/-- **LU decomposition of the shifted α-Stirling matrix.** Let $R$ be a commutative ring, let
$\alpha = (\alpha_j)_{j \ge 1}$ be a sequence in $R$, and let $n$ be a natural number. Then
$$\mathsf{S}_\alpha(n) = S_\alpha(n) \mathsf{U}_\alpha(n),$$
where $\mathsf{S}_\alpha(n)$ is the $n \times n$ shifted $\alpha$-Stirling matrix, $S_\alpha(n)$
is the $n \times n$ $\alpha$-Stirling matrix and $\mathsf{U}_\alpha(n)$ is the $n \times n$ upper
matrix of $\alpha$.

The paper assumes $\alpha_1 = 1$. The identity holds for every sequence $\alpha$ because both
sides scale by $\alpha_1$ and $\mathsf{U}_\alpha(n)$ does not depend on $\alpha_1$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 2
(`jis-2026-26.5.4-thm-2`). -/
public theorem shiftedAlphaStirlingMatrix_eq_mul (α : ℕ → R) (n : ℕ) :
    shiftedAlphaStirlingMatrix α n = alphaStirlingMatrix α n * alphaUpperMatrix α n := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [shiftedAlphaStirlingMatrix, alphaStirlingMatrix, alphaUpperMatrix, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => alphaStirlingEntry α i k * alphaUpperEntry α k j) n,
    shiftedAlphaStirlingEntry_eq_product]
  have hi : (i : ℕ) + 1 ≤ n := i.isLt
  exact Finset.sum_subset (Finset.range_mono hi) fun k _ hk => by
    simp only [Finset.mem_range, not_lt] at hk
    rw [alphaStirlingEntry_eq_zero α (by omega), zero_mul]

/-- **Determinant of the shifted $\alpha$-Stirling matrix.** Let $R$ be a commutative ring and
let $(\alpha_j)_{j \ge 1}$ be a sequence in $R$ with $\alpha_1 = 1$. For $n \ge 0$ let
$\mathsf{S}_\alpha(n)$ be the $n \times n$ matrix whose $(i, j)$ entry $\mathsf{S}_{i,j}$, with
rows and columns indexed from $1$, is $\alpha_1$ when $i = 1$ or $j = 1$, and satisfies
$\mathsf{S}_{i,j} = \mathsf{S}_{i,j-1} + \alpha_j \mathsf{S}_{i-1,j}$ for $i, j \ge 2$. Then
$\det \mathsf{S}_\alpha(n) = \prod_{j=1}^{n} \alpha_j^{\,j-1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 2
(`jis-2026-26.5.4-thm-2`). -/
public theorem det_shiftedAlphaStirlingMatrix (α : ℕ → R) (hα : α 1 = 1) (n : ℕ) :
    (shiftedAlphaStirlingMatrix α n).det = ∏ j : Fin n, α (j + 1) ^ (j : ℕ) := by
  have htri : (alphaStirlingMatrix α n).IsLowerTriangular :=
    fun {_ _} hij => alphaStirlingEntry_eq_zero α hij
  rw [shiftedAlphaStirlingMatrix_eq_mul, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ htri, det_alphaUpperMatrix]
  simp [alphaStirlingMatrix, alphaStirlingEntry_diag, hα]

end

end MetaMathlibExt
