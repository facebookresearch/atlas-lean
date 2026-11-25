/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.AlphaUpperMatrix
public import MathlibExt.Combinatorics.Enumerative.PascalStirlingGeneralization
public import MathlibExt.Combinatorics.Enumerative.PascalDiagonalExponential

/-!
# A generalization of the Pascal and Stirling matrices

Statements from A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal
and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4.

For a sequence `α = (α_j)_{j ≥ 1}` (here `α : ℕ → R` with `α 0` unused) the paper's matrices
`S_α(n)`, `𝖲_α(n)` and `𝖴_α(n)` are given by recurrences on their entries; the entry functions
below use 0-based indices, so entry `(i, j)` here is the paper's `(i + 1, j + 1)`. Statements were
checked with exact rational arithmetic before stating. The α-upper entries, their symmetric
polynomial formula, the matrix and its determinant formula are in
`MathlibExt.Combinatorics.Enumerative.AlphaUpperMatrix`.

The factorial matrix of a power series (`powerSeriesFactorialMatrix`), the lemma on its diagonal
entries (`powerSeriesFactorialMatrix_apply_self`) and the proved multiplicativity
`powerSeriesFactorialMatrix_mul` are in
`MathlibExt.Combinatorics.Enumerative.PascalStirlingGeneralization`, which this module imports.
-/

open scoped Matrix

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
equation (a-1). -/
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
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (a-1). -/
theorem alphaStirlingEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    alphaStirlingEntry α (i + 1) (j + 1) =
      alphaStirlingEntry α i j + α (j + 2) * alphaStirlingEntry α i (j + 1) := rfl

/-- **First column of the α-Stirling entries.** Let $R$ be a commutative ring, let $\alpha$ be a
sequence in $R$, and let $s_{i,j}$ ($i, j \ge 0$) be the α-Stirling entries of $\alpha$. Then
$s_{i,0} = \alpha_1$ for every $i \ge 0$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (a-1). -/
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
public theorem_wanted shiftedAlphaStirlingMatrix_eq_mul (α : ℕ → R) (n : ℕ) :
    shiftedAlphaStirlingMatrix α n = alphaStirlingMatrix α n * alphaUpperMatrix α n

/-- **Determinant of the shifted $\alpha$-Stirling matrix.** Let $R$ be a commutative ring and
let $(\alpha_j)_{j \ge 1}$ be a sequence in $R$ with $\alpha_1 = 1$. For $n \ge 0$ let
$\mathsf{S}_\alpha(n)$ be the $n \times n$ matrix whose $(i, j)$ entry $\mathsf{S}_{i,j}$, with
rows and columns indexed from $1$, is $\alpha_1$ when $i = 1$ or $j = 1$, and satisfies
$\mathsf{S}_{i,j} = \mathsf{S}_{i,j-1} + \alpha_j \mathsf{S}_{i-1,j}$ for $i, j \ge 2$. Then
$\det \mathsf{S}_\alpha(n) = \prod_{j=1}^{n} \alpha_j^{\,j-1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Theorem 2
(`jis-2026-26.5.4-thm-2`). -/
public theorem_wanted det_shiftedAlphaStirlingMatrix (α : ℕ → R) (hα : α 1 = 1) (n : ℕ) :
    (shiftedAlphaStirlingMatrix α n).det = ∏ j : Fin n, α (j + 1) ^ (j : ℕ)

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
public theorem_wanted det_hessenbergToeplitz_eq_recurrence (k : ℕ) (hk : 1 ≤ k) (c β : ℕ → R)
    (hβ : ∀ i, 1 ≤ i → i < k → β i = 0) (hβk : β k = 1)
    (hrec : ∀ m, k < m → β m = ∑ j ∈ Finset.Icc 1 k, c j * β (m - j)) (n : ℕ) :
    (Matrix.of fun a b : Fin n =>
        if (a : ℕ) ≤ b ∧ (b : ℕ) - a < k then c ((b : ℕ) - a + 1)
        else if (a : ℕ) = b + 1 then -1 else 0).det = β (n + k)

end

end MetaMathlibExt
