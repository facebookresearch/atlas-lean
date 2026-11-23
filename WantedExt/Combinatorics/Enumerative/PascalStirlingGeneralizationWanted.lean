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

/-!
# A generalization of the Pascal and Stirling matrices

Statements from A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal
and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4.

For a sequence `α = (α_j)_{j ≥ 1}` (here `α : ℕ → R` with `α 0` unused) the paper's matrices
`S_α(n)`, `𝖲_α(n)` and `𝖴_α(n)` are given by recurrences on their entries; the entry functions
below use 0-based indices, so entry `(i, j)` here is the paper's `(i + 1, j + 1)`. Statements were
checked with exact rational arithmetic before stating.
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

/-- **Entries of the α-upper matrix.** Let $R$ be a commutative ring and let
$\alpha_0, \alpha_1, \alpha_2, \dots$ be a sequence in $R$ ($\alpha_0$ is never used). The
α-upper entries $u_{i,j} \in R$, for $i, j \ge 0$, are defined recursively by $u_{0,j} = 1$ for
all $j$, $u_{i,0} = 0$ for $i \ge 1$, and
$u_{i+1,j+1} = u_{i+1,j} + \alpha_{i+1} u_{i,j} + (\alpha_{j+2} - \alpha_{i+1}) u_{i,j+1}$ for
all $i, j \ge 0$.

These are the entries of the paper's matrix $\mathsf{U}_\alpha(n)$ with indices shifted to start
at $0$; in the paper's $1$-based indexing the first row is $1$, the rest of the first column is
$0$, and $\mathsf{U}_{i,j} = \mathsf{U}_{i,j-1} + \alpha_{i-1} \mathsf{U}_{i-1,j-1} +
(\alpha_j - \alpha_{i-1}) \mathsf{U}_{i-1,j}$ for $i, j \ge 2$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2,
equation (u-1-2). -/
def alphaUpperEntry (α : ℕ → R) : ℕ → ℕ → R
  | 0, _ => 1
  | _ + 1, 0 => 0
  | i + 1, j + 1 =>
      alphaUpperEntry α (i + 1) j + α (i + 1) * alphaUpperEntry α i j +
        (α (j + 2) - α (i + 1)) * alphaUpperEntry α i (j + 1)

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
      shiftedAlphaStirlingEntry α (i + 1) j + α (j + 2) * shiftedAlphaStirlingEntry α i (j + 1) := by
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

/-- **Recurrence for the α-upper entries.** Let $R$ be a commutative ring, let $\alpha$ be a
sequence in $R$, and let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries of $\alpha$. Then for all
$i, j \ge 0$,
$u_{i+1,j+1} = u_{i+1,j} + \alpha_{i+1} u_{i,j} + (\alpha_{j+2} - \alpha_{i+1}) u_{i,j+1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, equation (u-1-2). -/
theorem alphaUpperEntry_succ_succ (α : ℕ → R) (i j : ℕ) :
    alphaUpperEntry α (i + 1) (j + 1) =
      alphaUpperEntry α (i + 1) j + α (i + 1) * alphaUpperEntry α i j +
        (α (j + 2) - α (i + 1)) * alphaUpperEntry α i (j + 1) := by
  rw [alphaUpperEntry]

/-- **Small α-upper entries.** Let $R$ be a commutative ring, let $\alpha$ be a sequence in $R$,
and let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries of $\alpha$. Then $u_{1,1} = \alpha_2$ and
$u_{1,2} = \alpha_2 + \alpha_3$.

Writing $\mathsf{U}_{i,j}$ for the entries of the paper's matrix $\mathsf{U}_\alpha(n)$ in its
$1$-based indexing, these are $\mathsf{U}_{2,2} = \alpha_2$ and
$\mathsf{U}_{2,3} = \alpha_2 + \alpha_3$, as in the paper's display of $\mathsf{U}_\alpha(4)$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2. -/
theorem alphaUpperEntry_one_one_one_two (α : ℕ → R) :
    alphaUpperEntry α 1 1 = α 2 ∧ alphaUpperEntry α 1 2 = α 2 + α 3 := by
  constructor
  · simp only [alphaUpperEntry]; ring
  · simp only [alphaUpperEntry]; ring

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

/-- **The α-upper matrix.** Let $R$ be a commutative ring, let $\alpha$ be a sequence in $R$, and
let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries of $\alpha$. For $n \ge 0$, the matrix
$\mathsf{U}_\alpha(n)$ is the $n \times n$ matrix over $R$, with rows and columns indexed by
$0, 1, \dots, n - 1$, whose $(i, j)$ entry is $u_{i,j}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 2. -/
def alphaUpperMatrix (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => alphaUpperEntry α a b

/-- **α-upper entries are complete homogeneous symmetric polynomials.** Let $R$ be a commutative
ring, let $\alpha$ be a sequence in $R$, and let $u_{i,j}$ ($i, j \ge 0$) be the α-upper entries
of $\alpha$. For all $i \le j$, $u_{i,j} = h_i(\alpha_{i+1}, \alpha_{i+2}, \dots, \alpha_{j+1})$,
where $h_i$ is the complete homogeneous symmetric polynomial of degree $i$ in $j - i + 1$
variables.

Writing $\mathsf{U}_{i,j}$ for the entries of the paper's matrix $\mathsf{U}_\alpha(n)$ in its
$1$-based indexing, this reads $\mathsf{U}_{i,j} = h_{i-1}(\alpha_i, \dots, \alpha_j)$ for
$j \ge i \ge 1$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 1
(`jis-2026-26.5.4-lem-1`). -/
public theorem_wanted alphaUpperEntry_eq_hsymm (α : ℕ → R) {i j : ℕ} (hij : i ≤ j) :
    alphaUpperEntry α i j =
      MvPolynomial.eval (fun t : Fin (j - i + 1) => α (i + 1 + t))
        (MvPolynomial.hsymm (Fin (j - i + 1)) R i)

/-- **Determinant of the α-upper matrix.** Let $R$ be a commutative ring and let $\alpha$ be a
sequence in $R$. For every $n \ge 0$, the determinant of the $n \times n$ α-upper matrix
$\mathsf{U}_\alpha(n)$ is $\det \mathsf{U}_\alpha(n) = \prod_{i=1}^{n} \alpha_i^{i-1}$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 1
(`jis-2026-26.5.4-lem-1`). -/
public theorem_wanted det_alphaUpperMatrix (α : ℕ → R) (n : ℕ) :
    (alphaUpperMatrix α n).det = ∏ i : Fin n, α (i + 1) ^ (i : ℕ)

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
public theorem_wanted exp_pascalDiagonalMatrix (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    NormedSpace.exp (pascalDiagonalMatrix k n) =
      (Matrix.of fun a b : Fin n =>
          if (b : ℕ) ≤ a then (pascalExpFirstColumn k ((a : ℕ) - b + 1) : ℝ) else 0) ⊙
        ∑ i ∈ Finset.range n, pascalDiagonalMatrix (k * i) n

/-- **Factorial matrix of a power series.** Let $K$ be a field, let $f$ be a formal power series
over $K$ in the variable $t$, and let $n$ be a natural number. The factorial matrix $M_n(f)$ is
the $n \times n$ matrix over $K$ whose entry in row $a$ and column $b$ (counted from $0$) is
$(a! \cdot 1_K) / (b! \cdot 1_K)$ times the coefficient of $t^{a-b}$ in $f$ when $b \le a$, and
$0$ when $b > a$. Here the quotient is taken in $K$ and is read as $0$ when $b! \cdot 1_K = 0$,
which can happen only in positive characteristic. When $K$ has characteristic zero, the factor is
the integer $a!/b!$ and $M_n(f)$ is the leading $n \times n$ section of the infinite lower
triangular matrix $M(f)$ of Moghaddamfar, Salehy and Salehy.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
noncomputable def powerSeriesFactorialMatrix {K : Type*} [Field K] (f : PowerSeries K) (n : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b =>
    if (b : ℕ) ≤ a then
      ((a : ℕ).factorial : K) / ((b : ℕ).factorial : K) * PowerSeries.coeff ((a : ℕ) - b) f
    else 0

/-- **Diagonal of the factorial matrix of a power series.** Let $K$ be a field of characteristic
zero, let $f$ be a formal power series over $K$ and let $n \ge 0$. Every diagonal entry of the
leading $n \times n$ section of $M(f)$, the lower triangular matrix whose $(a, b)$ entry, with rows
and columns indexed from $0$, is $\frac{a!}{b!} [t^{a-b}] f$ for $b \le a$ and $0$ for $b > a$,
equals the constant coefficient $[t^0] f$ of $f$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Section 3. -/
theorem powerSeriesFactorialMatrix_apply_self {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (n : ℕ) (a : Fin n) :
    powerSeriesFactorialMatrix f n a a = PowerSeries.coeff 0 f := by
  have h : ((a : ℕ).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp [powerSeriesFactorialMatrix, h]

/-- **Multiplicativity of the factorial matrix of a power series.** Let $K$ be a field of
characteristic zero, let $f$ and $g$ be formal power series over $K$ in the variable $t$, and let
$n$ be a natural number. For a power series $h$ over $K$, write $M_n(h)$ for the $n \times n$
factorial matrix of $h$, whose entry in row $a$ and column $b$ (counted from $0$) is
$\frac{a!}{b!}$ times the coefficient of $t^{a-b}$ in $h$ when $b \le a$, and $0$ otherwise. Then
$M_n(f) M_n(g) = M_n(fg)$.

Since these matrices are lower triangular and $M_n(h)$ is the leading $n \times n$ section of the
infinite matrix $M(h)$, this is equivalent to $M(f) M(g) = M(fg)$.

Source: A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal and
Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4, Lemma 5
(`jis-2026-26.5.4-lem-5`). -/
public theorem_wanted powerSeriesFactorialMatrix_mul {K : Type*} [Field K] [CharZero K]
    (f g : PowerSeries K) (n : ℕ) :
    powerSeriesFactorialMatrix f n * powerSeriesFactorialMatrix g n =
      powerSeriesFactorialMatrix (f * g) n

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
