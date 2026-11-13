/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Some identities involving Stirling numbers arising from matrix decompositions

Statements from M. Bahrami-Taghanaki, A. R. Moghaddamfar,
Nima Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
*Journal of Integer Sequences* 27 (2024), Article 24.5.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Moghaddamfar/mogh14.tex>).

For a sequence `α : ℕ → ℚ`, the paper's Stirling-like
matrix `S_α` is given entrywise (in the paper's 1-based
indexing) by `stirlingLikeEntry`, defined by the recurrence
`S_{i,j} = S_{i-1,j-1} + j S_{i-1,j}` with first row
`α_{j-1}` and first column `α₀`; `uEntry` is the analogous
recurrence for `U_α`, and `rEntry`/`rTildeEntry` are the
closed forms for `R_α` and its inverse candidate
`R̃_α`, built from `psi` (`Ψ_α(k) = ∑_{l<k} α_l/(k-1-l)!`)
and `omega` (`Ω(α,j) = ∑_{l<j} (j-1)↓_l α_l`). The paper's
`Λ(α,k₁,k₂)` is `lambda`; `s(i,j)` is MathlibExt's
`signedStirlingFirst` and `S(i,j)` is
`Nat.stirlingSecond`. Finite matrices are `Matrix (Fin n)
(Fin n) ℚ` with entry `(a,b)` the paper's
`(a+1, b+1)`-entry. Entry values at index `0` are junk
(`0`); all statements quantify over indices `≥ 1` as in the
paper. All identities were verified numerically for a test
sequence `α` before stating.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-- **Entries of the Stirling-like matrix $S_\alpha$.** For a sequence
$\alpha = (\alpha_0, \alpha_1, \dots)$ of rationals, the numbers $S_{i,j}$ for natural numbers
$i, j$ are defined recursively by $S_{1,j} = \alpha_{j-1}$ for $j \ge 1$, $S_{i,1} = \alpha_0$ for
$i \ge 2$, $S_{i,j} = S_{i-1,j-1} + j \, S_{i-1,j}$ for $i, j \ge 2$, and $S_{i,j} = 0$ when
$i = 0$ or $j = 0$. -/
def stirlingLikeEntry (α : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, j => if j = 0 then 0 else α (j - 1)
  | i + 2, j =>
      if j = 1 then α 0
      else if j = 0 then 0
      else stirlingLikeEntry α (i + 1) (j - 1) +
        (j : ℚ) * stirlingLikeEntry α (i + 1) j

/-- **Entries of the matrix $U_\alpha$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$
of rational numbers, the entries $U_{i,j}$ ($i, j \ge 1$) of the matrix $U_\alpha$ are defined by
recursion on the row index $i$. The first row is $U_{1,j} = \alpha_{j-1}$. For $i \ge 2$ the
first column is $U_{i,1} = 0$, and for $j \ge 2$

$$U_{i,j} = U_{i-1,j-1} + (j - i + 1)\, U_{i-1,j}.$$

Entries with $i = 0$ or $j = 0$ are set to $0$. -/
def uEntry (α : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, j => if j = 0 then 0 else α (j - 1)
  | i + 2, j =>
      if j ≤ 1 then 0
      else uEntry α (i + 1) (j - 1) +
        ((j : ℚ) - (i + 2) + 1) * uEntry α (i + 1) j

/-- **The sum $\Psi_\alpha(k)$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and a natural number $k$, $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$;
in particular $\Psi_\alpha(0) = 0$. -/
def psi (α : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ l ∈ Finset.range k, α l / (k - 1 - l).factorial

/-- **The sum $\Omega(\alpha, j)$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and a natural number $j$,
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$, where
$m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial; in particular
$\Omega(\alpha, 0) = 0$. -/
def omega (α : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Finset.range j,
    (Nat.descFactorial (j - 1) l : ℚ) * α l

/-- **The sum $\Lambda(\alpha, k_1, k_2)$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$
of rationals and natural numbers $k_1, k_2$,
$$
\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1},
$$
where differences of natural numbers are truncated at $0$ (this matters only when $k_2 < k_1$). -/
def lambda (α : ℕ → ℚ) (k₁ k₂ : ℕ) : ℚ :=
  ∑ l ∈ Finset.range k₁, (Nat.choose (k₁ - 1) l : ℚ) *
    ((l + k₂ - k₁).factorial : ℚ) / (k₂ - k₁).factorial *
    α (l + k₂ - k₁)

/-- **Entries of the matrix $R_\alpha$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and natural numbers $i, j$, the entry $R_{i,j}$ is
$\frac{(-1)^{j-i}}{(j-i)!} \Psi_\alpha(i)$ if $i \le j$ and $0$ if $i > j$, where
$\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$. The matrix $R_\alpha$ uses the
indices $i, j \ge 1$. -/
def rEntry (α : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if i ≤ j then (-1 : ℚ) ^ (j - i) / (j - i).factorial * psi α i
  else 0

/-- **Entries of the matrix $\tilde R_\alpha$.** For a sequence
$\alpha = (\alpha_0, \alpha_1, \dots)$ of rationals and natural numbers $i, j$, the entry
$\tilde R_{i,j}$ is $(j-1)^{\underline{i-1}} / \Omega(\alpha, j)$ if $i \le j$ and $0$ if
$i > j$, where $\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$,
$m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial, $0 - 1$ is read as $0$, and
division by $0$ gives $0$. The matrix $\tilde R_\alpha$ uses the indices $i, j \ge 1$. -/
def rTildeEntry (α : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if i ≤ j then
    (Nat.descFactorial (j - 1) (i - 1) : ℚ) / omega α j
  else 0

/-- **Stirling-like matrix.** For a sequence $\alpha \colon \mathbb{N} \to \mathbb{Q}$ and
$n \in \mathbb{N}$, the Stirling-like matrix $S_\alpha(n)$ is the $n \times n$ rational matrix,
with rows and columns indexed by $1, \dots, n$, whose $(i, j)$ entry is $S_{i,j}$, where
$S_{1,j} = \alpha_{j-1}$ for $j \ge 1$, $S_{i,1} = \alpha_0$ for $i \ge 2$, and
$S_{i,j} = S_{i-1,j-1} + j \, S_{i-1,j}$ for $i, j \ge 2$. -/
def stirlingLikeMatrix (α : ℕ → ℚ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => stirlingLikeEntry α (a.val + 1) (b.val + 1)

/-- **The matrix $U_\alpha(n)$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and a natural number $n$, $U_\alpha(n)$ is the $n \times n$ rational matrix whose
$(i, j)$ entry, for $1 \le i, j \le n$, is $U_{i,j}$, where $U_{1,j} = \alpha_{j-1}$ for
$j \ge 1$, $U_{i,1} = 0$ for $i \ge 2$, and $U_{i,j} = U_{i-1,j-1} + (j - i + 1) \, U_{i-1,j}$
for $i, j \ge 2$. -/
def uMatrix (α : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => uEntry α (a.val + 1) (b.val + 1)

/-- **The matrix $R_\alpha(n)$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and a natural number $n$, $R_\alpha(n)$ is the $n \times n$ rational matrix whose
$(i, j)$ entry, for $1 \le i, j \le n$, is $\frac{(-1)^{j-i}}{(j-i)!} \Psi_\alpha(i)$ if
$i \le j$ and $0$ if $i > j$, where
$\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$. -/
def rMatrix (α : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => rEntry α (a.val + 1) (b.val + 1)

/-- **The matrix $\tilde R_\alpha(n)$.** For a sequence $\alpha = (\alpha_0, \alpha_1, \dots)$ of
rationals and a natural number $n$, $\tilde R_\alpha(n)$ is the $n \times n$ rational matrix
whose $(i, j)$ entry, for $1 \le i, j \le n$, is $(j-1)^{\underline{i-1}} / \Omega(\alpha, j)$
if $i \le j$ and $0$ if $i > j$, where
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$,
$m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial, and division by $0$ gives
$0$. -/
def rTildeMatrix (α : ℕ → ℚ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => rTildeEntry α (a.val + 1) (b.val + 1)

/-- **Stirling matrix of the second kind.** For $n \in \mathbb{N}$, the Stirling matrix of the
second kind $S(n)$ is the $n \times n$ rational matrix, with rows and columns indexed by
$1, \dots, n$, whose $(i, j)$ entry is the Stirling number of the second kind $S(i, j)$, the
number of partitions of an $i$-element set into $j$ nonempty blocks. -/
def stirlingMatrix2 (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    (Nat.stirlingSecond (a.val + 1) (b.val + 1) : ℚ)

/-- **The Vandermonde matrix $V(n)$.** For $n \in \mathbb{N}$, $V(n)$ is the $n \times n$ rational
matrix whose entry in row $i$ and column $j$ ($1 \le i, j \le n$) is $V_{i,j} = j^{i-1}$. -/
def vandermondeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => ((b.val + 1 : ℕ) : ℚ) ^ a.val

/-- **Explicit formula for the entries of $U_\alpha$.** Let
$\alpha \colon \mathbb{N} \to \mathbb{Q}$ and let $U_\alpha = (U_{i,j})_{i \ge 1, j \ge 0}$ be
given by $U_{i,0} = 0$, $U_{1,j} = \alpha_{j-1}$ for $j \ge 1$, $U_{i,1} = 0$ for $i \ge 2$, and
$U_{i,j} = U_{i-1,j-1} + (j-i+1) \, U_{i-1,j}$ for $i, j \ge 2$. For $k_1 \le k_2$ let
$\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1}$. Then $U_{i,j} = \Lambda(\alpha, i, j)$
for all $1 \le i \le j$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 1. -/
theorem_wanted uEntry_eq_lambda (α : ℕ → ℚ) (i j : ℕ)
    (hi : 1 ≤ i) (hij : i ≤ j) :
    uEntry α i j = lambda α i j

/-- **The matrix $U_\alpha$ is upper triangular.** Let $\alpha \colon \mathbb{N} \to \mathbb{Q}$
and let $U_\alpha = (U_{i,j})_{i \ge 1, j \ge 0}$ be given by $U_{i,0} = 0$,
$U_{1,j} = \alpha_{j-1}$ for $j \ge 1$, $U_{i,1} = 0$ for $i \ge 2$, and
$U_{i,j} = U_{i-1,j-1} + (j-i+1) \, U_{i-1,j}$ for $i, j \ge 2$. Then $U_{i,j} = 0$ for all
natural numbers $j < i$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 1. -/
theorem_wanted uEntry_eq_zero_of_lt (α : ℕ → ℚ) (i j : ℕ)
    (h : j < i) :
    uEntry α i j = 0

/-- **Column sums of the matrix $R_\alpha$.** Let $\alpha \colon \mathbb{N} \to \mathbb{Q}$, let
$\Psi_\alpha(k) = \sum_{l=0}^{k-1} \alpha_l / (k-1-l)!$, and let $R_\alpha$ be the matrix with
entries $R_{i,j} = \frac{(-1)^{j-i}}{(j-i)!} \Psi_\alpha(i)$ for $1 \le i \le j$ and
$R_{i,j} = 0$ for $i > j$. Then for every $j \ge 1$, $\sum_{i=1}^{j} R_{i,j} = \alpha_{j-1}$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 2. -/
theorem_wanted sum_rEntry_col (α : ℕ → ℚ) (j : ℕ)
    (hj : 1 ≤ j) :
    ∑ i ∈ Finset.Icc 1 j, rEntry α i j = α (j - 1)

/-- **Two factorizations of the Stirling-like matrix.** Let
$\alpha = (\alpha_0, \alpha_1, \dots)$ be a sequence of rationals. For natural numbers
$i, j \ge 1$ define $S_{i,j}$ and $U_{i,j}$ by $S_{1,j} = U_{1,j} = \alpha_{j-1}$,
$S_{i,1} = \alpha_0$ and $U_{i,1} = 0$ for $i \ge 2$, and, for $i, j \ge 2$,
$S_{i,j} = S_{i-1,j-1} + j \, S_{i-1,j}$ and $U_{i,j} = U_{i-1,j-1} + (j-i+1) \, U_{i-1,j}$;
let $R_{i,j} = \frac{(-1)^{j-i}}{(j-i)!} \Psi_\alpha(i)$ if $i \le j$ and $R_{i,j} = 0$ if
$i > j$, where $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$. For every natural
number $n$, let $S_\alpha(n)$, $U_\alpha(n)$ and $R_\alpha(n)$ be the $n \times n$ matrices
$(S_{i,j})$, $(U_{i,j})$ and $(R_{i,j})$ with $1 \le i, j \le n$, let
$S(n) = (S(i,j))_{1 \le i, j \le n}$ be the matrix of Stirling numbers of the second kind, and
let $V(n) = (j^{i-1})_{1 \le i, j \le n}$. Then $S_\alpha(n) = S(n) \, U_\alpha(n)$ and
$S_\alpha(n) = V(n) \, R_\alpha(n)$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Theorem 3. -/
theorem_wanted stirlingLikeMatrix_decomp (α : ℕ → ℚ)
    (n : ℕ) :
    stirlingLikeMatrix α n = stirlingMatrix2 n * uMatrix α n ∧
      stirlingLikeMatrix α n = vandermondeMatrix n * rMatrix α n

/-- **Determinant of the Stirling-like matrix.** For a sequence
$\alpha \colon \mathbb{N} \to \mathbb{Q}$ and $j \ge 1$ let
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$, where
$m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial. Then for every
$n \in \mathbb{N}$ the determinant of the $n \times n$ Stirling-like matrix $S_\alpha(n)$ is
$\det S_\alpha(n) = \prod_{j=1}^{n} \Omega(\alpha, j)$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Theorem 4. -/
theorem_wanted stirlingLikeMatrix_det (α : ℕ → ℚ) (n : ℕ) :
    (stirlingLikeMatrix α n).det =
      ∏ i ∈ Finset.range n, omega α (i + 1)

/-- **Second-kind Stirling transform of the $\Lambda$ coefficients.** Let
$\alpha \colon \mathbb{N} \to \mathbb{Q}$, let $S(i, k)$ denote the Stirling numbers of the
second kind, let $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \alpha_l / (k-1-l)!$, and for $k_1 \le k_2$
let $\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1}$. Then for all $i, j \ge 1$,

$$\sum_{k=1}^{\min(i,j)} S(i,k) \, \Lambda(\alpha, k, j) =
\sum_{k=1}^{j} k^{i-1} \, \frac{(-1)^{j-k}}{(j-k)!} \, \Psi_\alpha(k).$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 5. -/
theorem_wanted sum_stirlingSecond_lambda (α : ℕ → ℚ)
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.Icc 1 (min i j),
        (Nat.stirlingSecond i k : ℚ) * lambda α k j =
      ∑ k ∈ Finset.Icc 1 j, (k : ℚ) ^ (i - 1) *
        ((-1 : ℚ) ^ (j - k) / (j - k).factorial) * psi α k

-- Corollary 6 of the paper (the classical formula
-- `S(i,j) = (1/j!) ∑_{k=1}^j C(j,k) (-1)^{j-k} k^i`) is
-- already proved in MathlibExt as
-- `MetaMathlibExt.stirlingSecond_mul_factorial_eq_sum`
-- and is therefore not restated here.


/-- **The inverse of the matrix $R_\alpha(n)$.** For a sequence
$\alpha = (\alpha_0, \alpha_1, \dots)$ of rationals, let
$\Psi_\alpha(k) = \sum_{l=0}^{k-1} \frac{\alpha_l}{(k-1-l)!}$ and
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$, where
$m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ is the falling factorial. For a natural number $n$,
let $R_\alpha(n)$ and $\tilde R_\alpha(n)$ be the upper triangular $n \times n$ rational
matrices whose $(i, j)$ entries for $1 \le i \le j \le n$ are
$\frac{(-1)^{j-i}}{(j-i)!} \Psi_\alpha(i)$ and $(j-1)^{\underline{i-1}} / \Omega(\alpha, j)$
respectively. If $\prod_{j=1}^{n} \Omega(\alpha, j) \ne 0$, then
$\tilde R_\alpha(n) = R_\alpha(n)^{-1}$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 7. -/
theorem_wanted rTildeMatrix_eq_inv (α : ℕ → ℚ) (n : ℕ)
    (h : ∏ j ∈ Finset.Icc 1 n, omega α j ≠ 0) :
    rTildeMatrix α n = (rMatrix α n)⁻¹

/-- **Stirling and falling-factorial sum of the $\Lambda$ coefficients.** Let
$\alpha \colon \mathbb{N} \to \mathbb{Q}$, let $S(i, k)$ denote the Stirling numbers of the
second kind, let $m^{\underline{l}} = m(m-1)\cdots(m-l+1)$ be the falling factorial, let
$\Omega(\alpha, j) = \sum_{l=0}^{j-1} (j-1)^{\underline{l}} \, \alpha_l$, and for $k_1 \le k_2$
let $\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1}$. If $i, j \ge 1$ and
$\prod_{k=1}^{\max(i,j)} \Omega(\alpha, k) \ne 0$, then

$$\sum_{k_1=1}^{i} \sum_{k_2=k_1}^{j} S(i,k_1) \, (j-1)^{\underline{k_2-1}} \,
\Lambda(\alpha, k_1, k_2) = j^{i-1} \, \Omega(\alpha, j).$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 8. -/
theorem_wanted sum_stirlingSecond_descFactorial_lambda
    (α : ℕ → ℚ) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : ∏ k ∈ Finset.Icc 1 (max i j), omega α k ≠ 0) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc k₁ j,
        (Nat.stirlingSecond i k₁ : ℚ) *
          (Nat.descFactorial (j - 1) (k₂ - 1) : ℚ) *
          lambda α k₁ k₂ =
      (j : ℚ) ^ (i - 1) * omega α j

/-- **First-kind Stirling formula for $\Lambda(\alpha, i, j)$.** Let
$\alpha \colon \mathbb{N} \to \mathbb{Q}$, let $s(i, k)$ denote the signed Stirling numbers of
the first kind, let $\Psi_\alpha(k) = \sum_{l=0}^{k-1} \alpha_l / (k-1-l)!$, and for
$k_1 \le k_2$ let $\Lambda(\alpha, k_1, k_2) = \sum_{l=0}^{k_1-1} \binom{k_1-1}{l}
\frac{(l+k_2-k_1)!}{(k_2-k_1)!} \, \alpha_{l+k_2-k_1}$. Then for all $i, j \ge 1$ the sum

$$\sum_{k_1=1}^{i} \sum_{k_2=1}^{j} s(i,k_1) \, k_2^{k_1-1} \, \frac{(-1)^{j-k_2}}{(j-k_2)!} \,
\Psi_\alpha(k_2)$$

equals $\Lambda(\alpha, i, j)$ if $i \le j$ and $0$ if $i > j$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 9. -/
theorem_wanted sum_signed_psi_eq (α : ℕ → ℚ) (i j : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc 1 j,
        (MetaMathlibExt.signedStirlingFirst i k₁ : ℚ) * (k₂ : ℚ) ^ (k₁ - 1) *
          ((-1 : ℚ) ^ (j - k₂) / (j - k₂).factorial) * psi α k₂ =
      if i ≤ j then lambda α i j else 0

/-- **Kronecker-delta identity for signed Stirling numbers of the first kind.** Let $s(i, k)$
denote the signed Stirling numbers of the first kind and $\delta_{i,j}$ the Kronecker delta
($1$ if $i = j$ and $0$ otherwise). Then for all integers $i, j \ge 1$, in $\mathbb{Q}$,

$$\sum_{k_1=1}^{i} \sum_{k_2=1}^{j}
\frac{(-1)^{j-k_2} \, s(i,k_1) \, k_2^{k_1-1}}{(j-k_2)! \, (k_2-1)!} = \delta_{i,j}.$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Corollary 10. -/
theorem_wanted sum_signed_eq_delta (i j : ℕ) (hi : 1 ≤ i)
    (hj : 1 ≤ j) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc 1 j,
        (-1 : ℚ) ^ (j - k₂) * (MetaMathlibExt.signedStirlingFirst i k₁ : ℚ) *
          (k₂ : ℚ) ^ (k₁ - 1) /
          ((j - k₂).factorial * (k₂ - 1).factorial) =
      if i = j then 1 else 0

end MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted
