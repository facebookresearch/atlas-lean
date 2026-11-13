/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import WantedExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-!
# Matrices whose entries are Stirling numbers of the second kind

Statements from M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima
Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27.

Conventions. `S(n, k)` is `Nat.stirlingSecond` and the signed Stirling number of
the first kind `s(n, k)` is MathlibExt's `signedStirlingFirst`. The `n × n`
matrices are `Matrix (Fin n) (Fin n) ℚ`, entry `(a, b)` being the paper's
`(a + 1, b + 1)` entry. The Stirling matrix of the second kind `S(n)` is the
existing `stirlingMatrix2`. The paper takes `n` positive; for `n = 0` every
matrix identity below is trivial, so no hypothesis on `n` is added.
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-- **Shifted Stirling matrix of the second kind.** For natural numbers $m$ and $n$, the shifted
Stirling matrix $S^{[m]}(n)$ is the $n \times n$ matrix over $\mathbb{Q}$ whose $(i, j)$ entry is
the Stirling number of the second kind $S(i + m, j)$, for $1 \le i, j \le n$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `S^[m](n)`). -/
public def stirlingSecondShiftMatrix (m n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => (Nat.stirlingSecond (a.val + 1 + m) (b.val + 1) : ℚ)

/-- **Shift zero gives the Stirling matrix of the second kind.** For every natural number $n$, the
shifted Stirling matrix $S^{[0]}(n)$, the $n \times n$ rational matrix with entries $S(i + 0, j)$
for $1 \le i, j \le n$, equals the Stirling matrix of the second kind $S(n)$, the $n \times n$
rational matrix with entries $S(i, j)$; here $S(i, j)$ denotes the Stirling numbers of the
second kind.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `S^[m](n)`). -/
public theorem stirlingSecondShiftMatrix_zero (n : ℕ) :
    stirlingSecondShiftMatrix 0 n = stirlingMatrix2 n := by
  ext a b
  simp [stirlingSecondShiftMatrix, stirlingMatrix2]

/-- **First column of a shifted Stirling matrix.** Let $m$ and $n$ be natural numbers with $n > 0$,
and let $S^{[m]}(n)$ be the $n \times n$ rational matrix with entries $S(i + m, j)$ for
$1 \le i, j \le n$, where $S(i, j)$ denotes the Stirling numbers of the second kind. Every entry
of the first column of $S^{[m]}(n)$ equals $1$: $S(i + m, 1) = 1$ for $1 \le i \le n$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1, Equation (5). -/
public theorem stirlingSecondShiftMatrix_apply_zero_right {m n : ℕ} (a : Fin n)
    (h : 0 < n) : stirlingSecondShiftMatrix m n a ⟨0, h⟩ = 1 := by
  simp only [stirlingSecondShiftMatrix, Matrix.of_apply]
  rw [show a.val + 1 + m = (a.val + m) + 1 by omega, Nat.stirlingSecond_one_right]
  simp

/-- **Stirling matrix of the first kind.** For a natural number $n$, the Stirling matrix of the
first kind $s(n)$ is the $n \times n$ matrix with rational entries $s(n)_{i,j} = s(i, j)$ for
$1 \le i, j \le n$, where $s(i, j)$ is the signed Stirling number of the first kind. Its
entries above the diagonal are zero, since $s(i, j) = 0$ for $j > i$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (definition of `s(n)`). -/
public def stirlingFirstMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => (signedStirlingFirst (a.val + 1) (b.val + 1) : ℚ)

/-- **Diagonal of the Stirling matrix of the first kind.** For every natural number $n$, every
diagonal entry of the Stirling matrix of the first kind $s(n)$ equals $1$, that is,
$s(n)_{i,i} = 1$ for $1 \le i \le n$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 1 (`s(n, n) = 1`). -/
public theorem stirlingFirstMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingFirstMatrix n a a = 1 := by
  simp [stirlingFirstMatrix, signedStirlingFirst, Nat.stirlingFirst_self]

/-- **Upper bidiagonal matrix V(n).** For a natural number $n$, $V(n)$ is the $n \times n$
matrix over $\mathbb{Q}$, with rows and columns indexed by $1, \dots, n$, whose entries are
$V_{i,i} = i$ on the diagonal, $V_{i,i+1} = 1$ just above the diagonal, and $0$ elsewhere.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `V(n)`). -/
public def stirlingVMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if b = a then (a.val + 1 : ℚ) else if b.val = a.val + 1 then 1 else 0

/-- **Diagonal entries of the bidiagonal matrix V(n).** For every natural number $n$, let $V(n)$ be
the $n \times n$ rational upper bidiagonal matrix with $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$ and
all other entries $0$, indices running over $1, \dots, n$. Then $V(n)_{i,i} = i$ for every
$1 \le i \le n$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `V(n)`). -/
public theorem stirlingVMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingVMatrix n a a = a.val + 1 := by
  simp [stirlingVMatrix]

/-- **Upper triangular matrix Ṽ(n).** For a natural number $n$, $\tilde V(n)$ is the
$n \times n$ matrix over $\mathbb{Q}$, with rows and columns indexed by $1, \dots, n$, whose
$(i, j)$ entry is $(-1)^{j-i} (i-1)!/j!$ if $i \le j$ and $0$ if $i > j$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `Ṽ(n)`). -/
public def stirlingVTildeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if a ≤ b then
      (-1 : ℚ) ^ (b.val - a.val) * (a.val.factorial : ℚ) / ((b.val + 1).factorial : ℚ)
    else 0

/-- **Diagonal entries of the matrix Ṽ(n).** For a natural number $n$, let $\tilde V(n)$ be the
$n \times n$ upper triangular matrix over $\mathbb{Q}$, with rows and columns indexed by
$1, \dots, n$, whose $(i, j)$ entry is $(-1)^{j-i} (i-1)!/j!$ if $i \le j$ and $0$ if $i > j$.
Then for every $i$ with $1 \le i \le n$, the $(i, i)$ entry of $\tilde V(n)$ is $1/i$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `Ṽ(n)`). -/
public theorem stirlingVTildeMatrix_apply_self {n : ℕ} (a : Fin n) :
    stirlingVTildeMatrix n a a = 1 / (a.val + 1 : ℚ) := by
  simp only [stirlingVTildeMatrix, Matrix.of_apply, le_refl, ite_true, Nat.sub_self,
    pow_zero, one_mul, Nat.factorial_succ, Nat.cast_mul]
  have h : (a.val.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  push_cast
  ring

/-- **Shifted Vandermonde matrix.** For a natural number $n$, the shifted Vandermonde matrix
$E(n)$ is the $n \times n$ matrix with rational entries $E(n)_{i,j} = (j + 1)^{i-1}$ for
$1 \le i, j \le n$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `E(n)`). -/
public def shiftedVandermondeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => ((b.val + 2 : ℕ) : ℚ) ^ a.val

/-- **First row of the shifted Vandermonde matrix.** For every natural number $n \ge 1$, every
entry in the first row of the shifted Vandermonde matrix $E(n)$ equals $1$, that is,
$E(n)_{1,j} = 1$ for $1 \le j \le n$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2 (definition of `E(n)`). -/
public theorem shiftedVandermondeMatrix_apply_zero_left {n : ℕ} (h : 0 < n) (b : Fin n) :
    shiftedVandermondeMatrix n ⟨0, h⟩ b = 1 := by
  simp [shiftedVandermondeMatrix]

/-- **Strictly upper triangular matrix $Q^{[N]}(n)$.** For natural numbers $N$ and $n$,
$Q^{[N]}(n)$ is the $n \times n$ matrix with rational entries
$$Q^{[N]}(n)_{i,j} = \frac{(-1)^{j-i+1}\, i^{N-1}}{(i-1)!\,(j-i-1)!} \quad (1 \le i < j \le n)$$
and $Q^{[N]}(n)_{i,j} = 0$ for $1 \le j \le i \le n$. Here $N - 1$ is truncated subtraction,
so $Q^{[0]}(n) = Q^{[1]}(n)$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2, Equation (6). -/
public def stirlingQMatrix (N n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    if a.val + 1 ≤ b.val then
      (-1 : ℚ) ^ (b.val - a.val + 1) * ((a.val + 1 : ℕ) : ℚ) ^ (N - 1) /
        ((a.val.factorial : ℚ) * ((b.val - a.val - 1).factorial : ℚ))
    else 0

/-- **Vanishing of $Q^{[N]}(n)$ on and below the diagonal.** For natural numbers $N$ and $n$, let
$Q^{[N]}(n)$ be the $n \times n$ rational matrix with
$Q^{[N]}(n)_{i,j} = (-1)^{j-i+1} i^{N-1} / ((i-1)!\,(j-i-1)!)$ for $1 \le i < j \le n$ and $0$
otherwise, where $N - 1$ is truncated subtraction. Then $Q^{[N]}(n)_{i,j} = 0$ for all indices
$1 \le j \le i \le n$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Section 2, Equation (6). -/
public theorem stirlingQMatrix_apply_of_le {N n : ℕ} {a b : Fin n} (h : b ≤ a) :
    stirlingQMatrix N n a b = 0 := by
  have : ¬ a.val + 1 ≤ b.val := by
    have := Fin.le_iff_val_le_val.1 h
    omega
  simp only [stirlingQMatrix, Matrix.of_apply, this, ↓reduceIte]

/-- **Explicit inverse of the bidiagonal matrix V(n).** For every natural number $n$, let $V(n)$ be
the $n \times n$ rational upper bidiagonal matrix with $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$ and
all other entries $0$, and let $\tilde V(n)$ be the upper triangular matrix with
$\tilde V(n)_{i,j} = (-1)^{j-i} (i-1)!/j!$ for $j \ge i$ and $\tilde V(n)_{i,j} = 0$ for $j < i$,
all indices running over $1, \dots, n$. Then $V(n)^{-1} = \tilde V(n)$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 1 (`integers-2025-A27-lem-1`). -/
public theorem_wanted stirlingVMatrix_inv (n : ℕ) :
    (stirlingVMatrix n)⁻¹ = stirlingVTildeMatrix n

/-- **Recurrence for $Q^{[N]}(n)$ in $N$.** For natural numbers $n$ and $N$ with $N \ge 1$, let
$V(n)$ be the $n \times n$ upper bidiagonal matrix with $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$
and all other entries $0$, let $I_n$ be the $n \times n$ identity matrix, and for $M \ge 1$ let
$Q^{[M]}(n)$ be the $n \times n$ matrix with
$Q^{[M]}(n)_{i,j} = (-1)^{j-i+1} i^{M-1} / ((i-1)!\,(j-i-1)!)$ for $j \ge i + 1$ and $0$
otherwise. Then, as matrices over $\mathbb{Q}$,
$$Q^{[N+1]}(n) = Q^{[N]}(n)\,(V(n) - I_n).$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 2 (`integers-2025-A27-lem-2`). -/
public theorem_wanted stirlingQMatrix_succ {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingQMatrix (N + 1) n = stirlingQMatrix N n * (stirlingVMatrix n - 1)

/-- **Factorization of $Q^{[N]}(n)$ through $Q^{[1]}(n)$.** For natural numbers $n$ and $N$ with
$N \ge 1$, let $V(n)$ be the $n \times n$ upper bidiagonal matrix with $V(n)_{i,i} = i$,
$V(n)_{i,i+1} = 1$ and all other entries $0$, let $I_n$ be the $n \times n$ identity matrix,
and for $M \ge 1$ let $Q^{[M]}(n)$ be the $n \times n$ matrix with
$Q^{[M]}(n)_{i,j} = (-1)^{j-i+1} i^{M-1} / ((i-1)!\,(j-i-1)!)$ for $j \ge i + 1$ and $0$
otherwise. Then, as matrices over $\mathbb{Q}$,
$$Q^{[N]}(n) = Q^{[1]}(n)\,(V(n) - I_n)^{N-1}.$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 1 (`integers-2025-A27-cor-1`). -/
public theorem_wanted stirlingQMatrix_eq_one_mul_pow {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingQMatrix N n = stirlingQMatrix 1 n * (stirlingVMatrix n - 1) ^ (N - 1)

/-- **Stirling matrix of the second kind times $V(n) - I_n$.** Let $n$ be a natural number. Let
$S(n)$ be the $n \times n$ Stirling matrix of the second kind, with entries the Stirling numbers
of the second kind $S(i, j)$ for $1 \le i, j \le n$; let $V(n)$ be the $n \times n$ upper
bidiagonal matrix with $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$ and all other entries $0$; let
$I_n$ be the identity matrix, $E(n)$ the shifted Vandermonde matrix with
$E(n)_{i,j} = (j + 1)^{i-1}$, and $Q^{[1]}(n)$ the matrix with
$Q^{[1]}(n)_{i,j} = (-1)^{j-i+1} / ((i-1)!\,(j-i-1)!)$ for $j \ge i + 1$ and $0$ otherwise.
Then, as matrices over $\mathbb{Q}$,
$$S(n)\,(V(n) - I_n) = E(n)\,Q^{[1]}(n).$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Lemma 3, Equation (7) (`integers-2025-A27-lem-3`). -/
public theorem_wanted stirlingMatrix2_mul_sub_one (n : ℕ) :
    stirlingMatrix2 n * (stirlingVMatrix n - 1) =
      shiftedVandermondeMatrix n * stirlingQMatrix 1 n

/-- **Stirling matrix of the second kind times powers of $V(n) - I_n$.** Let $n$ and $N$ be
natural numbers with $N \ge 1$. Let $S(n)$ be the $n \times n$ Stirling matrix of the second
kind, with entries the Stirling numbers of the second kind $S(i, j)$ for $1 \le i, j \le n$; let
$V(n)$ be the $n \times n$ upper bidiagonal matrix with $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$
and all other entries $0$; let $I_n$ be the identity matrix, $E(n)$ the shifted Vandermonde
matrix with $E(n)_{i,j} = (j + 1)^{i-1}$, and $Q^{[N]}(n)$ the matrix with
$Q^{[N]}(n)_{i,j} = (-1)^{j-i+1} i^{N-1} / ((i-1)!\,(j-i-1)!)$ for $j \ge i + 1$ and $0$
otherwise. Then, as matrices over $\mathbb{Q}$,
$$S(n)\,(V(n) - I_n)^N = E(n)\,Q^{[N]}(n).$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 1 (`integers-2025-A27-thm-1`). -/
public theorem_wanted stirlingMatrix2_mul_sub_one_pow {N : ℕ} (hN : 0 < N) (n : ℕ) :
    stirlingMatrix2 n * (stirlingVMatrix n - 1) ^ N =
      shiftedVandermondeMatrix n * stirlingQMatrix N n

/-- **Factorization and determinant of shifted Stirling matrices.** For natural numbers $m$ and
$n$, let $S(n)$ and $S^{[m]}(n)$ be the $n \times n$ rational matrices with entries $S(i, j)$ and
$S(i + m, j)$, where $S(i, j)$ denotes the Stirling numbers of the second kind, and let $V(n)$ be
the upper bidiagonal matrix with $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$ and all other entries $0$,
all indices running over $1, \dots, n$. Then $S^{[m]}(n) = S(n)\, V(n)^m$ and
$\det S^{[m]}(n) = (n!)^m$.

The paper assumes $m, n \ge 1$; the cases $m = 0$ and $n = 0$ hold as well.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 2, Equation (18) (`integers-2025-A27-thm-2`). -/
public theorem_wanted stirlingSecondShiftMatrix_eq_mul_pow (m n : ℕ) :
    stirlingSecondShiftMatrix m n = stirlingMatrix2 n * stirlingVMatrix n ^ m ∧
      (stirlingSecondShiftMatrix m n).det = (n.factorial : ℚ) ^ m

/-- **Recurrence for shifted Stirling matrices.** For natural numbers $m$ and $n$, let $S^{[m]}(n)$
be the $n \times n$ rational matrix with entries $S(i + m, j)$, where $S(i, j)$ denotes the
Stirling numbers of the second kind, and let $V(n)$ be the upper bidiagonal matrix with
$V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$ and all other entries $0$, all indices running over
$1, \dots, n$. Then $S^{[m+1]}(n) = S^{[m]}(n)\, V(n)$ and
$\det S^{[m+1]}(n) = n! \cdot \det S^{[m]}(n)$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 2 (`integers-2025-A27-cor-2`). -/
public theorem_wanted stirlingSecondShiftMatrix_succ (m n : ℕ) :
    stirlingSecondShiftMatrix (m + 1) n = stirlingSecondShiftMatrix m n * stirlingVMatrix n ∧
      (stirlingSecondShiftMatrix (m + 1) n).det =
        (n.factorial : ℚ) * (stirlingSecondShiftMatrix m n).det

/-- **Composition of shifted Stirling matrices.** For natural numbers $m$ and $n$, let $S^{[m]}(n)$
be the $n \times n$ rational matrix with entries $S(i + m, j)$ for $1 \le i, j \le n$, where
$S(i, j)$ denotes the Stirling numbers of the second kind, and let $s(n)$ be the $n \times n$
rational matrix with entries the signed Stirling numbers of the first kind $s(i, j)$ for
$1 \le i, j \le n$. Then for all natural numbers $m_1$, $m_2$ and $n$,
$S^{[m_1 + m_2]}(n) = S^{[m_1]}(n)\, s(n)\, S^{[m_2]}(n)$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 3 (`integers-2025-A27-cor-3`). -/
public theorem_wanted stirlingSecondShiftMatrix_add (m₁ m₂ n : ℕ) :
    stirlingSecondShiftMatrix (m₁ + m₂) n =
      stirlingSecondShiftMatrix m₁ n * stirlingFirstMatrix n * stirlingSecondShiftMatrix m₂ n

/-- **Inverse of a shifted Stirling matrix.** For natural numbers $m$ and $n$, let $S^{[m]}(n)$ be
the $n \times n$ rational matrix with entries $S(i + m, j)$, where $S(i, j)$ denotes the Stirling
numbers of the second kind; let $s(n)$ be the matrix with entries the signed Stirling numbers of
the first kind $s(i, j)$; and let $\tilde V(n)$ be the upper triangular matrix with
$\tilde V(n)_{i,j} = (-1)^{j-i} (i-1)!/j!$ for $j \ge i$ and $\tilde V(n)_{i,j} = 0$ for $j < i$,
all indices running over $1, \dots, n$. Then $S^{[m]}(n)^{-1} = \tilde V(n)^m\, s(n)$.

The paper assumes $m \ge 1$; the case $m = 0$, which reads $S^{[0]}(n)^{-1} = s(n)$, holds as well.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 3 (`integers-2025-A27-thm-3`). -/
public theorem_wanted stirlingSecondShiftMatrix_inv (m n : ℕ) :
    (stirlingSecondShiftMatrix m n)⁻¹ = stirlingVTildeMatrix n ^ m * stirlingFirstMatrix n

/-- **Shifted orthogonality of Stirling numbers.** Write $s(n, k)$ for the signed Stirling
numbers of the first kind and $S(n, k)$ for the Stirling numbers of the second kind. For all
natural numbers $i$, $j$, $m$ with $1 \le j \le i$, the integer
$\sum_{l=1}^{i} s(i, l)\, S(l + m, j)$ equals $i^m$ if $i = j$ and $0$ if $i > j$.

The case $m = 0$ is included, although the source assumes $m \ge 1$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 4 (`integers-2025-A27-thm-4`). -/
public theorem_wanted sum_signedStirlingFirst_mul_stirlingSecond_add {i j : ℕ} (hj : 1 ≤ j)
    (hji : j ≤ i) (m : ℕ) :
    ∑ l ∈ Finset.Icc 1 i, signedStirlingFirst i l * (Nat.stirlingSecond (l + m) j : ℤ) =
      if i = j then (i : ℤ) ^ m else 0

/-- **Alternating binomial sums of shifted Stirling numbers of the second kind.** Write
$S(n, k)$ for the Stirling numbers of the second kind. For all natural numbers $i, j, N \ge 1$,
the following identity holds in the rational numbers:
$$\sum_{l=0}^{N} (-1)^{N-l} \binom{N}{l} S(i+l, j) =
\sum_{k=1}^{j-1} \frac{(-1)^{j-k+1} k^{N-1} (k+1)^{i-1}}{(k-1)!\,(j-k-1)!}.$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 5 (`integers-2025-A27-thm-5`). -/
public theorem_wanted sum_choose_stirlingSecond_eq {i j N : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hN : 1 ≤ N) :
    ∑ l ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ (N - l) * (N.choose l : ℚ) * (Nat.stirlingSecond (i + l) j : ℚ) =
      ∑ k ∈ Finset.Ico 1 j,
        (-1 : ℚ) ^ (j - k + 1) * (k : ℚ) ^ (N - 1) * ((k + 1 : ℕ) : ℚ) ^ (i - 1) /
          (((k - 1).factorial : ℚ) * ((j - k - 1).factorial : ℚ))

/-- **Difference of consecutive Stirling numbers of the second kind.** For natural numbers
$i \ge 1$ and $j \ge 1$, the Stirling numbers of the second kind $S(i, j)$ satisfy, in $\mathbb{Q}$,
$$
S(i + 1, j) - S(i, j) = \sum_{k=1}^{j-1} \frac{(-1)^{j-k+1} (k + 1)^{i-1}}{(k - 1)!\,(j - k - 1)!}.
$$

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Corollary 4 (`integers-2025-A27-cor-4`). -/
public theorem_wanted stirlingSecond_succ_sub_eq_sum {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (Nat.stirlingSecond (i + 1) j : ℚ) - Nat.stirlingSecond i j =
      ∑ k ∈ Finset.Ico 1 j,
        (-1 : ℚ) ^ (j - k + 1) * ((k + 1 : ℕ) : ℚ) ^ (i - 1) /
          (((k - 1).factorial : ℚ) * ((j - k - 1).factorial : ℚ))

/-- **Double-sum Kronecker delta identity for Stirling numbers.** Write $S(n, k)$ for the Stirling
numbers of the second kind and $s(n, k)$ for the signed Stirling numbers of the first kind. For
all natural numbers $i, j, n$ with $i \ge 1$, $n \ge i$ and $n \ge j$, in the rational numbers,
$$\sum_{k_1=1}^{n} \sum_{k_2=k_1}^{n} (-1)^{k_2-k_1} \frac{(k_1-1)!}{k_2!}\,
S(i+1, k_1)\, s(k_2, j) = \delta_{i,j},$$
where $\delta_{i,j}$ is $1$ if $i = j$ and $0$ otherwise.

The hypothesis $i \ge 1$ cannot be dropped: for $i = j = 0$ the left side is $0$. The source's
hypothesis $j \ge 1$ is not needed.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 6 (`integers-2025-A27-thm-6`). -/
public theorem_wanted sum_sum_stirlingSecond_signedStirlingFirst_eq_ite {i j n : ℕ}
    (hi : 1 ≤ i) (hn : max i j ≤ n) :
    ∑ k₁ ∈ Finset.Icc 1 n, ∑ k₂ ∈ Finset.Icc k₁ n,
        (-1 : ℚ) ^ (k₂ - k₁) * ((k₁ - 1).factorial : ℚ) / (k₂.factorial : ℚ) *
          (Nat.stirlingSecond (i + 1) k₁ : ℚ) * (signedStirlingFirst k₂ j : ℚ) =
      if i = j then 1 else 0

/-- **Stirling numbers of the second kind from the next row.** Write $S(n, k)$ for the Stirling
numbers of the second kind. For all natural numbers $i \ge 1$ and $j$, the rational number
$$\sum_{k=1}^{\min(i+1, j)} (-1)^{j-k} \frac{(k-1)!}{j!} S(i+1, k)$$
equals $S(i, j)$ if $j \le i$ and $0$ if $j > i$.

The case $j = 0$, where both sides vanish, is included although the source assumes $j \ge 1$.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 7 (`integers-2025-A27-thm-7`). -/
public theorem_wanted sum_stirlingSecond_succ_eq_ite {i j : ℕ} (hi : 1 ≤ i) :
    ∑ k ∈ Finset.Icc 1 (min (i + 1) j),
        (-1 : ℚ) ^ (j - k) * ((k - 1).factorial : ℚ) / (j.factorial : ℚ) *
          (Nat.stirlingSecond (i + 1) k : ℚ) =
      if j ≤ i then (Nat.stirlingSecond i j : ℚ) else 0

/-- **Double-sum shift identity for Stirling numbers.** Write $S(n, k)$ for the Stirling numbers
of the second kind and $s(n, k)$ for the signed Stirling numbers of the first kind. For all
natural numbers $i, j, n, m_1, m_2$ with $i \ge 1$, $n \ge i$ and $n \ge j$,
$$\sum_{k_1=1}^{n} \sum_{k_2=1}^{k_1} S(i+m_1, k_1)\, s(k_1, k_2)\, S(k_2+m_2, j) =
S(i+m_1+m_2, j).$$

The source leaves the shifts $m_1, m_2$ unquantified; here they are arbitrary natural numbers,
as in Corollary 3 of the source, and the source's hypothesis $j \ge 1$ is not needed.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy,
*On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*,
INTEGERS 25 (2025), Article A27, Theorem 8 (`integers-2025-A27-thm-8`). -/
public theorem_wanted sum_sum_stirlingSecond_signedStirlingFirst_stirlingSecond {i j n : ℕ}
    (hi : 1 ≤ i) (hn : max i j ≤ n) (m₁ m₂ : ℕ) :
    ∑ k₁ ∈ Finset.Icc 1 n, ∑ k₂ ∈ Finset.Icc 1 k₁,
        (Nat.stirlingSecond (i + m₁) k₁ : ℤ) * signedStirlingFirst k₁ k₂ *
          (Nat.stirlingSecond (k₂ + m₂) j : ℤ) =
      Nat.stirlingSecond (i + m₁ + m₂) j

end

end MetaMathlibExt
