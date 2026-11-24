/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Generalized eigenvalues of MAX matrices to MIN matrices

Statements from Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki, and Timo Tossavainen,
*On Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices*,
Journal of Integer Sequences 28 (2025), Article 25.7.1.

A generalized eigenvalue (g-eigenvalue) of `A` to `B` (with `B` invertible) is a root of
`det (A - λ B)`. The g-eigenvalues with multiplicity are the roots of the polynomial
`det (A - X • B)`, written `(A.map C - (X : R[X]) • B.map C).det`.
-/

open Polynomial
open scoped ComplexOrder

namespace MetaMathlibExt

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
public theorem_wanted det_maxMatrix_sub_X_smul_minMatrix (n : ℕ) (hn : 2 < n)
    (s : Fin n → ℝ) (hs : StrictMono s) (hpos : 0 < s ⟨0, by omega⟩) :
    ((Matrix.of fun i j => max (s i) (s j)).map C -
        (X : ℝ[X]) • (Matrix.of fun i j => min (s i) (s j)).map C).det =
      C ((-1) ^ n * (Matrix.of fun i j => min (s i) (s j)).det) *
        ((X - C (Real.sqrt (s ⟨n - 1, by omega⟩ / s ⟨0, by omega⟩))) *
          (X + 1) ^ (n - 2) *
          (X + C (Real.sqrt (s ⟨n - 1, by omega⟩ / s ⟨0, by omega⟩))))

/-- **Cauchy interlacing for generalized eigenvalues.** Let $n \ge 1$, let $A$ be a Hermitian
and $B$ a positive definite complex $(n+1) \times (n+1)$ matrix, and let $A'$ and $B'$ be their
leading principal $n \times n$ submatrices (rows and columns $1, \dots, n$). Let
$\lambda_1 \ge \dots \ge \lambda_{n+1}$ be real numbers such that the roots of the polynomial
$\det(A - XB)$, counted with multiplicity, are exactly $\lambda_1, \dots, \lambda_{n+1}$, and
let $\lambda'_1 \ge \dots \ge \lambda'_n$ be real numbers such that the roots of
$\det(A' - XB')$, counted with multiplicity, are exactly $\lambda'_1, \dots, \lambda'_n$. Then
$\lambda_{k+1} \le \lambda'_k \le \lambda_k$ for every $k = 1, \dots, n$.

Source: Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki, and Timo Tossavainen, *On
Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices*,
Journal of Integer Sequences 28 (2025), Article 25.7.1, Theorem 6 (`jis-2025-25.7.1-thm-6`). -/
public theorem_wanted generalizedEigenvalue_interlacing (n : ℕ) (hn : 1 ≤ n)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) (hB : B.PosDef)
    (lam : Fin (n + 1) → ℝ) (hlam : Antitone lam)
    (hroots : (A.map C - (X : ℂ[X]) • B.map C).det.roots =
      Finset.univ.val.map fun i => (lam i : ℂ))
    (lam' : Fin n → ℝ) (hlam' : Antitone lam')
    (hroots' : ((A.submatrix Fin.castSucc Fin.castSucc).map C -
        (X : ℂ[X]) • (B.submatrix Fin.castSucc Fin.castSucc).map C).det.roots =
      Finset.univ.val.map fun i => (lam' i : ℂ)) :
    ∀ k : Fin n, lam k.succ ≤ lam' k ∧ lam' k ≤ lam k.castSucc

end

end MetaMathlibExt
