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
public import MathlibExt.LinearAlgebra.GeneralizedEigenvalueInterlacing

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

end

end MetaMathlibExt
