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

/-- Theorem 1: for `n > 2` positive reals `s_1 < ⋯ < s_n`, with MAX matrix
`M_S = (max (s_i, s_j))` and MIN matrix `N_S = (min (s_i, s_j))`, the g-eigenvalues of `M_S` to
`N_S` are `√(s_n / s_1)`, `-1` with multiplicity `n - 2`, and `-√(s_n / s_1)`. Stated as the
factorization of `det (M_S - X N_S)`, whose leading coefficient is `det (-N_S)`.

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

/-- Theorem 6 (Cauchy interlacing for g-eigenvalues): let `A` be a complex Hermitian and `B` a
positive definite `(n+1) × (n+1)` matrix (`n ≥ 1`), and `A'`, `B'` their leading principal
`n × n` submatrices. If `λ_1 ≥ ⋯ ≥ λ_{n+1}` enumerates the g-eigenvalues of `A` to `B` and
`λ'_1 ≥ ⋯ ≥ λ'_n` those of `A'` to `B'` (real numbers listing the roots of `det (A - X B)`,
respectively `det (A' - X B')`, with multiplicity), then
`λ_1 ≥ λ'_1 ≥ λ_2 ≥ ⋯ ≥ λ_n ≥ λ'_n ≥ λ_{n+1}`.

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
