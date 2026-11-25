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
public import MathlibExt.Combinatorics.Enumerative.ShiftedAlphaStirlingMatrix

/-!
# A generalization of the Pascal and Stirling matrices

Statements from A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *A Generalization of the Pascal
and Stirling Matrices*, Journal of Integer Sequences 29 (2026), Article 26.5.4.

The α-upper entries, their symmetric polynomial formula, the matrix and its determinant formula
are in `MathlibExt.Combinatorics.Enumerative.AlphaUpperMatrix`. The α-Stirling and shifted
α-Stirling entries and matrices, the factorization, and the shifted determinant formula are in
`MathlibExt.Combinatorics.Enumerative.ShiftedAlphaStirlingMatrix`.

The factorial matrix of a power series (`powerSeriesFactorialMatrix`), the lemma on its diagonal
entries (`powerSeriesFactorialMatrix_apply_self`) and the proved multiplicativity
`powerSeriesFactorialMatrix_mul` are in
`MathlibExt.Combinatorics.Enumerative.PascalStirlingGeneralization`, which this module imports.
-/

open scoped Matrix

namespace MetaMathlibExt

@[expose] public section

variable {R : Type*} [CommRing R]

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
