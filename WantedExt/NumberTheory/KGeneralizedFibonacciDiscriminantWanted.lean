/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- For `k ≥ 2`, the absolute value of the discriminant of the `k`-generalized Fibonacci
polynomial `X^k - X^{k-1} - ⋯ - X - 1` is a term `F^{(k)}_n` (`n ≥ 0`) of the
`k`-generalized Fibonacci sequence exactly when `k = 2` (`|Disc| = 5 = F_5`) or `k = 3`
(`|Disc| = 44 = F^{(3)}_8`). The sequence `F^{(k)}` is given by its defining properties on
the integer indices `n ≥ 2 - k`: `F_{2-k} = ⋯ = F_0 = 0`, `F_1 = 1`, and
`F_n = F_{n-1} + ⋯ + F_{n-k}` for `n ≥ 2`. The discriminant is Mathlib's `Polynomial.discr`
(the classical discriminant for this monic polynomial). The extracted statement prints the
target set as `{F_n}`; the superscript `(k)` is restored from the paper's own Lemma 1 text
(`F^{(k)}_n - f_k(α)α^{n-2}`) and from Batte and Luca's restatement of this theorem
(arXiv 2504.02514, Introduction); with the classical Fibonacci numbers the case `k = 3` fails,
since `44` is not a Fibonacci number.

Source: Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*,
The Fibonacci Quarterly 62 (2024), no. 3, Theorem 1 (`fq-2024-luca02082024-thm-1`). -/
public theorem_wanted abs_discr_kGeneralizedFibonacciPolynomial_mem_iff (k : ℕ) (hk : 2 ≤ k)
    (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ))) :
    (∃ n : ℕ, |(X ^ k - ∑ i ∈ Finset.range k, X ^ i : ℤ[X]).discr| = F n) ↔ k = 2 ∨ k = 3

/-- Size of `n` in the paper's equation (7),
`F^{(k)}_n = (2^{k+1} k^k - (k+1)^{k+1}) / (k-1)^2`: for `k > 100`,
`k + 1.99 + (k log k - 2 log(k-1)) / log 2 < n < k + 3.01 + (k log k - 2 log(k-1)) / log 2`.

Source: Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*,
The Fibonacci Quarterly 62 (2024), no. 3, Lemma 1 (`fq-2024-luca02082024-lem-1`). Equation (7) is written after
multiplying by `(k-1)^2`; `F^{(k)}` is given by its defining properties as in
`abs_discr_kGeneralizedFibonacciPolynomial_mem_iff`. By Theorem 1 the equation has no
solution with `k > 100`, so this intermediate bound is implied by that statement. -/
public theorem_wanted kGeneralizedFibonacci_discr_eq_index_bounds (k : ℕ) (hk : 100 < k)
    (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    (n : ℕ)
    (h7 : F n * ((k : ℤ) - 1) ^ 2 = 2 ^ (k + 1) * (k : ℤ) ^ k - ((k : ℤ) + 1) ^ (k + 1)) :
    (k : ℝ) + 1.99 + ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2 <
        (n : ℝ) ∧
      (n : ℝ) < (k : ℝ) + 3.01 +
        ((k : ℝ) * Real.log k - 2 * Real.log ((k : ℝ) - 1)) / Real.log 2

/-- Absolute bounds in the paper's equation (7): for `k > 100`, `k < 2·10^16` and
`n < 1.5·10^18`.

Source: Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*,
The Fibonacci Quarterly 62 (2024), no. 3, Lemma 2 (`fq-2024-luca02082024-lem-2`). Equation (7) is written after
multiplying by `(k-1)^2`, as in `kGeneralizedFibonacci_discr_eq_index_bounds`; by Theorem 1
the hypotheses are never met. -/
public theorem_wanted kGeneralizedFibonacci_discr_eq_bounds (k : ℕ) (hk : 100 < k)
    (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    (n : ℕ)
    (h7 : F n * ((k : ℤ) - 1) ^ 2 = 2 ^ (k + 1) * (k : ℤ) ^ k - ((k : ℤ) + 1) ^ (k + 1)) :
    k < 2 * 10 ^ 16 ∧ 2 * n < 3 * 10 ^ 18

end

end MetaMathlibExt
