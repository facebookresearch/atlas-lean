/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # Hyperbolic sums of arithmetic functions at the integer part

Statement-only requests from Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation
Involving Certain Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026),
Article A37. Following the source (arXiv:2412.16675v2, Section 1),
`S_{f,r}(x) = ∑_{n₁⋯n_r ≤ x} f(⌊x/(n₁⋯n_r)⌋) = ∑_{n ≤ x} f(⌊x/n⌋) τ_r(n)`, where
`τ_r(n) = (Nat.finMulAntidiag r n).card` counts the ordered factorizations of `n` into `r`
positive factors. The polynomial `P_r` with coefficients `a_j` is the one in
`∑_{n ≤ x} τ_r(n) = x P_r(log x) + O(x^{1-1/r} (log x)^{r-2})`; it is taken as a hypothesis
`P` satisfying that estimate, which determines it uniquely. The constants are
`C_i = ∑_{n ≥ 1} f(n) ((log n)^i/n - (log (n+1))^i/(n+1))`, written with the index
shifted to `n + 1`.
-/

open Asymptotics Filter

namespace MetaMathlibExt

@[expose] public section

/-- If `f(n) ≪ n^α` for some `α ∈ [0, 1)`, then for every fixed integer `i ≥ 0` the series
`∑_{n ≥ 1} f(n) ((log n)^i/n - (log (n+1))^i/(n+1))` converges absolutely.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Lemma 1 (`integers-2026-A37-lem-1`). -/
public theorem_wanted summable_abs_mul_log_pow_div_sub
    (f : ℕ → ℝ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hf : (fun n : ℕ => f n) =O[atTop] fun n : ℕ => (n : ℝ) ^ α) (i : ℕ) :
    Summable fun n : ℕ =>
      |f (n + 1) * (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))|

/-- Let `r ≥ 2` and let `f ≥ 0` satisfy `f(n) ≪ n^α` for some `α ∈ [0, 1)` and
`∑_{n ≤ x} f(n) ≪ x (log log x)^β` for some `β ≥ 0`. Then
`S_{f,r}(x) = x ∑_{j=0}^{r-1} ∑_{i=0}^{j} C(j,i) (-1)^i a_j C_i (log x)^{j-i}
+ O(x (log x)^{r-2} (log log x)^β)`. The hypothesis `0 ≤ f` is added: the source's proof
bounds its error sum `∑_{d ≤ x} f(d) O((x/d)^{1-1/r} (log (x/d))^{r-2})` through
`∑_{n ≤ x} f(n)`, which controls it only for nonnegative `f`.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Theorem 1 (`integers-2026-A37-thm-1`). -/
public theorem_wanted hyperbolic_floor_sum_asymptotic
    (r : ℕ) (hr : 2 ≤ r) (P : Polynomial ℝ)
    (hP : (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * P.eval (Real.log x)) =O[atTop]
        fun x : ℝ => x ^ (1 - 1 / (r : ℝ)) * Real.log x ^ (r - 2))
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hf : (fun n : ℕ => f n) =O[atTop] fun n : ℕ => (n : ℝ) ^ α)
    (β : ℝ) (hβ : 0 ≤ β)
    (hsum : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop]
        fun x : ℝ => x * Real.log (Real.log x) ^ β) :
    (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f ⌊x / n⌋₊ * ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (-1) ^ i * P.coeff j *
              (∑' n : ℕ, f (n + 1) *
                (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))) *
              Real.log x ^ (j - i)) =O[atTop]
      fun x : ℝ => x * Real.log x ^ (r - 2) * Real.log (Real.log x) ^ β

/-- Let `f(n) = ∑_{p^a ∥ n} g(a)` with `g(1) ≠ 0` and `g(n) = O(2^{n/2})`. With the
notation of Theorem 1,
`S_{f,r}(x) = x ∑_{j=0}^{r-1} ∑_{i=0}^{j} C(j,i) (-1)^i a_j C_i (log x)^{j-i}
+ O(x (log x)^{r-2} log log x)`. The sum over `p^a ∥ n` is the sum over
`p ∈ n.primeFactors` of `g (n.factorization p)`, so the source's convention `g(0) = 0` is
not needed.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Proposition 1 (`integers-2026-A37-prop-1`). -/
public theorem_wanted hyperbolic_floor_sum_asymptotic_additive
    (r : ℕ) (hr : 2 ≤ r) (P : Polynomial ℝ)
    (hP : (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * P.eval (Real.log x)) =O[atTop]
        fun x : ℝ => x ^ (1 - 1 / (r : ℝ)) * Real.log x ^ (r - 2))
    (g : ℕ → ℝ) (hg1 : g 1 ≠ 0)
    (hg : (fun n : ℕ => g n) =O[atTop] fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2)) :
    (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            (∑ p ∈ (⌊x / n⌋₊).primeFactors, g ((⌊x / n⌋₊).factorization p)) *
              ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (-1) ^ i * P.coeff j *
              (∑' n : ℕ, (∑ p ∈ (n + 1).primeFactors, g ((n + 1).factorization p)) *
                (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))) *
              Real.log x ^ (j - i)) =O[atTop]
      fun x : ℝ => x * Real.log x ^ (r - 2) * Real.log (Real.log x)

end

end MetaMathlibExt
