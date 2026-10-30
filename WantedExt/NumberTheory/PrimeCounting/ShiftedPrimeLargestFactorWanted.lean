/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.MaxPrimeFac
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

/-! # Largest prime factors of shifted primes

Statement-only requests for the shifted-prime inputs in Lebowitz-Lockard and Saunders' bound for
runs of integers with constant Carmichael function: the Baker–Harman lower bound on primes `p`
whose shift `p + a` has a large prime factor, and the resulting count of large primes `q`
dividing some `p - 1`. Throughout, `c = 0.677`.
-/

open Filter

namespace MetaMathlibExt

@[expose] public section

/-- Baker–Harman: for every integer `a` and every `0 < θ ≤ 0.677` there is `0 < δ < 1` such that,
for all sufficiently large real `x`, the number of primes `p ≤ x` whose shift `p + a` has largest
prime factor `P(p + a) > x^θ` exceeds `δ x / log x`. Here `P(p + a)` is `Nat.maxPrimeFac` of
`|p + a|`. The quantifier over all `a ∈ ℤ` is the cited lemma's as printed; Baker and Harman
state the bound for a nonzero shift, and the extra case `a = 0` follows from the prime number
theorem (every prime in `(x^θ, x]` qualifies, and these number `(1 + o(1)) x / log x`).

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Lemma 1 (`integers-2024-A91-lem-1`), quoted
there from Baker and Harman. -/
public theorem_wanted exists_card_maxPrimeFac_prime_add_gt_rpow (a : ℤ) {θ : ℝ} (hθ : 0 < θ)
    (hθc : θ ≤ 677 / 1000) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ x : ℝ in atTop,
      δ * x / Real.log x <
        (((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ =>
          p.Prime ∧ x ^ θ < (Nat.maxPrimeFac ((p : ℤ) + a).natAbs : ℝ)).card : ℝ)

open scoped Classical in
/-- With `c = 0.677`, there is `C > 0` such that for all sufficiently large real `x`,
`x^c / log x ≤ C · #{q prime : q > x^c and q ∣ p - 1 for some prime p ≤ x}`. The congruence
`p ≡ 1 (mod q)` is written `p % q = 1`; every such `q` is at most `x`, so the count runs over
`q ≤ ⌊x⌋`.

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Lemma 2 (`integers-2024-A91-lem-2`). -/
public theorem_wanted exists_rpow_div_log_le_mul_card_prime_dvd_prime_sub_one :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      x ^ (677 / 1000 : ℝ) / Real.log x ≤
        C * (((Finset.range (⌊x⌋₊ + 1)).filter fun q : ℕ =>
          q.Prime ∧ x ^ (677 / 1000 : ℝ) < q ∧
            ∃ p ∈ Finset.range (⌊x⌋₊ + 1), p.Prime ∧ p % q = 1).card : ℝ)

/-- Runs of equal Carmichael values: with `c = 0.677`, the largest `k` such that
`λ(n + 1) = λ(n + 2) = ⋯ = λ(n + k)` for some `n` with `n + k ≤ x`, written `F_λ(x)`,
satisfies `F_λ(x) = O((log x)^{1/c})` as `x → ∞`.

`F_λ(x)` follows the arXiv version (arXiv:2402.06832v4, Section 1): `F_f(x)` is the largest `k`
for which `f(n+1) = ⋯ = f(n+k)` has a solution with `n + k ≤ x`. Here `n` ranges over `ℕ` and `λ`
is `ArithmeticFunction.carmichael`. The admissible `k` are bounded by `x`, so `sSup` is their
maximum.

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Theorem 3 (`integers-2024-A91-thm-3`). -/
public theorem_wanted carmichael_constant_run_length_isBigO :
    (fun x : ℝ => ((sSup {k : ℕ | ∃ n : ℕ, ((n + k : ℕ) : ℝ) ≤ x ∧
        ∀ i ∈ Finset.Icc 1 k, ArithmeticFunction.carmichael (n + i) =
          ArithmeticFunction.carmichael (n + 1)} : ℕ) : ℝ)) =O[atTop]
      fun x : ℝ => Real.log x ^ ((1000 : ℝ) / 677)


/-- Pollack–Pomerance–Treviño: the largest `k` such that `φ(n + 1) ≥ φ(n + 2) ≥ ⋯ ≥ φ(n + k)`
for some `n` with `n + k ≤ x`, written `G_φ(x)`, satisfies
`G_φ(x) ∼ log₃ x / log₆ x` as `x → ∞`, where `log_k` is the `k`-th iterate of the natural
logarithm.

`G_φ(x)` follows the paper's definition (arXiv:2402.06832v4, Section 1): `G_f(x)` is the largest
`k` for which `f(n+1) ≥ f(n+2) ≥ ⋯ ≥ f(n+k)` has a solution with `n + k ≤ x`. Here `n` ranges
over `ℕ`, `φ` is `Nat.totient`, and the chain is written as `φ(n + i + 1) ≤ φ(n + i)` for
`1 ≤ i < k`. The admissible `k` are bounded by `x`, so `sSup` is their maximum.

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Theorem 1 (`integers-2024-A91-thm-1`),
quoted there from Pollack, Pomerance, and Treviño. -/
public theorem_wanted totient_nonincreasing_run_length_isEquivalent :
    Asymptotics.IsEquivalent atTop
      (fun x : ℝ => ((sSup {k : ℕ | ∃ n : ℕ, ((n + k : ℕ) : ℝ) ≤ x ∧
        ∀ i ∈ Finset.Ico 1 k, Nat.totient (n + i + 1) ≤ Nat.totient (n + i)} : ℕ) : ℝ))
      fun x : ℝ => Real.log^[3] x / Real.log^[6] x

end

end MetaMathlibExt
