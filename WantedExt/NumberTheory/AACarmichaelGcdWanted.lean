/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import MathlibExt.NumberTheory.AACarmichaelGcd

namespace MetaMathlibExt

@[expose] public section

/-- Conditional lower bound for `(a, a)`-Carmichael numbers with prescribed gcd. Assume
Conjecture 2 (there are `A ≥ 2` and `l₀` such that for every `l ≥ l₀` and every `b` coprime to
`l` there is a prime `p ≡ b (mod l)` with `p < l (log l)^A`). Let `a` be an integer and `ν` a
positive integer with `gcd(a, ν) = 1` and `a`, `ν` of opposite parity. Then the number
`C_ν(X, a)` of `(a, a)`-Carmichael numbers `n ≤ X` with `gcd_{p ∣ n}(p - a) = ν` satisfies
`C_ν(X, a) ≥ X^{1 - (2 + o(1)) log log log log X / log log log X}`, written here as: for every
`ε > 0` the bound with `2 + ε` in place of `2 + o(1)` holds for all large `X`.

The gcd is the normalized (nonnegative) `Finset.gcd` in `ℤ`. The definitions of `C_ν(X, a)`
and Conjecture 2 are read from the arXiv version (arXiv:2607.02738); the theorem's journal
wording matches it.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Theorem 1 (`integers-2026-A123-thm-1`). -/
public theorem_wanted aaCarmichael_count_ge_of_least_prime_in_progression_bound
    (hconj : ∃ A : ℝ, 2 ≤ A ∧ ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∀ b : ℤ, Int.gcd b l = 1 →
      ∃ p : ℕ, p.Prime ∧ (p : ℤ) ≡ b [ZMOD l] ∧ (p : ℝ) < l * Real.log l ^ A)
    (a : ℤ) (ν : ℕ) (hν : 0 < ν) (hcop : Int.gcd a ν = 1) (hpar : Odd (a + ν))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      X ^ (1 - (2 + ε) * Real.log (Real.log (Real.log (Real.log X))) /
          Real.log (Real.log (Real.log X))) ≤
        ({n : ℕ | (n : ℝ) ≤ X ∧ IsAACarmichael a n ∧
            n.primeFactors.gcd (fun p => (p : ℤ) - a) = ν}.ncard : ℝ)


/-- Size of the primes `q ∈ 𝒬ᵢ` in the construction. Let `z` be a natural number and
`J = ∏_{z/2 ≤ r ≤ z, r prime} r`, and let `𝓡_j` be the set of primes `q = g j + 1` with `g ∣ J`
and `ω(g) = ⌊log z⌋`. For every real `A` and all sufficiently large `z`, every `q ∈ 𝓡_j` with
`1 ≤ j ≤ (log z)^{2A}` satisfies `(z/6)^{log z} ≤ q ≤ 2 z^{log z} (log z)^{2A}`.

The paper states the bound for `q ∈ 𝒬ᵢ`, a chosen subset of `𝓡_{j₀}` with `j₀ ≤ (log z)^{2A}`
(`A ≥ 2` the constant of Conjecture 2); the statement here quantifies over every such `j` and
every `q ∈ 𝓡_j`, so it covers every choice of `j₀` and `𝒬ᵢ`, and it allows every real `A`.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 3 (definitions of `J`, `𝓡_j`, `𝒬ᵢ`) and Lemma 1
(`integers-2026-A123-lem-1`). -/
public theorem_wanted rpow_log_le_prime_of_eq_mul_add_one_of_dvd_prod_primes
    (A : ℝ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ j g q : ℕ, 1 ≤ j → (j : ℝ) ≤ Real.log z ^ (2 * A) →
      g ∣ ∏ r ∈ (Finset.Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r →
      g.primeFactors.card = ⌊Real.log z⌋₊ → q.Prime → q = g * j + 1 →
        ((z : ℝ) / 6) ^ Real.log z ≤ q ∧
          (q : ℝ) ≤ 2 * (z : ℝ) ^ Real.log z * Real.log z ^ (2 * A)

/-- The Carmichael function of `L₁L₂` is small. With `J` and `𝓡_j` as in
`rpow_log_le_prime_of_eq_mul_add_one_of_dvd_prod_primes`, for every real `A` and all sufficiently
large `z`, every finite set `S` of primes in `𝓡_j` with `1 ≤ j ≤ (log z)^{2A}` satisfies
`λ(∏_{q ∈ S} q) ≤ e^{4z/5}`.

The paper states this for `L₁L₂ = ∏_{q ∈ 𝒬₁ ∪ 𝒬₂} q` with disjoint chosen subsets
`𝒬₁, 𝒬₂ ⊆ 𝓡_{j₀}`; the statement here covers every finite subset of every such `𝓡_j`, and every
real `A`. `λ` is `ArithmeticFunction.carmichael`.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 3 and Lemma 3 (`integers-2026-A123-lem-3`). -/
public theorem_wanted carmichael_prod_primes_eq_mul_add_one_le_exp
    (A : ℝ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ Real.log z ^ (2 * A) →
      ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ ∃ g : ℕ,
          g ∣ ∏ r ∈ (Finset.Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r ∧
          g.primeFactors.card = ⌊Real.log z⌋₊ ∧ q = g * j + 1) →
        (ArithmeticFunction.carmichael (∏ q ∈ S, q) : ℝ) ≤ Real.exp (4 * z / 5)

end

end MetaMathlibExt
