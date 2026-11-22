/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

namespace MetaMathlibExt

@[expose] public section

/-- An `(a, a)`-Carmichael number: a squarefree natural number `n` such that `p - a ∣ n - a`
for every prime `p ∣ n`, the divisibility taken in `ℤ`.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, abstract and Section 1 (definition read from the arXiv version,
arXiv:2607.02738; the journal display could not be checked). -/
def IsAACarmichael (a : ℤ) (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p ∈ n.primeFactors, ((p : ℤ) - a) ∣ ((n : ℤ) - a)

/-- Every prime is an `(a, a)`-Carmichael number, for every integer `a`.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, characteristic lemma of the definition in Section 1. -/
theorem isAACarmichael_of_prime (a : ℤ) {p : ℕ} (hp : p.Prime) : IsAACarmichael a p := by
  refine ⟨hp.prime.squarefree, fun q hq => ?_⟩
  rw [hp.primeFactors, Finset.mem_singleton] at hq
  subst hq
  exact dvd_rfl

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

/-- The gcd of `p₁ - a` and `p₂ - a` is exactly `ν`. Let `L₁, L₂` be coprime, let `k₁, k₂` be
coprime to each other and to `ν L₁ L₂`, and let `pᵢ = dᵢ kᵢ ν + a` with `dᵢ ∣ Lᵢ`. Then
`gcd(p₁ - a, p₂ - a) = ν`.

In the paper `pᵢ ∈ 𝒫^i_{kᵢ} = {p prime : p = dᵢ kᵢ ν + a, dᵢ ∣ Lᵢ, ω(dᵢ) = z}` with
`Lᵢ = ∏_{q ∈ 𝒬ᵢ} q` for disjoint sets of primes `𝒬₁, 𝒬₂` and `k₁, k₂` from Lemmas 4 and 5; the
statement keeps only the hypotheses the conclusion uses (`(L₁, L₂) = 1`, `(kᵢ, νL₁L₂) = 1`,
`(k₁, k₂) = 1`, `dᵢ ∣ Lᵢ`) and drops primality of `pᵢ` and `ω(dᵢ) = z`.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 5 (definition of `𝒫^i_k`) and Lemma 6
(`integers-2026-A123-lem-6`). -/
public theorem_wanted int_gcd_sub_eq_of_eq_mul_mul_add
    (a : ℤ) (ν L₁ L₂ k₁ k₂ d₁ d₂ : ℕ) (hL : Nat.Coprime L₁ L₂)
    (hk₁ : Nat.Coprime k₁ (ν * L₁ * L₂)) (hk₂ : Nat.Coprime k₂ (ν * L₁ * L₂))
    (hk : Nat.Coprime k₁ k₂) (hd₁ : d₁ ∣ L₁) (hd₂ : d₂ ∣ L₂) (p₁ p₂ : ℤ)
    (hp₁ : p₁ = d₁ * k₁ * ν + a) (hp₂ : p₂ = d₂ * k₂ * ν + a) :
    Int.gcd (p₁ - a) (p₂ - a) = ν

end

end MetaMathlibExt
