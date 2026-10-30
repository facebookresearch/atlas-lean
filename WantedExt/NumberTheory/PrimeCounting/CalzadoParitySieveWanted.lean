/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Calzado, a Bombieri–Vinogradov result and the parity problem — wishlist

Statement-only records for the sieve lemmas of Calzado's INTEGERS 26 (2026)
paper that are stated over explicit objects: the Mertens-type sums over primes
in `x^{1/5} < p ≤ x^{1/2}` (Lemma 1), the size of the Euler product `V(z)` of a
sieve of dimension `k` (Lemma 3), and the sifting bounds for the shifted primes
`{p + a : p ≤ x}` with `a` even and nonzero (Lemmas 4 and 6).

For the shifted primes, `S(A, P, z)` is the number of primes `n ≤ x` such that
`n + a` has no prime factor `q < z` (divisibility in `ℤ`), and `S(A_ℓ, P, z)`
adds the condition `ℓ ∣ n + a`. Here `P` is the set of all primes, as in the
paper's Theorem 2.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- Lemma 1, equation (11): `∑_{x^{1/5} < p ≤ x^{1/2}} 1 / φ(p) → log (5/2)`.
The paper prints the limit as `0.916…`; the exact value `log (5/2) = 0.91629…`
is forced by Mertens' theorem.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 1
(`integers-2026-A117-lem-1`). -/
public theorem_wanted calzado_sum_inv_totient_fifth_to_half_tendsto :
    Tendsto (fun x : ℝ =>
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          x ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ ((1 : ℝ) / 2)),
        1 / (Nat.totient p : ℝ))
      atTop (𝓝 (Real.log (5 / 2)))

/-- Lemma 1, equation (12): for fixed `B > 0`,
`∑_{x^{1/2} (log x)^{-B} < p ≤ x^{1/2}} 1 / φ(p) ≪_B log log x / log x`.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 1
(`integers-2026-A117-lem-1`). -/
public theorem_wanted calzado_sum_inv_totient_near_sqrt_isBigO (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          x ^ ((1 : ℝ) / 2) * Real.log x ^ (-B) < (p : ℝ) ∧
            (p : ℝ) ≤ x ^ ((1 : ℝ) / 2)),
        1 / (Nat.totient p : ℝ)
        ≤ C * Real.log (Real.log x) / Real.log x

/-- Lemma 3: if `P` is a set of primes, `0 ≤ ω(p) < p` for `p ∈ P`, and the
sieve has dimension `k`, i.e. `∑_{t ≤ p < z, p ∈ P} ω(p) log p / p =
k log (z / t) + O(1)` uniformly for `2 ≤ t ≤ z`, then
`V(z) = ∏_{p < z, p ∈ P} (1 - ω(p) / p) ≍ (log z)^{-k}` for `z ≥ 2`.
The constants depend on `ω` and `P`, not only on `k`.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 3
(`integers-2026-A117-lem-3`). -/
public theorem_wanted calzado_sieve_euler_product_asymp (P : Set ℕ)
    [DecidablePred (· ∈ P)] (ω : ℕ → ℝ) (k : ℝ) (hk : 0 < k)
    (hP : ∀ p ∈ P, p.Prime ∧ 0 ≤ ω p ∧ ω p < p)
    (hdim : ∃ C₀ : ℝ, ∀ t z : ℝ, 2 ≤ t → t ≤ z →
      |∑ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
          ω p * Real.log p / p - k * Real.log (z / t)| ≤ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      c / Real.log z ^ k ≤
          ∏ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
            (1 - ω p / p) ∧
        ∏ p ∈ (Finset.range (⌈z⌉₊)).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
            (1 - ω p / p) ≤ C / Real.log z ^ k

open Classical in
/-- Lemma 4: for `a` even and nonzero, `A = {n + a : n ≤ x prime}` and
`z = x^{1/5}`, uniformly for primes `x^{1/5} < ℓ ≤ x^{1/2}`,
`S(A_ℓ, P, z) ≪ x / (φ(ℓ) (log x)^2)`, for all sufficiently large `x`; the
constant may depend on `a`.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 4
(`integers-2026-A117-lem-4`). -/
public theorem_wanted calzado_shifted_primes_sifted_multiple_le (a : ℤ) (ha : Even a)
    (ha0 : a ≠ 0) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ ℓ : ℕ, ℓ.Prime →
      x ^ ((1 : ℝ) / 5) < (ℓ : ℝ) → (ℓ : ℝ) ≤ x ^ ((1 : ℝ) / 2) →
      (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ (ℓ : ℤ) ∣ (n : ℤ) + a ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) → ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ)
        ≤ C * x / ((Nat.totient ℓ : ℝ) * Real.log x ^ 2)

open Classical in
/-- Lemma 6, equation (15): for `a` even and nonzero there are constants
`0 < C₁ < C₂` with `C₁ x / (log x)^2 < S(A, P, x^{1/5}) < C₂ x / (log x)^2`
for all sufficiently large `x`, where `A = {n + a : n ≤ x prime}`.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 6
(`integers-2026-A117-lem-6`). -/
public theorem_wanted calzado_shifted_primes_sifted_asymp (a : ℤ) (ha : Even a)
    (ha0 : a ≠ 0) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ < C₂ ∧ ∀ᶠ x : ℝ in atTop,
      C₁ * x / Real.log x ^ 2 <
          (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
            ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
              ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) ∧
        (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
            ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
              ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) < C₂ * x / Real.log x ^ 2

open Classical in
/-- Lemma 6, equation (16), which is condition (7) of Theorem 1 for
`A = {n + a : n ≤ x prime}`: for `a` even and nonzero,
`S(A_ℓ, P, x^{1/5}) ≪ S(A, P, x^{1/5}) / φ(ℓ)` uniformly for primes
`x^{1/5} < ℓ ≤ x^{1/2}`, for all sufficiently large `x`.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 6
(`integers-2026-A117-lem-6`). -/
public theorem_wanted calzado_shifted_primes_sifted_multiple_le_sifted (a : ℤ)
    (ha : Even a) (ha0 : a ≠ 0) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ ℓ : ℕ, ℓ.Prime →
      x ^ ((1 : ℝ) / 5) < (ℓ : ℝ) → (ℓ : ℝ) ≤ x ^ ((1 : ℝ) / 2) →
      (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ (ℓ : ℤ) ∣ (n : ℤ) + a ∧
          ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) → ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ)
        ≤ C * (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
            ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
              ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) / (Nat.totient ℓ : ℝ)

open Classical in
/-- Lemma 2 (Selberg's upper bound sieve, quoted from Heath-Brown): let `A` be a finite sequence
of positive integers, `P` a set of primes, `ω` a non-negative multiplicative function with
`0 ≤ ω(p) < p` for `p ∈ P`, `X > 0`, and `R_d = #A_d - ω(d) X / d`. If the sieve has dimension
`κ > 0`, `∑_{t ≤ p < z, p ∈ P} ω(p) log p / p = κ log (z / t) + O(1)` uniformly for `2 ≤ t ≤ z`,
then `S(A, P, z) ≤ X e^{γκ} Γ(κ + 1) ∏_{p < z, p ∈ P} (1 - ω(p)/p) (1 + O(1 / log z)) +
∑_{d < z², d ∣ P(z)} 3^{ν(d)} |R_d|`, the implied constant depending only on `κ` and the
constant `C₀` of the dimension hypothesis.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 2 (`integers-2026-A117-lem-2`). -/
public theorem_wanted calzado_selberg_upper_bound_sieve (κ C₀ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ (P : Set ℕ) (ω : ArithmeticFunction ℝ) (A : Multiset ℕ) (X z : ℝ),
      (∀ p ∈ P, p.Prime ∧ ω p < p) → ω.IsMultiplicative → (∀ n, 0 ≤ ω n) →
      (∀ n ∈ A, 0 < n) → 0 < X → 2 ≤ z →
      (∀ t : ℝ, 2 ≤ t → t ≤ z →
        |∑ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
            ω p * Real.log p / p - κ * Real.log (z / t)| ≤ C₀) →
      ((A.filter fun n => n.Coprime
          (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z), p)).card : ℝ) ≤
        X * Real.exp (Real.eulerMascheroniConstant * κ) * Real.Gamma (κ + 1) *
            (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
              (1 - ω p / p)) * (1 + C / Real.log z) +
          ∑ d ∈ (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z),
              p).divisors.filter (fun d : ℕ => (d : ℝ) < z ^ 2),
            (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
              |((A.filter (fun n => d ∣ n)).card : ℝ) - ω d / d * X|

open Classical in
/-- Lemma 5 (the Rosser–Iwaniec linear sieve, quoted from Heath-Brown): with the setting of
Lemma 2 and the one-dimensional condition
`∑_{t ≤ ℓ < z, ℓ ∈ P} ω(ℓ) log ℓ / ℓ ≤ log (z / t) + O(1)` uniformly for `2 ≤ t ≤ z`, a level
`y ≥ z` and `s = log y / log z`,
`X V(z) (f(s) - C e^{-s} (log y)^{-1/3}) - ∑_{d < y, d ∣ P(z)} |R_d| ≤ S(A, P, z) ≤
X V(z) (F(s) + C e^{-s} (log y)^{-1/3}) + ∑_{d < y, d ∣ P(z)} |R_d|`, with `C > 0` depending only
on the constant `C₀` of the condition. `F` and `f` are the continuous functions on `(0, ∞)` with
`F(s) = 2e^γ / s` (`0 < s ≤ 3`), `f(s) = 0` (`0 < s ≤ 2`), `(s F(s))' = f(s - 1)` (`s > 3`) and
`(s f(s))' = F(s - 1)` (`s > 2`); in particular `f(s) = 2e^γ log(s - 1) / s` for `2 ≤ s ≤ 4`.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 5 (`integers-2026-A117-lem-5`). -/
public theorem_wanted calzado_linear_sieve (F f : ℝ → ℝ)
    (hFc : ContinuousOn F (Set.Ioi 0)) (hfc : ContinuousOn f (Set.Ioi 0))
    (hF : ∀ s, 0 < s → s ≤ 3 → F s = 2 * Real.exp Real.eulerMascheroniConstant / s)
    (hf : ∀ s, 0 < s → s ≤ 2 → f s = 0)
    (hF' : ∀ s, 3 < s → HasDerivAt (fun u => u * F u) (f (s - 1)) s)
    (hf' : ∀ s, 2 < s → HasDerivAt (fun u => u * f u) (F (s - 1)) s) (C₀ : ℝ) :
    (∀ s, 2 ≤ s → s ≤ 4 → f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Set ℕ) (ω : ArithmeticFunction ℝ) (A : Multiset ℕ) (X z y : ℝ),
      (∀ p ∈ P, p.Prime ∧ ω p < p) → ω.IsMultiplicative → (∀ n, 0 ≤ ω n) →
      (∀ n ∈ A, 0 < n) → 0 < X → 2 ≤ z → z ≤ y →
      (∀ t : ℝ, 2 ≤ t → t ≤ z →
        ∑ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
            ω p * Real.log p / p ≤ Real.log (z / t) + C₀) →
      let Pz := ∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z), p
      let V := ∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < z), (1 - ω p / p)
      let s := Real.log y / Real.log z
      let R := ∑ d ∈ Pz.divisors.filter (fun d : ℕ => (d : ℝ) < y),
        |((A.filter (fun n => d ∣ n)).card : ℝ) - ω d / d * X|
      let S := ((A.filter fun n => n.Coprime Pz).card : ℝ)
      S ≤ X * V * (F s + C * Real.exp (-s) * Real.log y ^ (-(1 : ℝ) / 3)) + R ∧
        X * V * (f s - C * Real.exp (-s) * Real.log y ^ (-(1 : ℝ) / 3)) - R ≤ S

open Classical in
/-- Theorem 2, inequality (9): for `a` even and nonzero there is `C > 0` such that for every
`B > 0` and all sufficiently large `x`, the number of primes `n ≤ x` with `n + a` prime is at least
`C x / (log x)² - ∑_{x^{1/5} < p ≤ x^{1/2} (log x)^{-B}} Δ̄(A_p)`, where
`Δ̄(A_p) = #{n ≤ x prime : n ≡ -a (mod p), f(n + a)} - #{n ≤ x prime : (n, p) = 1, f(n + a)} / φ(p)`
and `f(n + a)` says that `n + a` has no prime factor `q < x^{1/5}` (Equation (10)).

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Theorem 2 (`integers-2026-A117-thm-2`). -/
public theorem_wanted calzado_shifted_primes_prime_count_lower (a : ℤ) (ha : Even a)
    (ha0 : a ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∀ᶠ x : ℝ in atTop,
      C * x / Real.log x ^ 2 -
          ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
              x ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ ((1 : ℝ) / 2) * Real.log x ^ (-B)),
            ((((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
                (n : ℤ) ≡ -a [ZMOD p] ∧ ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
                  ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) -
              (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ n.Coprime p ∧
                ∀ q : ℕ, q.Prime → (q : ℝ) < x ^ ((1 : ℝ) / 5) →
                  ¬ (q : ℤ) ∣ (n : ℤ) + a)).card : ℝ) / (Nat.totient p : ℝ)) ≤
        (((Finset.range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧
          0 < (n : ℤ) + a ∧ Prime ((n : ℤ) + a))).card : ℝ)

end

end MetaMathlibExt
