/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.NearPerfectPowerTwoDivisibility
public import MathlibExt.NumberTheory.StrongTwoNearPerfectExponentBound
public import MathlibExt.NumberTheory.TwoNearPerfectEquationSeven
public import MathlibExt.NumberTheory.TwoNearPerfectEquationSix
public import MathlibExt.NumberTheory.TwoNearPerfectOddDivisor
public import MathlibExt.NumberTheory.TwoNearPerfectOmittedDivisors
public import MathlibExt.NumberTheory.TwoNearPerfectPowerOfTwoDivisors
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Classification of prime solutions of `p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1`

This module proves `strong_two_near_perfect_two_pow_mul_prime_classification`.

Statements from Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua
Zelinsky, *On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305).
Labels follow the journal numbering; the arXiv version numbers Lemmas 1-10 as Lemmas 3-7,
10, 11, 14, 15, 17 and Propositions 1-5 as Propositions 8, 9, 12, 13, 16.

A number `n` is `2`-near perfect with omitted divisors `d₁ ≠ d₂` when `d₁, d₂ ∣ n` and
`σ(n) = 2n + d₁ + d₂`. It is strongly `2`-near perfect when it has a divisor `d` with
`σ(n) = 2n + d + n / d` (the paper's equivalent form of the definition); for `n = 2^k p`
with `p` odd, `d ≠ n / d` holds automatically. Exponents flattened in the extracted
statements (`2k+1`, `pk`) are read as powers, as in the paper.
-/

namespace MetaMathlibExt

/-- **Classification of prime solutions of $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$.** Let $a \le k$
be natural numbers and let $p$ be a prime with $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$, that is,
$p = (2^{k+1} - 2^a - 1)/(1 + 2^{k-a})$. Then $k = a + 2$, $2^k p / 2^a = 4p$,
$5p = 2^{a+3} - 2^a - 1$, and $a \equiv 3 \pmod 4$.

The source states this for $n = 2^k p$ strongly $2$-near perfect, that is, with
$\sigma(n) = 2n + d + n/d$ for some divisor $d$ of $n$, where $\sigma$ is the sum of divisors.
That hypothesis follows from the equation for $p$ by taking $d = 2^a$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 5
(`integers-2024-A61-prop-5`). -/
public theorem strong_two_near_perfect_two_pow_mul_prime_classification {a k p : ℕ}
    (hp : p.Prime) (hak : a ≤ k)
    (hform : (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1) :
    k = a + 2 ∧ 2 ^ k * p / 2 ^ a = 4 * p ∧ (5 * p : ℤ) = 2 ^ (a + 3) - 2 ^ a - 1 ∧
      a % 4 = 3 := by
  have hb0 : k - a ≠ 0 := by
    intro h0
    have hka : k = a := by omega
    rw [hka, Nat.sub_self, pow_zero] at hform
    have hpow1 : (2 : ℤ) ^ (a + 1) = 2 * 2 ^ a := pow_succ' _ _
    rw [hpow1] at hform
    have h2a : (2 : ℤ) ^ a = 2 * (p : ℤ) + 1 := by linear_combination -hform
    by_cases ha0 : a = 0
    · subst ha0
      norm_num at h2a
      have hp0 : (p : ℤ) = 0 := by omega
      exact hp.ne_zero (by exact_mod_cast hp0)
    · have ha1 : 1 ≤ a := by omega
      obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      subst ha'
      rw [pow_succ] at h2a
      omega
  have hkdvd : (2 ^ (k - a) + 1 : ℕ) ∣ 3 * 2 ^ a + 1 := by
    have hpowk : (2 : ℤ) ^ (k + 1) = (2 : ℤ) ^ (a + 1) * (2 : ℤ) ^ (k - a) := by
      rw [show k + 1 = (a + 1) + (k - a) by omega, pow_add]
    have hpow2 : (2 : ℤ) ^ (a + 1) = 2 * (2 : ℤ) ^ a := pow_succ' _ _
    rw [hpowk, hpow2] at hform
    have hzdvd : ((2 : ℤ) ^ (k - a) + 1) ∣ 3 * 2 ^ a + 1 := by
      refine ⟨(2 : ℤ) ^ (a + 1) - (p : ℤ), ?_⟩
      rw [hpow2]
      linear_combination hform
    have hcast : ((2 ^ (k - a) + 1 : ℕ) : ℤ) = (2 : ℤ) ^ (k - a) + 1 := by
      push_cast; ring
    have hcast2 : ((3 * 2 ^ a + 1 : ℕ) : ℤ) = 3 * (2 : ℤ) ^ a + 1 := by
      push_cast; ring
    rw [← hcast, ← hcast2] at hzdvd
    exact Int.ofNat_dvd.mp hzdvd
  have hkb : k - a = 2 := eq_two_of_two_pow_add_one_dvd (by omega) hkdvd
  have hk2 : k = a + 2 := by omega
  subst hk2
  have hdiv : 2 ^ (a + 2) * p / 2 ^ a = 4 * p := by
    have h2a : (2 : ℕ) ^ (a + 2) = 2 ^ a * 4 := by ring
    rw [h2a, show 2 ^ a * 4 * p = 2 ^ a * (4 * p) by ring,
      Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)]
  have h5 : (5 : ℤ) * (p : ℤ) = (2 : ℤ) ^ (a + 3) - 2 ^ a - 1 := by
    rw [show a + 2 - a = 2 by omega, show a + 2 + 1 = a + 3 by omega] at hform
    linear_combination hform
  have hmod : (2 : ZMod 5) ^ (a + 1) = 1 := by
    have h5mod : (5 : ZMod 5) * (p : ZMod 5) =
        (2 : ZMod 5) ^ (a + 3) - (2 : ZMod 5) ^ a - 1 := by
      have h5' := congrArg (Int.cast : ℤ → ZMod 5) h5
      simpa using h5'
    have h50 : (5 : ZMod 5) = 0 := by decide
    rw [h50, zero_mul] at h5mod
    have hsplit : (2 : ZMod 5) ^ (a + 3) = 8 * (2 : ZMod 5) ^ a := by ring
    rw [hsplit] at h5mod
    have h7 : (7 : ZMod 5) * (2 : ZMod 5) ^ a = 1 := by linear_combination -h5mod
    have h72 : (7 : ZMod 5) = 2 := by decide
    rw [h72] at h7
    have hpow : (2 : ZMod 5) ^ (a + 1) = 2 * (2 : ZMod 5) ^ a := by ring
    rw [hpow]
    exact h7
  have hord : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm1 hm2 => ?_⟩
    interval_cases m <;> decide
  have hdvd4 : 4 ∣ a + 1 := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hmod
  have ha4 : a % 4 = 3 := by omega
  exact ⟨rfl, hdiv, by simpa using h5, ha4⟩

end MetaMathlibExt
