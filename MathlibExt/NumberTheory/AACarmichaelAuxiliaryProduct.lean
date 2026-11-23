/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

/-!
# The Carmichael function of a product of auxiliary primes

For auxiliary primes of the form `g * j + 1` in Wright's construction, we bound the
Carmichael function of their product by `exp (4 * z / 5)`.
-/

namespace MetaMathlibExt

open Finset Filter Real

-- At the rounded midpoint a prime can fail to divide the middle binomial coefficient.
-- Multiplying the coefficient by the midpoint accounts for this possible factor.
private theorem prod_primes_half_interval_le {z : ℕ} (hz : 0 < z) :
    ∏ r ∈ (Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r ≤ z * 2 ^ z := by
  let k := z - z / 2
  have hk : 0 < k := by dsimp [k]; omega
  have hkz : k ≤ z := Nat.sub_le _ _
  calc
    _ ≤ k * z.choose k := by
      apply Nat.le_of_dvd (Nat.mul_pos hk (Nat.choose_pos hkz))
      apply prod_primes_dvd _ (fun _ hr => (mem_filter.mp hr).2.1.prime)
      intro r hr
      obtain ⟨hrz, hp, hhalf⟩ := mem_filter.mp hr
      have hz₂ : z ≤ 2 * r := by exact_mod_cast (show (z : ℝ) ≤ 2 * r by linarith)
      have hkr : k ≤ r := by dsimp [k]; omega
      obtain rfl | hlt := hkr.eq_or_lt
      · exact dvd_mul_right _ _
      · have hsub : z - k ≤ k := by dsimp [k]; omega
        exact dvd_mul_of_dvd_right (hp.dvd_choose hlt (hsub.trans_lt hlt) (mem_Iic.mp hrz)) _
    _ ≤ z * 2 ^ z := Nat.mul_le_mul hkz (Nat.choose_le_two_pow _ _)

/-- **The Carmichael function of a product of auxiliary primes is small.** For a natural number
$z$, let $J$ be the product of the primes $r$ with $z/2 \le r \le z$, and write $\omega(g)$ for the
number of distinct prime factors of $g$. For every real $A$ and all sufficiently large natural
numbers $z$ the following holds: for every natural number $j$ with $1 \le j \le (\log z)^{2A}$
and every finite set $S$ of primes such that each $q \in S$ equals $gj + 1$ for some natural
number $g$ with $g \mid J$ and $\omega(g) = \lfloor \log z \rfloor$, the Carmichael function
$\lambda$ satisfies $\lambda\bigl(\prod_{q \in S} q\bigr) \le e^{4z/5}$.

In the paper this is stated for $L_1 L_2$, the product of the primes in two disjoint chosen sets
of such primes for a fixed $j = j_0$; the statement here covers every finite set of such primes,
for every such $j$ and every real $A$.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 3 and Lemma 3 (`integers-2026-A123-lem-3`). -/
public theorem carmichael_prod_primes_eq_mul_add_one_le_exp
    (A : ℝ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ Real.log z ^ (2 * A) →
      ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ ∃ g : ℕ,
          g ∣ ∏ r ∈ (Finset.Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r ∧
          g.primeFactors.card = ⌊Real.log z⌋₊ ∧ q = g * j + 1) →
        (ArithmeticFunction.carmichael (∏ q ∈ S, q) : ℝ) ≤ Real.exp (4 * z / 5) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 * A) zero_lt_one).eventuallyLE
  have hexp := (isLittleO_exp_mul_rpow_of_lt 2
    (show log 2 < 4 / 5 by linarith [log_two_lt_d9])).eventuallyLE
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlog,
    tendsto_natCast_atTop_atTop.eventually hexp, eventually_gt_atTop 0] with z hlog hexp hz
  intro j hj hjz S hS
  let J := ∏ r ∈ (Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r
  have hJ : 0 < J := prod_pos fun _ hr => (mem_filter.mp hr).2.1.pos
  have hdvd : ArithmeticFunction.carmichael (∏ q ∈ S, q) ∣ J * j := by
    rw [ArithmeticFunction.carmichael_finsetProd (fun p hp q hq hpq =>
      (Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq)]
    apply Finset.lcm_dvd
    intro q hq
    obtain ⟨hp, g, hg, _, heq⟩ := hS q hq
    change ArithmeticFunction.carmichael q ∣ J * j
    rw [ArithmeticFunction.carmichael_of_prime hp, heq, Nat.add_sub_cancel]
    exact Nat.mul_dvd_mul_right hg j
  have hj_le : (j : ℝ) ≤ z := hjz.trans <| (le_abs_self _).trans <| by
    simpa only [rpow_one, Real.norm_eq_abs, Nat.abs_cast] using hlog
  have hpow : (2 : ℝ) ^ z = exp (log 2 * z) := by
    rw [mul_comm, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    (ArithmeticFunction.carmichael (∏ q ∈ S, q) : ℝ) ≤ (J : ℝ) * j := by
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hJ hj) hdvd
    _ ≤ ((z : ℝ) * 2 ^ z) * z := by
      gcongr
      exact_mod_cast prod_primes_half_interval_le hz
    _ = exp (log 2 * z) * (z : ℝ) ^ 2 := by rw [hpow]; ring
    _ ≤ exp (4 * z / 5) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg, exp_pos, Real.rpow_two, mul_div_right_comm]
        using hexp

end MetaMathlibExt
