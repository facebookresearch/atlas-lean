/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.BinomialOptimalStopping
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# No early exercise for an American call on a binomial tree

On the binomial tree of `MathlibExt.Economics.Finance.BinomialOptimalStopping`,
take a non-dividend stock with price `S₀ u^(#up) d^(#down)` at a node, a
risk-neutral probability `p ∈ [0, 1]` with `p u + (1 - p) d = R`, gross interest
`R ≥ 1` (nonnegative interest) and discount `R⁻¹`, and a call with strike
`K ≥ 0`.

The European call value dominates the immediate exercise value at every node
(`callPayoff_le_european`): by convexity of `max (· - K) 0` and the martingale
condition, the discounted continuation is at least `R⁻¹ (R S - K)⁺ ≥ (S - K)⁺`.
Hence the Snell envelope recursion never prefers exercise and the American call
value equals the European value at every node and horizon
(`snell_call_eq_european`). The interest condition cannot be dropped: with a
negative rate, early exercise can be strictly optimal (see the tests).

## Main results

* `MathlibExt.Economics.Finance.BinomialOptimalStopping.callPayoff_le_european`
* `MathlibExt.Economics.Finance.BinomialOptimalStopping.snell_call_eq_european`

## References

* R. C. Merton, "Theory of Rational Option Pricing", Bell Journal of Economics
  and Management Science 4 (1973), 141–183.
* S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing
  Model*, Springer (2004), Chapter 4.

Atlas roadmap target FI12.T05.
-/

namespace MathlibExt.Economics.Finance.BinomialOptimalStopping

/-- Stock price at node `s` of a binomial tree with initial price `S₀`, up factor
`u` and down factor `d`: `S₀ u^(number of up moves) d^(number of down moves)`. -/
def stockPrice (S₀ u d : ℝ) (s : List Bool) : ℝ :=
  S₀ * u ^ s.count true * d ^ s.count false

/-- Exercise payoff of a call with strike `K` on the binomial stock. -/
noncomputable def callPayoff (S₀ u d K : ℝ) (s : List Bool) : ℝ :=
  max (stockPrice S₀ u d s - K) 0

/-- The European rule: never exercise before the horizon. -/
def europeanRule : ℕ → List Bool → Bool :=
  fun _ _ => false

theorem stockPrice_up (S₀ u d : ℝ) (s : List Bool) :
    stockPrice S₀ u d (true :: s) = stockPrice S₀ u d s * u := by
  have hc1 : (true :: s).count true = s.count true + 1 := List.count_cons_self
  have hc2 : (true :: s).count false = s.count false :=
    List.count_cons_of_ne (by decide)
  unfold stockPrice
  rw [hc1, hc2, pow_succ]
  ring

theorem stockPrice_down (S₀ u d : ℝ) (s : List Bool) :
    stockPrice S₀ u d (false :: s) = stockPrice S₀ u d s * d := by
  have hc1 : (false :: s).count true = s.count true :=
    List.count_cons_of_ne (by decide)
  have hc2 : (false :: s).count false = s.count false + 1 := List.count_cons_self
  unfold stockPrice
  rw [hc1, hc2, pow_succ]
  ring

private theorem max_mix_le {p a b : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    max (p * a + (1 - p) * b) 0 ≤ p * max a 0 + (1 - p) * max b 0 := by
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
  have hnn : 0 ≤ p * max a 0 + (1 - p) * max b 0 :=
    add_nonneg (mul_nonneg hp₀ (le_max_right _ _)) (mul_nonneg h1p (le_max_right _ _))
  rcases le_total (p * a + (1 - p) * b) 0 with h | h
  · rw [max_eq_right h]
    exact hnn
  · rw [max_eq_left h]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hp₀)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) h1p)

private theorem discount_call_le {S K R : ℝ} (hR : 1 ≤ R) (hK : 0 ≤ K) :
    max (S - K) 0 ≤ R⁻¹ * max (R * S - K) 0 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hdisc : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  rcases le_total S K with h | h
  · rw [max_eq_right (sub_nonpos.mpr h)]
    exact mul_nonneg hdisc (le_max_right _ _)
  · have hS0 : 0 ≤ S := le_trans hK h
    have hRS : S ≤ R * S := le_mul_of_one_le_left hS0 hR
    have h0a : (0:ℝ) ≤ S - K := sub_nonneg.mpr h
    have h0b : (0:ℝ) ≤ R * S - K := le_trans h0a (sub_le_sub_right hRS K)
    rw [max_eq_left h0a, max_eq_left h0b]
    have hRne : R ≠ 0 := ne_of_gt hRpos
    have hKR : K * R⁻¹ ≤ K := by
      have hinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
      calc K * R⁻¹ ≤ K * 1 := mul_le_mul_of_nonneg_left hinv hK
        _ = K := mul_one K
    have heq : R⁻¹ * (R * S - K) = S - K * R⁻¹ := by
      have h1 : R⁻¹ * (R * S) = S := by
        rw [← mul_assoc, inv_mul_cancel₀ hRne, one_mul]
      calc R⁻¹ * (R * S - K) = R⁻¹ * (R * S) - R⁻¹ * K := mul_sub _ _ _
        _ = S - K * R⁻¹ := by rw [h1, mul_comm R⁻¹ K]
    rw [heq]
    exact sub_le_sub_left hKR S

/-- Under the risk-neutral (martingale) condition `p u + (1 - p) d = R` with gross
interest rate `R ≥ 1`, discount factor `R⁻¹`, and strike `K ≥ 0`, the European
call value with `k` periods left is at least the immediate exercise value. -/
theorem callPayoff_le_european {S₀ u d K p R : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hR : 1 ≤ R) (hmart : p * u + (1 - p) * d = R) (hK : 0 ≤ K) (k : ℕ) (s : List Bool) :
    callPayoff S₀ u d K s ≤ ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k s := by
  induction k generalizing s with
  | zero => simp only [ruleValue, le_refl]
  | succ k ih =>
    have hcont : ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule (k + 1) s =
        continuation p R⁻¹ (ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k) s := by
      simp [ruleValue, europeanRule]
    rw [hcont]
    set S := stockPrice S₀ u d s with hS
    have hUp : stockPrice S₀ u d (true :: s) = S * u := by
      rw [stockPrice_up, hS]
    have hDown : stockPrice S₀ u d (false :: s) = S * d := by
      rw [stockPrice_down, hS]
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hdisc : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
    have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
    have hmono : R⁻¹ * (p * max (S * u - K) 0 + (1 - p) * max (S * d - K) 0) ≤
        continuation p R⁻¹ (ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k) s := by
      unfold continuation
      apply mul_le_mul_of_nonneg_left _ hdisc
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hp₀
        have h := ih (true :: s)
        simpa only [callPayoff, hUp] using h
      · apply mul_le_mul_of_nonneg_left _ h1p
        have h := ih (false :: s)
        simpa only [callPayoff, hDown] using h
    have hmartS : p * (S * u - K) + (1 - p) * (S * d - K) = R * S - K := by
      linear_combination S * hmart
    have hconv : max (R * S - K) 0 ≤
        p * max (S * u - K) 0 + (1 - p) * max (S * d - K) 0 := by
      rw [← hmartS]
      exact max_mix_le hp₀ hp₁
    have hdisc2 : max (S - K) 0 ≤ R⁻¹ * max (R * S - K) 0 :=
      discount_call_le hR hK
    have hpay : callPayoff S₀ u d K s = max (S - K) 0 := by
      simp only [callPayoff, hS]
    rw [hpay]
    calc max (S - K) 0 ≤ R⁻¹ * max (R * S - K) 0 := hdisc2
      _ ≤ R⁻¹ * (p * max (S * u - K) 0 + (1 - p) * max (S * d - K) 0) :=
          mul_le_mul_of_nonneg_left hconv hdisc
      _ ≤ continuation p R⁻¹ (ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k) s :=
          hmono

/-- No early exercise for an American call on a non-dividend binomial stock: with
nonnegative interest (`R ≥ 1`), the American value (Snell envelope) equals the
European value at every node and horizon. -/
theorem snell_call_eq_european {S₀ u d K p R : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hR : 1 ≤ R) (hmart : p * u + (1 - p) * d = R) (hK : 0 ≤ K) (k : ℕ) (s : List Bool) :
    snell p R⁻¹ (callPayoff S₀ u d K) k s =
      ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k s := by
  induction k generalizing s with
  | zero => simp only [snell, ruleValue]
  | succ k ih =>
    have hfun : snell p R⁻¹ (callPayoff S₀ u d K) k =
        ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k := funext ih
    have hcont : ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule (k + 1) s =
        continuation p R⁻¹ (ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k) s := by
      simp [ruleValue, europeanRule]
    have hle : callPayoff S₀ u d K s ≤
        continuation p R⁻¹ (ruleValue p R⁻¹ (callPayoff S₀ u d K) europeanRule k) s := by
      have h := @callPayoff_le_european S₀ u d K p R hp₀ hp₁ hR hmart hK (k + 1) s
      rwa [hcont] at h
    simp only [snell]
    rw [hfun, hcont, max_eq_right hle]

end MathlibExt.Economics.Finance.BinomialOptimalStopping
