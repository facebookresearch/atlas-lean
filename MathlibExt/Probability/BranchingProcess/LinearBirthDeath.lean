/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The linear birth–death process

In the linear (simple) birth–death process every individual independently gives birth at rate
`b` and dies at rate `d` (`0 ≤ b`, `0 ≤ d`, time `t ≥ 0` in the units of the rates). Started
from one individual, the population size `X t` has the law found by Kendall (1948):
`P(X t = 0) = α t` and `P(X t = n) = (1 - α t) (1 - β t) (β t) ^ (n - 1)` for `n ≥ 1`, where,
with `E = exp ((b - d) t)`,

* `α t = d (E - 1) / (b E - d)` and `β t = b (E - 1) / (b E - d)` if `b ≠ d`,
* `α t = β t = b t / (1 + b t)` if `b = d`.

Multiplying numerator and denominator by `exp (-(b - d) t)` gives the equivalent form
`α t = d (1 - exp (-(b - d) t)) / (b - d exp (-(b - d) t))`.

This file defines these probabilities and proves that they are the solution of the Kolmogorov
equations of the process, together with the mean and the extinction probability.

## Main definitions

* `extinctionProb b d t`: `α t = P(X t = 0 | X 0 = 1)`.
* `geomRatio b d t`: `β t`, the ratio of the geometric tail of the law of `X t`.
* `prob b d t n`: Kendall's `P(X t = n | X 0 = 1)`.

## Main results

* `prob_zero_time`, `hasDerivAt_prob_zero`, `hasDerivAt_prob_succ`: `prob b d · n` starts from
  `δ₁` and solves the forward Kolmogorov equations
  `p_n' = b (n - 1) p_(n-1) - (b + d) n p_n + d (n + 1) p_(n+1)`.
* `prob_nonneg`, `hasSum_prob`: it is a probability distribution on `ℕ` for every `t ≥ 0`.
* `hasSum_mul_prob`: the mean is `E[X t] = exp ((b - d) t)`.
* `hasDerivAt_extinctionProb`, `eq_extinctionProb_of_hasDerivWithinAt`: `α` solves the backward
  equation `q' = d - (b + d) q + b q²`, `q 0 = 0`, and is its only solution with values in
  `[0, 1]`.
* `tendsto_extinctionProb_of_lt`, `tendsto_extinctionProb_of_le`: as `t → ∞`, `α t → d / b` if
  `d < b`, and `α t → 1` if `b ≤ d` and `0 < d`. (With `b = d = 0` nothing happens and
  `α t = 0`.)

## Scope

We do not construct the Markov chain on `ℕ` with these rates. The forward equations together with
`p (0) = δ₁` determine its transition probabilities from state `1` (the linear process does not
explode), but that uniqueness is not proved here; the extinction probability is characterized
intrinsically as the unique `[0, 1]`-valued solution of the backward equation.

## References

* D. G. Kendall, *On the generalized "birth-and-death" process*, Ann. Math. Statist. 19 (1948),
  1–15.
* N. T. J. Bailey, *The Elements of Stochastic Processes with Applications to the Natural
  Sciences*, Wiley (1964), ch. 8.
* S. Karlin, H. M. Taylor, *A First Course in Stochastic Processes*, 2nd ed., Academic Press
  (1975), ch. 4.
-/

@[expose] public section

open Real Filter Topology Set

namespace MathlibExt.Probability.LinearBirthDeath

/-- Kendall's extinction probability `α t = P(X t = 0 | X 0 = 1)` of the linear birth–death
process with per-capita birth rate `b` and death rate `d`: `d (E - 1) / (b E - d)` with
`E = exp ((b - d) t)` if `b ≠ d`, and `b t / (1 + b t)` if `b = d`. Meaningful for `0 ≤ b`,
`0 ≤ d`, `0 ≤ t`. -/
noncomputable def extinctionProb (b d t : ℝ) : ℝ :=
  if b = d then b * t / (1 + b * t)
  else d * (exp ((b - d) * t) - 1) / (b * exp ((b - d) * t) - d)

/-- Kendall's ratio `β t` of the geometric tail of the law of `X t`: `b (E - 1) / (b E - d)`
with `E = exp ((b - d) t)` if `b ≠ d`, and `b t / (1 + b t)` if `b = d`. -/
noncomputable def geomRatio (b d t : ℝ) : ℝ :=
  if b = d then b * t / (1 + b * t)
  else b * (exp ((b - d) * t) - 1) / (b * exp ((b - d) * t) - d)

/-- Kendall's law of the linear birth–death process at time `t` started from one individual:
`prob b d t 0 = α t` and `prob b d t (n + 1) = (1 - α t) (1 - β t) (β t) ^ n`. -/
noncomputable def prob (b d t : ℝ) : ℕ → ℝ
  | 0 => extinctionProb b d t
  | n + 1 => (1 - extinctionProb b d t) * (1 - geomRatio b d t) * geomRatio b d t ^ n

/-- The denominator `b E - d` of the `b ≠ d` case has the sign of `b - d`. -/
private lemma denom_pos {b d t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (h : d < b) :
    0 < b * exp ((b - d) * t) - d := by
  have : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) ht)
  nlinarith

private lemma denom_neg {b d t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (h : b < d) :
    b * exp ((b - d) * t) - d < 0 := by
  have : exp ((b - d) * t) ≤ 1 :=
    exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht)
  nlinarith

private lemma denom_ne {b d t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (h : b ≠ d) :
    b * exp ((b - d) * t) - d ≠ 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · exact (denom_neg hb ht h).ne
  · exact (denom_pos hb ht h).ne'

private lemma one_sub_extinctionProb_of_ne {b d t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (h : b ≠ d) : 1 - extinctionProb b d t
      = (b - d) * exp ((b - d) * t) / (b * exp ((b - d) * t) - d) := by
  have := denom_ne hb ht h
  simp only [extinctionProb, h, ↓reduceIte]
  field_simp
  ring

private lemma one_sub_geomRatio_of_ne {b d t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (h : b ≠ d) : 1 - geomRatio b d t = (b - d) / (b * exp ((b - d) * t) - d) := by
  have := denom_ne hb ht h
  simp only [geomRatio, h, ↓reduceIte]
  field_simp
  ring

/-- `0 ≤ α t`. -/
private lemma extinctionProb_nonneg {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    0 ≤ extinctionProb b d t := by
  unfold extinctionProb
  split_ifs with h
  · positivity
  · rcases lt_or_gt_of_ne h with h | h
    · have : exp ((b - d) * t) ≤ 1 :=
        exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht)
      exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hd (by linarith))
        (denom_neg hb ht h).le
    · have : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) ht)
      exact div_nonneg (mul_nonneg hd (by linarith)) (denom_pos hb ht h).le

/-- `0 ≤ β t`. -/
private lemma geomRatio_nonneg {b d t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    0 ≤ geomRatio b d t := by
  unfold geomRatio
  split_ifs with h
  · positivity
  · rcases lt_or_gt_of_ne h with h | h
    · have : exp ((b - d) * t) ≤ 1 :=
        exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht)
      exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hb (by linarith))
        (denom_neg hb ht h).le
    · have : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) ht)
      exact div_nonneg (mul_nonneg hb (by linarith)) (denom_pos hb ht h).le

/-- `0 < 1 - α t`. -/
private lemma one_sub_extinctionProb_pos {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    0 < 1 - extinctionProb b d t := by
  by_cases h : b = d
  · subst h
    simp only [extinctionProb, ↓reduceIte]
    have : 0 < 1 + b * t := by positivity
    rw [sub_pos, div_lt_one this]
    linarith
  · rw [one_sub_extinctionProb_of_ne hb ht h]
    rcases lt_or_gt_of_ne h with h | h
    · exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) (exp_pos _))
        (denom_neg hb ht h)
    · exact div_pos (mul_pos (by linarith) (exp_pos _)) (denom_pos hb ht h)

/-- `0 < 1 - β t`. -/
private lemma one_sub_geomRatio_pos {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    0 < 1 - geomRatio b d t := by
  by_cases h : b = d
  · subst h
    simp only [geomRatio, ↓reduceIte]
    have : 0 < 1 + b * t := by positivity
    rw [sub_pos, div_lt_one this]
    linarith
  · rw [one_sub_geomRatio_of_ne hb ht h]
    rcases lt_or_gt_of_ne h with h | h
    · exact div_pos_of_neg_of_neg (by linarith) (denom_neg hb ht h)
    · exact div_pos (by linarith) (denom_pos hb ht h)

/-- `(1 - α t) / (1 - β t) = exp ((b - d) t)`. -/
private lemma one_sub_extinctionProb_div {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    (1 - extinctionProb b d t) / (1 - geomRatio b d t) = exp ((b - d) * t) := by
  by_cases h : b = d
  · subst h
    have : (1 : ℝ) - b * t / (1 + b * t) ≠ 0 := by
      have : 0 < 1 + b * t := by positivity
      rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq this.ne']
      linarith
    simp only [extinctionProb, geomRatio, ↓reduceIte, sub_self, zero_mul, exp_zero]
    exact div_self this
  · rw [one_sub_extinctionProb_of_ne hb ht h, one_sub_geomRatio_of_ne hb ht h]
    have := denom_ne hb ht h
    have : b - d ≠ 0 := sub_ne_zero.2 h
    field_simp

/-- `α t ≤ 1`. -/
private lemma extinctionProb_le_one {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    extinctionProb b d t ≤ 1 := by
  linarith [one_sub_extinctionProb_pos hb hd ht]

/-- At time `0` the population is one individual: `prob b d 0 = δ₁`. -/
theorem prob_zero_time (b d : ℝ) (n : ℕ) : prob b d 0 n = if n = 1 then 1 else 0 := by
  rcases n with _ | _ | n <;> simp [prob, extinctionProb, geomRatio]

/-- Kendall's probabilities are nonnegative. -/
theorem prob_nonneg {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ prob b d t n := by
  rcases n with _ | n
  · exact extinctionProb_nonneg hb hd ht
  · exact mul_nonneg (mul_nonneg (one_sub_extinctionProb_pos hb hd ht).le
      (one_sub_geomRatio_pos hb hd ht).le) (pow_nonneg (geomRatio_nonneg hb ht) n)

/-- Kendall's probabilities sum to `1`: no mass escapes to infinity. -/
theorem hasSum_prob {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    HasSum (prob b d t) 1 := by
  have h1 := one_sub_geomRatio_pos hb hd ht
  have hg := (hasSum_geometric_of_lt_one (geomRatio_nonneg (d := d) hb ht)
    (by linarith)).mul_left ((1 - extinctionProb b d t) * (1 - geomRatio b d t))
  refine (hasSum_nat_add_iff' 1).1 ?_
  convert hg using 1
  · rfl
  · rw [mul_assoc, mul_inv_cancel₀ h1.ne', mul_one, Finset.sum_range_one]
    rfl

/-- The mean population size at time `t` started from one individual is
`E[X t] = exp ((b - d) t)` (Kendall 1948; Bailey 1964, ch. 8). -/
theorem hasSum_mul_prob {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    HasSum (fun n : ℕ ↦ (n : ℝ) * prob b d t n) (exp ((b - d) * t)) := by
  have h1 := one_sub_geomRatio_pos hb hd ht
  have h0 := geomRatio_nonneg (d := d) hb ht
  have hn : ‖geomRatio b d t‖ < 1 := by rw [Real.norm_of_nonneg h0]; linarith
  have hg := ((hasSum_coe_mul_geometric_of_norm_lt_one hn).add
    (hasSum_geometric_of_lt_one h0 (by linarith))).mul_left
    ((1 - extinctionProb b d t) * (1 - geomRatio b d t))
  refine (hasSum_nat_add_iff' 1).1 ?_
  rw [← one_sub_extinctionProb_div hb hd ht]
  convert hg using 1
  · funext n
    simp [prob]
    ring
  · simp [prob]
    field_simp
    ring

/-- `b α t = d β t`. -/
private lemma mul_extinctionProb (b d t : ℝ) : b * extinctionProb b d t = d * geomRatio b d t := by
  unfold extinctionProb geomRatio
  split_ifs with h
  · rw [h]
  · ring

/-- The derivative of `E = exp ((b - d) t)`. -/
private lemma hasDerivAt_growth (b d t : ℝ) :
    HasDerivAt (fun s ↦ exp ((b - d) * s)) ((b - d) * exp ((b - d) * t)) t := by
  simpa [mul_comm] using ((hasDerivAt_id t).const_mul (b - d)).exp

/-- `α' = d (1 - α) (1 - β)`. -/
private lemma hasDerivAt_extinctionProb' {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    HasDerivAt (extinctionProb b d)
      (d * (1 - extinctionProb b d t) * (1 - geomRatio b d t)) t := by
  by_cases h : b = d
  · subst h
    have h1 : 0 < 1 + b * t := by positivity
    have hf : extinctionProb b b = fun s ↦ b * s / (1 + b * s) := by
      funext s
      simp only [extinctionProb, ↓reduceIte]
    rw [hf]
    have := ((hasDerivAt_id t).const_mul b).div (((hasDerivAt_id t).const_mul b).const_add 1)
      h1.ne'
    convert this using 1
    · ext s
      simp [div_eq_mul_inv]
    · simp only [geomRatio, ↓reduceIte, id]
      field_simp
      ring
  · have hD := denom_ne hb ht h
    have hf : extinctionProb b d
        = fun s ↦ d * (exp ((b - d) * s) - 1) / (b * exp ((b - d) * s) - d) := by
      funext s
      simp [extinctionProb, h]
    rw [hf]
    have := (((hasDerivAt_growth b d t).sub_const 1).const_mul d).div
      (((hasDerivAt_growth b d t).const_mul b).sub_const d) hD
    convert this using 1
    rw [← hf, one_sub_extinctionProb_of_ne hb ht h, one_sub_geomRatio_of_ne hb ht h]
    field_simp
    ring

/-- `β' = b (1 - α) (1 - β)`. -/
private lemma hasDerivAt_geomRatio {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    HasDerivAt (geomRatio b d)
      (b * (1 - extinctionProb b d t) * (1 - geomRatio b d t)) t := by
  by_cases h : b = d
  · subst h
    have hg : geomRatio b b = extinctionProb b b := by
      funext s
      simp [geomRatio, extinctionProb]
    rw [hg]
    simpa [hg] using hasDerivAt_extinctionProb' hb hd ht
  · have hD := denom_ne hb ht h
    have hf : geomRatio b d
        = fun s ↦ b * (exp ((b - d) * s) - 1) / (b * exp ((b - d) * s) - d) := by
      funext s
      simp [geomRatio, h]
    rw [hf]
    have := (((hasDerivAt_growth b d t).sub_const 1).const_mul b).div
      (((hasDerivAt_growth b d t).const_mul b).sub_const d) hD
    convert this using 1
    rw [← hf, one_sub_extinctionProb_of_ne hb ht h, one_sub_geomRatio_of_ne hb ht h]
    field_simp
    ring

/-- Forward Kolmogorov equation for state `0`: `p_0' = d p_1`. -/
theorem hasDerivAt_prob_zero {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    HasDerivAt (fun s ↦ prob b d s 0) (d * prob b d t 1) t := by
  have := hasDerivAt_extinctionProb' hb hd ht
  simp only [prob, pow_zero, mul_one]
  convert this using 1
  ring

/-- Forward Kolmogorov equation for state `n + 1`:
`p_(n+1)' = b n p_n - (b + d) (n + 1) p_(n+1) + d (n + 2) p_(n+2)`. -/
theorem hasDerivAt_prob_succ {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) (n : ℕ) :
    HasDerivAt (fun s ↦ prob b d s (n + 1))
      (b * n * prob b d t n - (b + d) * (n + 1) * prob b d t (n + 1)
        + d * (n + 2) * prob b d t (n + 2)) t := by
  have hα := hasDerivAt_extinctionProb' hb hd ht
  have hβ := hasDerivAt_geomRatio hb hd ht
  have key := mul_extinctionProb b d t
  have := ((hα.const_sub 1).mul (hβ.const_sub 1)).mul (hβ.pow n)
  simp only [prob]
  convert this using 1
  set α := extinctionProb b d t
  set β := geomRatio b d t
  simp only [Pi.mul_apply, Pi.pow_apply]
  rcases n with _ | n
  · simp only [Nat.cast_zero, mul_zero, zero_mul, zero_sub, pow_zero, mul_one]
    linear_combination (-(1 - α) * (1 - β)) * key
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    linear_combination ((1 - α) * (1 - β) * β ^ n * ((n + 1) * (1 - β) - β)) * key

/-- Backward Kolmogorov equation for the extinction probability:
`α' = d - (b + d) α + b α²` (Karlin–Taylor 1975, ch. 4). -/
theorem hasDerivAt_extinctionProb {b d t : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    HasDerivAt (extinctionProb b d)
      (d - (b + d) * extinctionProb b d t + b * extinctionProb b d t ^ 2) t := by
  convert hasDerivAt_extinctionProb' hb hd ht using 1
  linear_combination (-(1 - extinctionProb b d t)) * mul_extinctionProb b d t

/-- The extinction probability is the only `[0, 1]`-valued solution `q` on `[0, ∞)` of the
backward equation `q' = d - (b + d) q + b q²` with `q 0 = 0`. -/
theorem eq_extinctionProb_of_hasDerivWithinAt {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) {q : ℝ → ℝ}
    (hc : ContinuousOn q (Ici 0))
    (hq : ∀ t, 0 ≤ t → HasDerivWithinAt q (d - (b + d) * q t + b * q t ^ 2) (Ici t) t)
    (hq01 : ∀ t, 0 ≤ t → q t ∈ Icc 0 1) (hq0 : q 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    q t = extinctionProb b d t := by
  set K : NNReal := ⟨3 * b + d, by positivity⟩
  have hv : ∀ s ∈ Ico (0 : ℝ) t,
      LipschitzOnWith K (fun x : ℝ ↦ d - (b + d) * x + b * x ^ 2) (Icc 0 1) := by
    intro _ _
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [Real.dist_eq, Real.dist_eq]
    have h : d - (b + d) * x + b * x ^ 2 - (d - (b + d) * y + b * y ^ 2)
        = (b * (x + y) - (b + d)) * (x - y) := by ring
    rw [h, abs_mul]
    gcongr
    change |b * (x + y) - (b + d)| ≤ 3 * b + d
    rw [abs_le]
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hα : ContinuousOn (extinctionProb b d) (Icc 0 t) := fun s hs ↦
    (hasDerivAt_extinctionProb hb hd hs.1).continuousAt.continuousWithinAt
  have := ODE_solution_unique_of_mem_Icc_right (v := fun _ x ↦ d - (b + d) * x + b * x ^ 2)
    (s := fun _ ↦ Icc 0 1) hv (hc.mono Icc_subset_Ici_self) (fun s hs ↦ hq s hs.1)
    (fun s hs ↦ hq01 s hs.1) hα
    (fun s hs ↦ (hasDerivAt_extinctionProb hb hd hs.1).hasDerivWithinAt)
    (fun s hs ↦ ⟨extinctionProb_nonneg hb hd hs.1, extinctionProb_le_one hb hd hs.1⟩)
    (by rw [hq0]; simp [extinctionProb]) (a := 0) (b := t)
  exact this ⟨ht, le_rfl⟩

/-- Supercritical case: if `d < b`, the extinction probability tends to `d / b`. -/
theorem tendsto_extinctionProb_of_lt {b d : ℝ} (hd : 0 ≤ d) (hdb : d < b) :
    Tendsto (extinctionProb b d) atTop (𝓝 (d / b)) := by
  have hb : 0 < b := hd.trans_lt hdb
  have he : Tendsto (fun t ↦ exp (-((b - d) * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by linarith))
  have key : Tendsto (fun t ↦ d * (1 - exp (-((b - d) * t))) / (b - d * exp (-((b - d) * t))))
      atTop (𝓝 (d * (1 - 0) / (b - d * 0))) :=
    ((tendsto_const_nhds.sub he).const_mul d).div (tendsto_const_nhds.sub (he.const_mul d))
      (by simp only [mul_zero, sub_zero, ne_eq]; exact hb.ne')
  rw [sub_zero, mul_one, mul_zero, sub_zero] at key
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hden := denom_pos hb.le ht hdb
  have hE := exp_pos ((b - d) * t)
  simp only [extinctionProb, hdb.ne', ↓reduceIte, exp_neg]
  field_simp

/-- Critical and subcritical cases: if `b ≤ d` and `0 < d`, extinction is certain in the limit. -/
theorem tendsto_extinctionProb_of_le {b d : ℝ} (hd : 0 < d) (hbd : b ≤ d) :
    Tendsto (extinctionProb b d) atTop (𝓝 1) := by
  rcases hbd.lt_or_eq with hbd | rfl
  · have he : Tendsto (fun t ↦ exp ((b - d) * t)) atTop (𝓝 0) := by
      have : Tendsto (fun t ↦ exp (-((d - b) * t))) atTop (𝓝 0) :=
        tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by linarith))
      refine this.congr fun t ↦ ?_
      ring_nf
    have key : Tendsto (fun t ↦ d * (exp ((b - d) * t) - 1) / (b * exp ((b - d) * t) - d))
        atTop (𝓝 (d * (0 - 1) / (b * 0 - d))) :=
      ((he.sub tendsto_const_nhds).const_mul d).div ((he.const_mul b).sub tendsto_const_nhds)
        (by simp only [mul_zero, zero_sub, ne_eq, neg_eq_zero]; exact hd.ne')
    have h1 : d * (0 - 1) / (b * 0 - d) = 1 := by
      rw [mul_zero, zero_sub, zero_sub, mul_neg_one, neg_div_neg_eq, div_self hd.ne']
    rw [h1] at key
    refine key.congr fun t ↦ ?_
    simp only [extinctionProb, hbd.ne, ↓reduceIte]
  · have hlin : Tendsto (fun t ↦ 1 + b * t) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop hd)
    have key : Tendsto (fun t ↦ 1 - (1 + b * t)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp hlin)
    rw [sub_zero] at key
    refine key.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have : 0 < 1 + b * t := by positivity
    simp only [extinctionProb, ↓reduceIte]
    field_simp
    ring

end MathlibExt.Probability.LinearBirthDeath
