/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import MathlibExt.Analysis.SpecialFunctions.LogSumExp

@[expose] public section

/-!
# Logarithmic market scoring rule (LMSR) cost-function market maker

This file formalizes Hanson's logarithmic market scoring rule (LMSR), a
cost-function market maker over finitely many outcomes `ι` with liquidity
parameter `b > 0` and outstanding-share vector `q : ι → ℝ`.

## Model summary

The cost of a share vector `q` is `C(q) = b * log ∑ i, exp (q i / b)`.
The instantaneous price of outcome `i` is the softmax probability
`pᵢ(q) = exp (q i / b) / ∑ j, exp (q j / b)`. A trader moving the market
from `q` to `q'` pays `C(q') - C(q)` and receives `q' i - q i` if outcome
`i` occurs. The market maker's worst-case loss is bounded by `b * log n`,
where `n` is the number of outcomes.

## Main results

* `lmsrCost`, `lmsrPrice`, `lmsrLoss`: cost, softmax prices, maker loss (C1).
* `le_lmsrCost`, `lmsrCost_le`: cost bounds in terms of `max q` (C2).
* `lmsrLoss_le`: worst-case maker loss is at most `b * log n` (C2).
* `deriv_update_lmsrCost`: the instantaneous price is the softmax (C3).
* `tradeProfit_eq_logScore`: trade profit equals the log-score difference (C3).
* `tendsto_lmsrLoss_single`: the loss bound `b * log n` is tight (C4).

## Non-goals

* Combinatorial markets: no joint-outcome or security-space structure.
* Liquidity-sensitive variants: `b` is a fixed positive constant.

## References

* R. Hanson, "Combinatorial information market design",
  Information Systems Frontiers 5, 2003.
* Y. Chen and D. M. Pennock, "A utility framework for bounded-loss
  market makers", UAI 2007.
-/

namespace MathlibExt.GameTheory.LMSR

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- (C1 cost/prices) LMSR cost function: `b * log ∑ i, exp (q i / b)`. -/
noncomputable def lmsrCost (b : ℝ) (q : ι → ℝ) : ℝ :=
  b * Real.logSumExp (fun i => q i / b)

/-- (C1 cost/prices) LMSR instantaneous price of outcome `i`: softmax. -/
noncomputable def lmsrPrice (b : ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  Real.softmax (fun j => q j / b) i

/-- (C1 cost/prices) Maker loss when `i` occurs after trades from `0` to `q`. -/
noncomputable def lmsrLoss (b : ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  q i - (lmsrCost b q - lmsrCost b (0 : ι → ℝ))

/-- (C1 cost/prices) LMSR prices are nonnegative (no hypothesis on `b`). -/
theorem lmsrPrice_nonneg (b : ℝ) (q : ι → ℝ) (i : ι) :
    0 ≤ lmsrPrice b q i :=
  (Real.softmax_pos _ i).le

/-- (C1 cost/prices) LMSR prices are positive (no hypothesis on `b`). -/
theorem lmsrPrice_pos (b : ℝ) (q : ι → ℝ) (i : ι) :
    0 < lmsrPrice b q i :=
  Real.softmax_pos _ i

/-- (C1 cost/prices) LMSR prices sum to one. -/
theorem sum_lmsrPrice (b : ℝ) (q : ι → ℝ) :
    ∑ i, lmsrPrice b q i = 1 :=
  Real.sum_softmax _

omit [Nonempty ι] in
/-- (C1 cost/prices) Cost of the zero share vector. -/
theorem lmsrCost_zero (b : ℝ) :
    lmsrCost b (0 : ι → ℝ) = b * Real.log (Fintype.card ι) := by
  simp [lmsrCost, Real.logSumExp]

/-- (C2 bounds) The cost dominates every outstanding-share quantity. -/
theorem le_lmsrCost (b : ℝ) (hb : 0 < b) (q : ι → ℝ) (i : ι) :
    q i ≤ lmsrCost b q := by
  have h1 : Real.exp (q i / b) ≤ ∑ j, Real.exp (q j / b) := by
    apply Finset.single_le_sum _ (Finset.mem_univ i)
    intro j _
    exact le_of_lt (Real.exp_pos _)
  have h2 : Real.log (Real.exp (q i / b)) ≤ Real.log (∑ j, Real.exp (q j / b)) :=
    Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h2
  have hbne : b ≠ 0 := ne_of_gt hb
  have h3 : q i = b * (q i / b) := (mul_div_cancel₀ _ hbne).symm
  rw [h3]
  simp only [lmsrCost, Real.logSumExp]
  exact mul_le_mul_of_nonneg_left h2 (le_of_lt hb)

/-- (C2 bounds) The cost is at most `max q + b * log n`. -/
theorem lmsrCost_le (b : ℝ) (hb : 0 < b) (q : ι → ℝ) (M : ℝ)
    (hM : ∀ j, q j ≤ M) :
    lmsrCost b q ≤ M + b * Real.log (Fintype.card ι) := by
  have hdiv : ∀ j, q j / b ≤ M / b := by
    intro j
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM j) (inv_nonneg.mpr (le_of_lt hb))
  have hsum : ∑ j, Real.exp (q j / b) ≤ (Fintype.card ι : ℝ) * Real.exp (M / b) := by
    have h := Finset.sum_le_card_nsmul Finset.univ (fun j => Real.exp (q j / b))
      (Real.exp (M / b)) (fun j _ => Real.exp_le_exp.mpr (hdiv j))
    rw [Finset.card_univ, nsmul_eq_mul] at h
    exact h
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlog : Real.log (∑ j, Real.exp (q j / b))
      ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (M / b)) :=
    Real.log_le_log (Real.sum_exp_pos (fun i => q i / b)) hsum
  rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hbne : b ≠ 0 := ne_of_gt hb
  have hcancel : b * (M / b) = M := mul_div_cancel₀ _ hbne
  have hmul : b * Real.log (∑ j, Real.exp (q j / b))
      ≤ b * (Real.log (Fintype.card ι) + M / b) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt hb)
  have hexpand : b * (Real.log (Fintype.card ι) + M / b)
      = b * Real.log (Fintype.card ι) + M := by
    rw [mul_add, hcancel]
  simp only [lmsrCost, Real.logSumExp]
  rw [hexpand] at hmul
  linarith

/-- (C2 bounds) Worst-case maker loss is at most `b * log n`. -/
theorem lmsrLoss_le (b : ℝ) (hb : 0 < b) (q : ι → ℝ) (i : ι) :
    lmsrLoss b q i ≤ b * Real.log (Fintype.card ι) := by
  unfold lmsrLoss
  rw [lmsrCost_zero]
  have h := le_lmsrCost b hb q i
  linarith

/-- (C3 price identity) Instantaneous price is the softmax price. -/
theorem deriv_update_lmsrCost [DecidableEq ι] (b : ℝ) (hb : 0 < b) (q : ι → ℝ)
    (i : ι) :
    deriv (fun t => lmsrCost b (Function.update q i (q i + t))) 0
      = lmsrPrice b q i := by
  have hsplit : ∀ t : ℝ, (∑ j, Real.exp ((Function.update q i (q i + t)) j / b))
      = Real.exp ((q i + t) / b)
        + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b) := by
    intro t
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.ne_of_mem_erase hj]
  have hfun : (fun t => lmsrCost b (Function.update q i (q i + t)))
      = fun t => b * Real.log (Real.exp ((q i + t) / b)
        + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b)) := by
    funext t
    simp only [lmsrCost, Real.logSumExp]
    rw [hsplit t]
  rw [hfun]
  have haffine : HasDerivAt (fun t : ℝ => (q i + t) / b) (1 / b) 0 :=
    ((hasDerivAt_const_add_iff (q i)).mpr (hasDerivAt_id 0)).div_const b
  have hexp : HasDerivAt (fun t : ℝ => Real.exp ((q i + t) / b))
      (Real.exp (q i / b) * (1 / b)) 0 := by
    simpa using haffine.exp
  have hsum : HasDerivAt (fun t : ℝ => Real.exp ((q i + t) / b)
      + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b))
      (Real.exp (q i / b) * (1 / b) + 0) 0 :=
    hexp.add (hasDerivAt_const 0 _)
  have harg : (0 : ℝ) < Real.exp ((q i + 0) / b)
      + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b) := by
    have hC : (0 : ℝ) ≤ ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b) :=
      Finset.sum_nonneg (fun j _ => le_of_lt (Real.exp_pos _))
    have he := Real.exp_pos ((q i + 0) / b)
    linarith
  have hlog : HasDerivAt (fun t : ℝ => Real.log (Real.exp ((q i + t) / b)
      + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b)))
      ((Real.exp (q i / b) * (1 / b) + 0)
        / (Real.exp ((q i + 0) / b)
          + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b))) 0 :=
    hsum.log (ne_of_gt harg)
  have hmul : HasDerivAt (fun t : ℝ => b * Real.log (Real.exp ((q i + t) / b)
      + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b)))
      (b * ((Real.exp (q i / b) * (1 / b) + 0)
        / (Real.exp ((q i + 0) / b)
          + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b)))) 0 :=
    hlog.const_mul b
  have hS0 : Real.exp ((q i + 0) / b)
      + ∑ j ∈ Finset.univ.erase i, Real.exp (q j / b)
      = ∑ j, Real.exp (q j / b) := by
    have h0 := hsplit 0
    have hcongr : (∑ j, Real.exp ((Function.update q i (q i + 0)) j / b))
        = ∑ j, Real.exp (q j / b) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [hcongr] at h0
    exact h0.symm
  rw [hmul.deriv, hS0]
  simp only [lmsrPrice, Real.softmax]
  have hbne : b ≠ 0 := ne_of_gt hb
  have hSne : (∑ j, Real.exp (q j / b)) ≠ 0 :=
    ne_of_gt (Real.sum_exp_pos (fun i => q i / b))
  field_simp
  ring

/-- (C3 price identity) Trade profit equals the log-score difference. -/
theorem tradeProfit_eq_logScore (b : ℝ) (hb : 0 < b) (q q' : ι → ℝ) (i : ι) :
    (q' i - q i) - (lmsrCost b q' - lmsrCost b q)
      = b * (Real.log (lmsrPrice b q' i) - Real.log (lmsrPrice b q i)) := by
  have hlog : ∀ r : ι → ℝ, Real.log (lmsrPrice b r i)
      = r i / b - Real.log (∑ j, Real.exp (r j / b)) := by
    intro r
    simp only [lmsrPrice, Real.softmax]
    rw [Real.log_div (Real.exp_pos _).ne' (Real.sum_exp_pos (fun i => r i / b)).ne',
      Real.log_exp]
  rw [hlog q', hlog q]
  simp only [lmsrCost, Real.logSumExp]
  have hbne : b ≠ 0 := ne_of_gt hb
  field_simp
  ring

/-- (C4 tightness) Heavy buying drives the loss to the `b * log n` bound. -/
theorem tendsto_lmsrLoss_single [DecidableEq ι] (b : ℝ) (hb : 0 < b) (i : ι) :
    Filter.Tendsto (fun t : ℝ => lmsrLoss b (Pi.single i t) i)
      Filter.atTop (nhds (b * Real.log (Fintype.card ι))) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hsplit : ∀ t : ℝ, (∑ j, Real.exp (((Pi.single i t : ι → ℝ)) j / b))
      = Real.exp (t / b) + ((Fintype.card ι - 1 : ℕ) : ℝ) := by
    intro t
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp only [Pi.single_eq_same]
    · have h1 : ∀ j ∈ Finset.univ.erase i,
          Real.exp (((Pi.single i t : ι → ℝ)) j / b) = 1 := by
        intro j hj
        have h0 : Pi.single (M := fun _ => ℝ) i t j = 0 :=
          Pi.single_eq_of_ne (M := fun _ => ℝ) (Finset.ne_of_mem_erase hj) t
        rw [h0]
        simp
      rw [Finset.sum_congr rfl h1, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        nsmul_eq_mul, mul_one]
  have hloss : ∀ t : ℝ, lmsrLoss b (Pi.single i t) i
      = b * Real.log (Fintype.card ι)
        - b * Real.log (1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
          * Real.exp (-(t / b))) := by
    intro t
    have hcost : lmsrCost b (Pi.single i t)
        = t + b * Real.log (1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
          * Real.exp (-(t / b))) := by
      simp only [lmsrCost, Real.logSumExp]
      rw [hsplit t]
      have hexp : (0 : ℝ) < Real.exp (t / b) := Real.exp_pos _
      have h1pos : (0 : ℝ) < 1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
          * Real.exp (-(t / b)) := by
        positivity
      have hmul : Real.exp (t / b) * Real.exp (-(t / b)) = 1 := by
        rw [← Real.exp_add]
        simp
      have hfac : Real.exp (t / b) + ((Fintype.card ι - 1 : ℕ) : ℝ)
          = Real.exp (t / b) * (1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
            * Real.exp (-(t / b))) := by
        have hexpand : Real.exp (t / b)
            * (1 + ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.exp (-(t / b)))
            = Real.exp (t / b) + ((Fintype.card ι - 1 : ℕ) : ℝ)
              * (Real.exp (t / b) * Real.exp (-(t / b))) := by
          ring
        rw [hexpand, hmul, mul_one]
      rw [hfac, Real.log_mul hexp.ne' h1pos.ne', Real.log_exp]
      have hcancel : b * (t / b) = t := mul_div_cancel₀ _ hbne
      rw [mul_add, hcancel]
    unfold lmsrLoss
    rw [lmsrCost_zero, Pi.single_eq_same, hcost]
    linarith
  have hfun : (fun t : ℝ => lmsrLoss b (Pi.single i t) i)
      = fun t => b * Real.log (Fintype.card ι)
        - b * Real.log (1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
          * Real.exp (-(t / b))) :=
    funext hloss
  rw [hfun]
  have hdiv : Filter.Tendsto (fun t : ℝ => t / b) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hb Filter.tendsto_id
  have hexp0 : Filter.Tendsto (fun t : ℝ => Real.exp (-(t / b))) Filter.atTop
      (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  have hKexp : Filter.Tendsto
      (fun t : ℝ => ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.exp (-(t / b)))
      Filter.atTop (nhds (((Fintype.card ι - 1 : ℕ) : ℝ) * 0)) :=
    Filter.Tendsto.const_mul _ hexp0
  rw [mul_zero] at hKexp
  have h1 : Filter.Tendsto
      (fun t : ℝ => 1 + ((Fintype.card ι - 1 : ℕ) : ℝ) * Real.exp (-(t / b)))
      Filter.atTop (nhds (1 + 0)) :=
    Filter.Tendsto.const_add 1 hKexp
  rw [add_zero] at h1
  have hlog1 : Filter.Tendsto
      (fun t : ℝ => Real.log (1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
        * Real.exp (-(t / b))))
      Filter.atTop (nhds (Real.log 1)) :=
    (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  rw [Real.log_one] at hlog1
  have hblog : Filter.Tendsto
      (fun t : ℝ => b * Real.log (1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
        * Real.exp (-(t / b))))
      Filter.atTop (nhds (b * 0)) :=
    Filter.Tendsto.const_mul b hlog1
  rw [mul_zero] at hblog
  have hfinal : Filter.Tendsto
      (fun t : ℝ => b * Real.log (Fintype.card ι)
        - b * Real.log (1 + ((Fintype.card ι - 1 : ℕ) : ℝ)
          * Real.exp (-(t / b))))
      Filter.atTop (nhds (b * Real.log (Fintype.card ι) - 0)) :=
    Filter.Tendsto.const_sub _ hblog
  rw [sub_zero] at hfinal
  exact hfinal

end MathlibExt.GameTheory.LMSR
