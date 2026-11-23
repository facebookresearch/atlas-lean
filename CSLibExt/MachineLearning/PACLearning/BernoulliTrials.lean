/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Valiant's Bernoulli-trial bound: `L(h, S) ≤ ⌈2h(S + ln h)⌉`

Section 4 of L. G. Valiant, *A theory of the learnable*, Comm. ACM 27 (1984), 1134-1142,
abstracts the probabilistic analysis of all his learning algorithms into one lemma. For a real
`h > 1` and a positive integer `S`, `L(h, S)` is the least number of independent Bernoulli trials,
each with success probability at least `1/h`, after which the probability of fewer than `S`
successes is less than `1/h`; his Proposition states `L(h, S) ≤ 2h(S + ln h)`. Valiant derives it
from a Chernoff bound on the binomial lower tail. This file proves the probability bound for every
number of trials `m ≥ 2h(S + ln h)`, which gives `L(h, S) ≤ ⌈2h(S + ln h)⌉`, one trial weaker than
the Proposition when `2h(S + ln h)` is not an integer. The proof uses the exponential moment at
`-1`:

`P(N < S) ≤ e^S E[e^{-N}] ≤ e^S exp (-(1 - e⁻¹) m / h) < e^S exp (-m / (2h)) ≤ 1 / h`

for `N` the number of successes in `m ≥ 2h(S + ln h)` trials, using `1 - e⁻¹ > 1/2`.

Main result:

* `measureReal_sum_lt_lt_inv`: **in `m ≥ 2h(S + ln h)` independent trials with success
  probabilities at least `1/h`, fewer than `S` successes has probability less than `1/h`**, so
  `L(h, S) ≤ ⌈2h(S + ln h)⌉`.

## Cost model

None: this is a probability estimate.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning.BernoulliTrials

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Exponential moment of a Bernoulli trial.** If `X` takes only the values `0` and `1`, then
`E[e^{-X}] = 1 - (1 - e⁻¹) P(X = 1)`. -/
theorem mgf_neg_one_of_zero_or_one [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) :
    mgf X μ (-1) = 1 - (1 - exp (-1)) * μ.real {ω | X ω = 1} := by
  have hset : MeasurableSet {ω | X ω = 1} := hX (measurableSet_singleton 1)
  have hpt : (fun ω => exp (-1 * X ω)) =
      fun ω => 1 - (1 - exp (-1)) * ({ω | X ω = 1}.indicator (fun _ => (1 : ℝ)) ω) := by
    funext ω
    rcases h01 ω with h | h <;> simp [h]
  have hint : Integrable ({ω | X ω = 1}.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hset
  rw [mgf, hpt, integral_sub (integrable_const _) (hint.const_mul _), integral_const_mul,
    integral_indicator_const (1 : ℝ) hset]
  simp

/-- **Valiant's Bernoulli-trial bound, `L(h, S) ≤ ⌈2h(S + ln h)⌉`.** Let `X₀, …, X_{m-1}` be
independent random variables with values in `{0, 1}` (Bernoulli trials), each with success
probability `P(Xᵢ = 1) ≥ 1/h`, where `h > 1`, and let `S ≥ 1` be an integer. If
`m ≥ 2h(S + ln h)`, then the probability of fewer than `S` successes is less than `1/h`. Hence
`L(h, S) ≤ ⌈2h(S + ln h)⌉`; Valiant's Proposition states the slightly sharper
`L(h, S) ≤ 2h(S + log_e h)` (L. G. Valiant, *A theory of the learnable*, Comm. ACM 27 (1984),
1134-1142, Section 4, Proposition). -/
theorem measureReal_sum_lt_lt_inv [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    {h : ℝ} (hh : 1 < h) (hp : ∀ i, 1 / h ≤ μ.real {ω | X i ω = 1}) {S : ℕ} (hS : 1 ≤ S)
    (hm : 2 * h * (S + log h) ≤ m) :
    μ.real {ω | ∑ i, X i ω < S} < 1 / h := by
  set c : ℝ := 1 - exp (-1) with hc
  have he : exp (-1) < 1 / 2 := by
    rw [exp_neg, inv_lt_comm₀ (exp_pos 1) (by norm_num)]
    have := exp_one_gt_d9
    norm_num at this ⊢
    linarith
  have hc_half : 1 / 2 < c := by rw [hc]; linarith
  have hc1 : c ≤ 1 := by rw [hc]; linarith [exp_pos (-1)]
  have hh0 : 0 < h := by linarith
  have hlog : 0 < log h := log_pos hh
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  set N : Ω → ℝ := ∑ i, X i with hN
  have hNapp : ∀ ω, N ω = ∑ i, X i ω := fun ω => by simp [hN]
  have hNmeas : Measurable N := by
    rw [hN]; fun_prop
  -- `e^{-N}` is bounded by `1`, hence integrable.
  have hNnonneg : ∀ ω, 0 ≤ N ω := fun ω => by
    rw [hNapp]; exact Finset.sum_nonneg fun i _ => by rcases h01 i ω with h | h <;> simp [h]
  have hint : Integrable (fun ω => exp (-1 * N ω)) μ := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (measurable_exp.comp (hNmeas.const_mul (-1))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      linarith [hNnonneg ω]
  -- Chernoff at `t = -1`.
  have hchern : μ.real {ω | N ω ≤ S} ≤ exp S * mgf N μ (-1) := by
    have := measure_le_le_exp_mul_mgf (X := N) (μ := μ) (S : ℝ) (t := -1) (by norm_num) hint
    simpa using this
  have hmgf : mgf N μ (-1) = ∏ i, (1 - c * μ.real {ω | X i ω = 1}) := by
    rw [hN, hind.mgf_sum hmeas]
    exact Finset.prod_congr rfl fun i _ => mgf_neg_one_of_zero_or_one (hmeas i) (h01 i)
  have hprod : ∏ i, (1 - c * μ.real {ω | X i ω = 1}) ≤ exp (-(c * (m / h))) := by
    calc ∏ i, (1 - c * μ.real {ω | X i ω = 1})
        ≤ ∏ i : Fin m, exp (-(c * μ.real {ω | X i ω = 1})) := by
          refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
          · have : μ.real {ω | X i ω = 1} ≤ 1 := measureReal_le_one
            nlinarith [measureReal_nonneg (μ := μ) (s := {ω | X i ω = 1})]
          · linarith [add_one_le_exp (-(c * μ.real {ω | X i ω = 1}))]
      _ = exp (-(c * ∑ i, μ.real {ω | X i ω = 1})) := by
          rw [← exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ exp (-(c * (m / h))) := by
          gcongr
          calc (m : ℝ) / h = ∑ _i : Fin m, 1 / h := by simp [div_eq_mul_inv]
            _ ≤ ∑ i, μ.real {ω | X i ω = 1} := Finset.sum_le_sum fun i _ => hp i
  have hfinal : exp S * exp (-(c * (m / h))) < 1 / h := by
    rw [← exp_add]
    have hmh : 2 * (S + log h) ≤ m / h := by
      rw [le_div_iff₀ hh0]; linarith
    have hpos : 0 < (m : ℝ) / h := by positivity
    have : (S : ℝ) - c * (m / h) < -log h := by nlinarith
    calc exp (S - c * (m / h)) < exp (-log h) := exp_lt_exp.2 (by linarith)
      _ = 1 / h := by rw [exp_neg, exp_log hh0, one_div]
  calc μ.real {ω | ∑ i, X i ω < S} ≤ μ.real {ω | N ω ≤ S} :=
        measureReal_mono (fun ω hω => by
          simp only [Set.mem_ofPred_eq] at hω ⊢; rw [hNapp]; exact hω.le)
    _ ≤ exp S * mgf N μ (-1) := hchern
    _ ≤ exp S * exp (-(c * (m / h))) := by
        rw [hmgf]; exact mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ < 1 / h := hfinal

end Cslib.MachineLearning.PACLearning.BernoulliTrials
