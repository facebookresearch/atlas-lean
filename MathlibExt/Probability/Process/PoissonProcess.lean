/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.FinCases

/-!
# Poisson processes

A counting process `N : ℝ≥0 → Ω → ℕ` is a *Poisson process of rate `r`* (Kingman 1993, ch. 4;
Karlin–Taylor 1975, ch. 4) if `N 0 = 0`, its paths are nondecreasing, it has independent
increments, and every increment `N t - N s` (`s ≤ t`) has the Poisson law of mean `r (t - s)`.
In particular the increments are stationary: the law of `N t - N s` depends only on `t - s`.

We also consider the counting process of i.i.d. exponential interarrival times `T 0, T 1, …` of
rate `r`: the `n`-th arrival happens at `S n = T 0 + ⋯ + T (n - 1)` and `N t = #{n ≥ 1 : S n ≤ t}`.

## Main definitions

* `ProbabilityTheory.IsPoissonProcess N r P`: `N` is a Poisson process of rate `r` under `P`.
* `ProbabilityTheory.PoissonProcess.arrivalTime T n`: the `n`-th arrival time `S n`.
* `ProbabilityTheory.PoissonProcess.count T t`: the number of arrivals in `[0, t]`.
* `ProbabilityTheory.PoissonProcess.thinning N B`: keep the `i`-th point of `N` iff `B i`.

## Main results

* `PoissonProcess.hasLaw_arrivalTime`: `S (n + 1)` has the Gamma (Erlang) law `Γ(n + 1, r)`.
* `PoissonProcess.hasLaw_count`: `N t` has the Poisson law of mean `r t`.
* `PoissonProcess.ae_count_zero`, `PoissonProcess.ae_count_monotone`: `N 0 = 0` and the paths of
  `N` are nondecreasing almost surely.
* `PoissonProcess.hasLaw_count_increments`: the increments of `N` over consecutive intervals are
  independent with the Poisson laws of means `r (t (i + 1) - t i)`.
* `PoissonProcess.isPoissonProcess_count`: hence `N` is a Poisson process of rate `r`.
* `IsPoissonProcess.add` (superposition): the sum of two independent Poisson processes of rates
  `r₁` and `r₂` is a Poisson process of rate `r₁ + r₂`.
* `IsPoissonProcess.thinning`: keeping each point independently with probability `p` turns a
  Poisson process of rate `r` into a Poisson process of rate `p r`.

## Implementation notes

Times and rates are in `ℝ≥0`, so no sign hypotheses are needed. The conditions `N 0 = 0` and
monotone paths are required almost surely, as in Kingman (1993); the counting process of
exponential interarrivals satisfies them only off a null set (an interarrival can vanish, and on
the null event `∑ T i < ∞` the arrival set in `[0, t]` is infinite and `Set.ncard` returns its
junk value `0`). Increments `N t - N s` use truncated subtraction on `ℕ`; along a.s. monotone
paths it is the true increment. The independence of the increments of `N` is proved by
conditioning on the first interarrival time (memorylessness and the Erlang convolution), by
induction over the blocks of consecutive intervals; no joint density of the arrival times is used.

## References

* J. F. C. Kingman, *Poisson Processes*, Oxford University Press (1993), §2.2, ch. 4, §5.1.
* S. Karlin, H. M. Taylor, *A First Course in Stochastic Processes*, 2nd ed., Academic Press
  (1975), ch. 4.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `N : ℝ≥0 → Ω → ℕ` is a **Poisson process of rate `r`** under `P` (Kingman 1993, ch. 4;
Karlin–Taylor 1975, ch. 4): `N 0 = 0` and the paths are nondecreasing almost surely, the
increments over consecutive intervals are independent, and for `s ≤ t` the increment `N t - N s`
has the Poisson law of mean `r (t - s)`. -/
structure IsPoissonProcess (N : ℝ≥0 → Ω → ℕ) (r : ℝ≥0) (P : Measure Ω := by volume_tac) :
    Prop where
  /-- The process starts at `0` almost surely. -/
  ae_zero : ∀ᵐ ω ∂P, N 0 ω = 0
  /-- Almost every path is nondecreasing. -/
  ae_monotone : ∀ᵐ ω ∂P, Monotone fun t ↦ N t ω
  /-- Increments over consecutive intervals are independent. -/
  hasIndepIncrements : HasIndepIncrements N P
  /-- The increment over `(s, t]` has the Poisson law of mean `r (t - s)`. -/
  hasLaw_sub : ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
    HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P

namespace PoissonProcess

/-- The `n`-th arrival time `S n = T 0 + ⋯ + T (n - 1)` of the interarrival times `T`. -/
noncomputable def arrivalTime (T : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, T i ω

/-- The counting process of the interarrival times `T`: `count T t ω` is the number of arrivals
`n ≥ 1` with `S n ≤ t`. When that set is infinite (a null event for exponential interarrivals of
positive rate) `Set.ncard` returns `0`. -/
noncomputable def count (T : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℕ :=
  {n : ℕ | arrivalTime T (n + 1) ω ≤ t}.ncard

private lemma erlang_pdf (n : ℕ) (r x : ℝ) (hx : 0 ≤ x) :
    gammaPDF (n + 1) r x =
      ENNReal.ofReal (r ^ (n + 1) / (n.factorial : ℝ) * x ^ n * Real.exp (-(r * x))) := by
  rw [gammaPDF_of_nonneg hx, Real.Gamma_nat_eq_factorial]
  simp only [add_sub_cancel_right]
  rw [← Nat.cast_add_one, Real.rpow_natCast, Real.rpow_natCast]

private lemma erlang_conv_integrand (n : ℕ) (r x y : ℝ) (hr : 0 < r) :
    gammaPDF (n + 1) r y * gammaPDF 1 r (-y + x) =
      (Icc 0 x).indicator
        (fun y ↦ ENNReal.ofReal
          (r ^ (n + 1) / (n.factorial : ℝ) * r * Real.exp (-(r * x)) * y ^ n)) y := by
  by_cases hy : 0 ≤ y
  · by_cases hxy : y ≤ x
    · rw [erlang_pdf n r y hy]
      change ENNReal.ofReal _ * exponentialPDF r (-y + x) = _
      rw [exponentialPDF_of_nonneg (by linarith),
        indicator_of_mem (show y ∈ Icc 0 x from ⟨hy, hxy⟩)]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have he : Real.exp (-(r * y)) * Real.exp (-(r * (-y + x))) =
          Real.exp (-(r * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = r ^ (n + 1) / (n.factorial : ℝ) * r *
            (Real.exp (-(r * y)) * Real.exp (-(r * (-y + x)))) * y ^ n := by ring
        _ = _ := by rw [he]
    · rw [gammaPDF_of_neg (show -y + x < 0 by linarith), mul_zero,
        indicator_of_notMem (by simp [hxy])]
  · rw [gammaPDF_of_neg (lt_of_not_ge hy), zero_mul,
      indicator_of_notMem (by simp [hy])]

private lemma erlang_density_conv (n : ℕ) (r x : ℝ) (hr : 0 < r) :
    (∫⁻ y, gammaPDF (n + 1) r y * gammaPDF 1 r (-y + x)) =
      gammaPDF (n + 2) r x := by
  simp_rw [erlang_conv_integrand n r x _ hr]
  rw [lintegral_indicator measurableSet_Icc]
  by_cases hx : 0 ≤ x
  · rw [← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous (fun y : ℝ ↦
        r ^ (n + 1) / (n.factorial : ℝ) * r * Real.exp (-(r * x)) * y ^ n)).integrableOn_Icc)]
    · rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hx, integral_pow]
      rw [show (n : ℝ) + 2 = (n + 1 : ℕ) + 1 by push_cast; ring]
      rw [erlang_pdf (n + 1) r x hx]
      congr 1
      simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact mul_nonneg (by positivity) (pow_nonneg hy.1 n)
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hx), Measure.restrict_empty, lintegral_zero_measure,
      gammaPDF_of_neg (lt_of_not_ge hx)]

private lemma erlang_conv (n : ℕ) (r : ℝ) (hr : 0 < r) :
    gammaMeasure (n + 1) r ∗ expMeasure r = gammaMeasure (n + 2) r := by
  unfold expMeasure gammaMeasure
  rw [conv_withDensity_eq_lconvolution (by unfold gammaPDF; fun_prop)
    (by unfold gammaPDF; fun_prop)]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ erlang_density_conv n r x hr

/-- The `(n + 1)`-th arrival time of i.i.d. rate-`r` exponential interarrivals has the Gamma
(Erlang) law with shape `n + 1` and rate `r` (Karlin–Taylor 1975, §4.2). -/
theorem hasLaw_arrivalTime {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) (n : ℕ) :
    HasLaw (arrivalTime T (n + 1)) (gammaMeasure (n + 1) r) P := by
  have hr' : 0 < (r : ℝ) := hr
  have := isProbabilityMeasure_expMeasure hr'
  induction n with
  | zero =>
    convert hT 0 using 1
    · ext ω
      simp [arrivalTime]
    · simp [expMeasure]
  | succ n ih =>
    have := isProbabilityMeasure_gammaMeasure (show 0 < (n : ℝ) + 1 by positivity) hr'
    have hi : IndepFun (arrivalTime T (n + 1)) (T (n + 1)) P := by
      convert hind.indepFun_finsetSum_of_notMem₀ (fun i ↦ (hT i).aemeasurable)
        (s := Finset.range (n + 1)) (i := n + 1) (by simp) using 1
      ext ω
      simp [arrivalTime, Finset.sum_apply]
    have h := hi.hasLaw_add ih (hT (n + 1))
    rw [erlang_conv n (r : ℝ) hr'] at h
    convert h using 1
    · ext ω
      simp [arrivalTime, Finset.sum_range_succ]
    · congr 1
      push_cast
      ring

private lemma exp_survival (r u : ℝ) (hr : 0 < r) (hu : 0 ≤ u) :
    expMeasure r (Ioi u) = ENNReal.ofReal (Real.exp (-(r * u))) := by
  have := isProbabilityMeasure_expMeasure hr
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change (expMeasure r).real (Ioi u) = _
  have huniv : (expMeasure r).real univ = 1 := by simp [measureReal_def]
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, huniv,
    ← cdf_eq_real, cdf_expMeasure_eq hr, ite_eq_left hu]
  ring

private lemma gamma_gap_integrand (n : ℕ) (r t x : ℝ) (hr : 0 < r) :
    gammaPDF (n + 1) r x *
      (expMeasure r) {y | x ≤ t ∧ t < x + y} =
      (gammaPDF (n + 1) r x * gammaPDF 1 r (-x + t)) *
        (ENNReal.ofReal r)⁻¹ := by
  by_cases hx : x ≤ t
  · have heq : {y : ℝ | x ≤ t ∧ t < x + y} = Ioi (-x + t) := by
      ext y
      simp only [mem_ofPred_eq, mem_Ioi]
      constructor
      · rintro ⟨_, h⟩
        linarith
      · intro h
        exact ⟨hx, by linarith⟩
    rw [heq, exp_survival r (-x + t) hr (by linarith)]
    change _ = (gammaPDF (n + 1) r x * exponentialPDF r (-x + t)) * _
    rw [exponentialPDF_of_nonneg (by linarith), ENNReal.ofReal_mul hr.le]
    have hr0 : ENNReal.ofReal r ≠ 0 := by positivity
    calc
      _ = (gammaPDF (n + 1) r x * ENNReal.ofReal (Real.exp (-(r * (-x + t))))) *
          (ENNReal.ofReal r * (ENNReal.ofReal r)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hr0 ENNReal.ofReal_ne_top, mul_one]
      _ = _ := by ac_rfl
  · have heq : {y : ℝ | x ≤ t ∧ t < x + y} = ∅ := by simp [hx]
    rw [heq, measure_empty, mul_zero, gammaPDF_of_neg (x := -x + t) (by linarith),
      mul_zero, zero_mul]

private lemma gamma_gap_measure (n : ℕ) (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    ((gammaMeasure (n + 1) r).prod (expMeasure r))
        {z | z.1 ≤ t ∧ t < z.1 + z.2} =
      ENNReal.ofReal (Real.exp (-(r * t)) * (r * t) ^ (n + 1) /
        ((n + 1).factorial : ℝ)) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [Measure.prod_apply (by measurability)]
  change (∫⁻ x, (expMeasure r) {y | x ≤ t ∧ t < x + y}
    ∂(volume.withDensity (gammaPDF (n + 1) r))) = _
  have hg : Measurable fun x : ℝ ↦ (expMeasure r) {y | x ≤ t ∧ t < x + y} := by
    convert measurable_measure_prodMk_left (ν := expMeasure r)
      (s := {z : ℝ × ℝ | z.1 ≤ t ∧ t < z.1 + z.2}) (by measurability) using 1
    ext x
    congr 1
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold gammaPDF; fun_prop) hg]
  simp only [Pi.mul_apply]
  simp_rw [gamma_gap_integrand n r t _ hr]
  rw [lintegral_mul_const _ (by unfold gammaPDF; fun_prop),
    erlang_density_conv n r t hr]
  rw [show (n : ℝ) + 2 = (n + 1 : ℕ) + 1 by push_cast; ring,
    erlang_pdf (n + 1) r t ht, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hr]
  congr 1
  rw [pow_succ, mul_pow]
  field_simp

private lemma arrivalTime_mono {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω)
    (hT : ∀ i, 0 ≤ T i ω) : Monotone (fun n ↦ arrivalTime T n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [arrivalTime, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hT n)

private lemma count_of_gap {Ω : Type*} (T : ℕ → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (hT : ∀ i, 0 ≤ T i ω) (k : ℕ)
    (hk : arrivalTime T k ω ≤ t ∧ t < arrivalTime T (k + 1) ω) :
    count T t ω = k := by
  have hm := arrivalTime_mono T ω hT
  have heq : {n : ℕ | arrivalTime T (n + 1) ω ≤ t} = Iio k := by
    ext n
    simp only [mem_ofPred_eq, mem_Iio]
    constructor
    · intro hn
      by_contra hnk
      have hle := hm (Nat.add_le_add_right (Nat.le_of_not_gt hnk) 1)
      linarith [hk.2]
    · intro hn
      exact (hm (by omega)).trans hk.1
  unfold count
  rw [heq, Set.ncard_Iio_nat]

private lemma ae_nonneg_exp (r : ℝ) :
    ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
  rw [ae_iff]
  have heq : {a : ℝ | ¬0 ≤ a} = Iio 0 := by ext; simp
  rw [heq]
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

private lemma arrivalTime_aemeasurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {T : ℕ → Ω → ℝ} (hT : ∀ i, AEMeasurable (T i) P) (n : ℕ) :
    AEMeasurable (arrivalTime T n) P := by
  change AEMeasurable (fun ω ↦ ∑ i ∈ Finset.range n, T i ω) P
  fun_prop

private lemma gap_probability {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P)
    (t : ℝ≥0) (k : ℕ) :
    P {ω | arrivalTime T k ω ≤ t ∧ t < arrivalTime T (k + 1) ω} =
      (poissonMeasure (r * t)) {k} := by
  have hr' : 0 < (r : ℝ) := hr
  have := isProbabilityMeasure_expMeasure hr'
  have := (hT 0).isProbabilityMeasure
  rw [poissonMeasure_singleton]
  cases k with
  | zero =>
    have heq : {ω | arrivalTime T 0 ω ≤ t ∧ t < arrivalTime T (0 + 1) ω} =
        {ω | (t : ℝ) < T 0 ω} := by
      ext ω
      simp [arrivalTime, t.coe_nonneg]
    rw [heq]
    have hl := (hT 0).measure_eq (p := fun x ↦ (t : ℝ) < x) measurableSet_Ioi
    convert hl.trans (exp_survival (r : ℝ) t hr' t.coe_nonneg) using 1
    simp
  | succ n =>
    have hi : IndepFun (arrivalTime T (n + 1)) (T (n + 1)) P := by
      convert hind.indepFun_finsetSum_of_notMem₀ (fun i ↦ (hT i).aemeasurable)
        (s := Finset.range (n + 1)) (i := n + 1) (by simp) using 1
      ext ω
      simp [arrivalTime, Finset.sum_apply]
    have hp := hi.hasLaw_prod (hasLaw_arrivalTime hr hT hind n) (hT (n + 1))
    have hl := hp.measure_eq
      (p := fun z : ℝ × ℝ ↦ z.1 ≤ t ∧ (t : ℝ) < z.1 + z.2) (by measurability)
    convert hl.trans (gamma_gap_measure n (r : ℝ) t hr' t.coe_nonneg) using 1
    · congr 1
      ext ω
      simp [arrivalTime, Finset.sum_range_succ]
    · simp

/-- The number of arrivals in `[0, t]` of i.i.d. rate-`r` exponential interarrivals has the
Poisson law of mean `r t` (Karlin–Taylor 1975, §4.2, Theorem 2.1). -/
theorem hasLaw_count {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) (t : ℝ≥0) :
    HasLaw (count T t) (poissonMeasure (r * t)) P := by
  have hr' : 0 < (r : ℝ) := hr
  have := isProbabilityMeasure_expMeasure hr'
  have := (hT 0).isProbabilityMeasure
  have hS := arrivalTime_aemeasurable (fun i ↦ (hT i).aemeasurable)
  have hN : AEMeasurable (count T t) P := by
    change AEMeasurable (fun ω ↦ {n | arrivalTime T (n + 1) ω ≤ t}.ncard) P
    apply measurable_ncard.comp_aemeasurable
    apply AEMeasurable.of_mem
    intro n
    exact nullMeasurableSet_setOfPred.mp (nullMeasurableSet_le (hS (n + 1))
      aemeasurable_const)
  have hpos : ∀ᵐ ω ∂P, ∀ i, 0 ≤ T i ω := by
    apply ae_all_iff.mpr
    intro i
    exact ((hT i).ae_iff measurableSet_Ici.mem).mpr (ae_nonneg_exp (r : ℝ))
  let E : ℕ → Set Ω := fun k ↦
    {ω | arrivalTime T k ω ≤ t ∧ t < arrivalTime T (k + 1) ω}
  have hE : ∀ k, NullMeasurableSet (E k) P := fun k ↦
    (nullMeasurableSet_le (hS k) aemeasurable_const).inter
      (nullMeasurableSet_lt aemeasurable_const (hS (k + 1)))
  have hd : Pairwise (Function.onFun (AEDisjoint P) E) := by
    intro i j hij
    change AEDisjoint P (E i) (E j)
    rw [AEDisjoint]
    apply measure_mono_null_ae (t := ∅) ?_ measure_empty
    filter_upwards [hpos] with ω hω
    rintro ⟨hi, hj⟩
    have hm := arrivalTime_mono T ω hω
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle := hm (show i + 1 ≤ j by omega)
      exact (not_lt_of_ge (hle.trans hj.1)) hi.2
    · have hle := hm (show j + 1 ≤ i by omega)
      exact (not_lt_of_ge (hle.trans hi.1)) hj.2
  have hprob : ∀ k, P (E k) = (poissonMeasure (r * t)) {k} :=
    gap_probability hr hT hind t
  have hU : P (⋃ k, E k) = 1 := by
    rw [measure_iUnion₀ hd hE]
    simp_rw [hprob]
    rw [← measure_iUnion (f := fun k : ℕ ↦ ({k} : Set ℕ))
      (by intro i j hij; exact disjoint_singleton.mpr hij) measurableSet_singleton]
    rw [show (⋃ k : ℕ, ({k} : Set ℕ)) = univ by ext x; simp]
    exact measure_univ
  have hgood : ∀ᵐ ω ∂P, ω ∈ ⋃ k, E k := by
    rw [ae_iff]
    change P (⋃ k, E k)ᶜ = 0
    rw [measure_compl₀ (NullMeasurableSet.iUnion hE) (measure_ne_top _ _),
      measure_univ, hU, tsub_self]
  refine ⟨hN, Measure.ext_of_singleton fun k ↦ ?_⟩
  rw [Measure.map_apply_of_aemeasurable hN (measurableSet_singleton k)]
  calc
    P ((count T t) ⁻¹' {k}) = P (E k) := by
      apply measure_congr
      filter_upwards [hpos, hgood] with ω hω hg
      obtain ⟨j, hj⟩ := mem_iUnion.mp hg
      have hjc := count_of_gap T t ω hω j hj
      apply propext
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hk
        have hjk : j = k := hjc.symm.trans hk
        simpa [hjk] using hj
      · intro hk
        exact count_of_gap T t ω hω k hk
    _ = _ := hprob k

private theorem expMeasure_Iic {r : ℝ} (hr : 0 < r) (x : ℝ) :
    expMeasure r (Set.Iic x) =
      ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr]

private theorem ae_interarrival_pos {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) :
    ∀ᵐ ω ∂P, ∀ i, 0 < T i ω := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have h := (hT i).measure_eq (p := fun x ↦ x ≤ 0) measurableSet_Iic
  change P {ω | T i ω ≤ 0} = expMeasure r (Set.Iic 0) at h
  simpa only [not_lt, expMeasure_Iic (NNReal.coe_pos.mpr hr) 0, mul_zero, neg_zero,
    Real.exp_zero, sub_self, ENNReal.ofReal_zero, ite_eq_left le_rfl] using h

private theorem arrivalTime_succ (T : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    arrivalTime T (n + 1) ω = arrivalTime T n ω + T n ω := by
  simp [arrivalTime, Finset.sum_range_succ]

private theorem arrivalTime_strictMono {T : ℕ → Ω → ℝ} {ω : Ω}
    (hω : ∀ i, 0 < T i ω) : StrictMono fun n ↦ arrivalTime T n ω := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [arrivalTime_succ]
  exact lt_add_of_pos_right _ (hω n)

/-- The counting process of i.i.d. rate-`r` exponential interarrivals starts at `0` almost
surely (all interarrival times are positive almost surely). -/
theorem ae_count_zero {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) : ∀ᵐ ω ∂P, count T 0 ω = 0 := by
  filter_upwards [ae_interarrival_pos hr hT] with ω hω
  have hpos (n : ℕ) : 0 < arrivalTime T (n + 1) ω := by
    simpa [arrivalTime] using (arrivalTime_strictMono hω) (Nat.zero_lt_succ n)
  have hempty : {n : ℕ | arrivalTime T (n + 1) ω ≤ (0 : ℝ≥0)} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, NNReal.coe_zero, Set.mem_empty_iff_false, iff_false]
    exact not_le.mpr (hpos n)
  simp only [count, hempty, Set.ncard_empty]

private theorem ae_arrivalTime_tendsto {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n ↦ arrivalTime T n ω) Filter.atTop Filter.atTop := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have := (hT 0).isProbabilityMeasure
  let f : ℝ → ℝ := (Set.Ioi 1).indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_Ioi
  have hint : Integrable (f ∘ T 0) P :=
    (hT 0).integrable_comp ((integrable_const 1).indicator measurableSet_Ioi)
  have hmean : 0 < ∫ x, f x ∂expMeasure r := by
    change 0 < ∫ x, (Set.Ioi 1).indicator (fun _ ↦ (1 : ℝ)) x ∂expMeasure r
    rw [integral_indicator_const 1 measurableSet_Ioi, smul_eq_mul, mul_one]
    rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
      ← cdf_eq_real, cdf_expMeasure_eq (NNReal.coe_pos.mpr hr)]
    simp only [ite_eq_left (zero_le_one : (0 : ℝ) ≤ 1)]
    linarith [Real.exp_pos (-(r * (1 : ℝ)))]
  have hmean' : 0 < ∫ ω, (f ∘ T 0) ω ∂P := by
    rw [(hT 0).integral_comp hf.aestronglyMeasurable]
    exact hmean
  have hlim := strong_law_ae_real (fun i ↦ f ∘ T i) hint
    (fun i j hij ↦ (hind.indepFun hij).comp hf hf)
    (fun i ↦ ((hT i).identDistrib (hT 0)).comp hf)
  filter_upwards [hlim, ae_interarrival_pos hr hT] with ω hω hpos
  have hsum : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f (T i ω))
      Filter.atTop Filter.atTop := by
    have h := Filter.Tendsto.atTop_mul_pos hmean'
      (tendsto_natCast_atTop_atTop (R := ℝ)) hω
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [Function.comp_apply]
    field_simp
  apply Filter.tendsto_atTop_mono _ hsum
  intro n
  apply Finset.sum_le_sum
  intro i hi
  change (Set.Ioi 1).indicator (fun _ ↦ (1 : ℝ)) (T i ω) ≤ T i ω
  by_cases h : 1 < T i ω
  · simpa [h] using h.le
  · simpa [h] using (hpos i).le

private theorem finite_arrivals {T : ℕ → Ω → ℝ} {ω : Ω}
    (hω : Filter.Tendsto (fun n ↦ arrivalTime T n ω) Filter.atTop Filter.atTop)
    (t : ℝ≥0) : {n : ℕ | arrivalTime T (n + 1) ω ≤ t}.Finite := by
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 (hω.eventually_gt_atTop (t : ℝ))
  apply (Set.finite_Iio m).subset
  intro n hn
  change n < m
  by_contra h
  have hlt := hm (n + 1) (by omega)
  exact (not_le.mpr hlt) hn

/-- The counting process of i.i.d. rate-`r` exponential interarrivals has nondecreasing paths
almost surely (the arrival times tend to infinity almost surely, so every arrival set in
`[0, t]` is finite). -/
theorem ae_count_monotone {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) :
    ∀ᵐ ω ∂P, Monotone fun t ↦ count T t ω := by
  filter_upwards [ae_arrivalTime_tendsto hr hT hind] with ω hω
  intro s t hst
  exact Set.ncard_le_ncard (fun n hn ↦ hn.trans (NNReal.coe_le_coe.mpr hst))
    (finite_arrivals hω t)

end PoissonProcess

/-- Increments of paths are measurable functions of the path. -/
private lemma measurable_incr (s t : ℝ≥0) : Measurable fun f : ℝ≥0 → ℕ ↦ f t - f s := by
  have h : Measurable fun f : ℝ≥0 → ℕ ↦ (f t, f s) :=
    (measurable_pi_apply t).prodMk (measurable_pi_apply s)
  exact (measurable_of_countable fun p : ℕ × ℕ ↦ p.1 - p.2).comp h

/-- Two independent families of independent `ℕ`-valued variables, independent of each other as
vectors, give an independent family of pairs. -/
private lemma iIndepFun_prodMk {n : ℕ} {A B : Fin n → Ω → ℕ} [IsProbabilityMeasure P]
    (hAm : ∀ i, AEMeasurable (A i) P) (hBm : ∀ i, AEMeasurable (B i) P)
    (hA : iIndepFun A P) (hB : iIndepFun B P)
    (hAB : IndepFun (fun ω i ↦ A i ω) (fun ω i ↦ B i ω) P) :
    iIndepFun (fun i ω ↦ (A i ω, B i ω)) P := by
  have hABi : ∀ i, IndepFun (A i) (B i) P := fun i ↦
    hAB.comp (measurable_pi_apply i) (measurable_pi_apply i)
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hAm i).prodMk (hBm i)]
  refine Measure.ext_of_singleton fun x ↦ ?_
  have hAv : AEMeasurable (fun ω i ↦ A i ω) P := .of_eval hAm
  have hBv : AEMeasurable (fun ω i ↦ B i ω) P := .of_eval hBm
  have hpre : (fun ω i ↦ (A i ω, B i ω)) ⁻¹' {x}
      = (fun ω i ↦ A i ω) ⁻¹' {fun i ↦ (x i).1} ∩ (fun ω i ↦ B i ω) ⁻¹' {fun i ↦ (x i).2} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, funext_iff,
      Prod.ext_iff]
    exact forall_and
  rw [Measure.map_apply_of_aemeasurable (.of_eval fun i ↦ (hAm i).prodMk (hBm i))
    (measurableSet_singleton _), hpre,
    hAB.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _) (measurableSet_singleton _),
    ← Measure.map_apply_of_aemeasurable hAv (measurableSet_singleton _),
    ← Measure.map_apply_of_aemeasurable hBv (measurableSet_singleton _),
    hA.map_fun_eq_pi_map hAm, hB.map_fun_eq_pi_map hBm, Measure.pi_singleton,
    Measure.pi_singleton, Measure.pi_singleton, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have hprei : (fun ω ↦ (A i ω, B i ω)) ⁻¹' {x i} = A i ⁻¹' {(x i).1} ∩ B i ⁻¹' {(x i).2} := by
    ext ω
    simp [Prod.ext_iff]
  rw [Measure.map_apply_of_aemeasurable ((hAm i).prodMk (hBm i)) (measurableSet_singleton _),
    hprei, (hABi i).measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
      (measurableSet_singleton _),
    Measure.map_apply_of_aemeasurable (hAm i) (measurableSet_singleton _),
    Measure.map_apply_of_aemeasurable (hBm i) (measurableSet_singleton _)]

/-- **Superposition** (Kingman 1993, §2.2): the sum of two independent Poisson processes of rates
`r₁` and `r₂` is a Poisson process of rate `r₁ + r₂`. Independence is of the two processes as
random paths. -/
theorem IsPoissonProcess.add {N₁ N₂ : ℝ≥0 → Ω → ℕ} {r₁ r₂ : ℝ≥0}
    (h₁ : IsPoissonProcess N₁ r₁ P) (h₂ : IsPoissonProcess N₂ r₂ P)
    (hind : IndepFun (fun ω t ↦ N₁ t ω) (fun ω t ↦ N₂ t ω) P) :
    IsPoissonProcess (N₁ + N₂) (r₁ + r₂) P := by
  have hP : IsProbabilityMeasure P := (h₁.hasLaw_sub (le_refl 0)).isProbabilityMeasure
  have hmono : ∀ᵐ ω ∂P, ∀ s t, s ≤ t →
      (N₁ + N₂) t ω - (N₁ + N₂) s ω = (N₁ t ω - N₁ s ω) + (N₂ t ω - N₂ s ω) := by
    filter_upwards [h₁.ae_monotone, h₂.ae_monotone] with ω h1 h2 s t hst
    have a1 : N₁ s ω ≤ N₁ t ω := h1 hst
    have a2 : N₂ s ω ≤ N₂ t ω := h2 hst
    simp only [Pi.add_apply]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [h₁.ae_zero, h₂.ae_zero] with ω h1 h2
    simp [h1, h2]
  · filter_upwards [h₁.ae_monotone, h₂.ae_monotone] with ω h1 h2
    exact h1.add h2
  · intro n t ht
    have hφ : Measurable fun (f : ℝ≥0 → ℕ) (i : Fin n) ↦ f (t i.succ) - f (t i.castSucc) :=
      Measurable.of_eval fun i : Fin n ↦ measurable_incr (t i.castSucc) (t i.succ)
    have hvec : IndepFun (fun ω (i : Fin n) ↦ N₁ (t i.succ) ω - N₁ (t i.castSucc) ω)
        (fun ω (i : Fin n) ↦ N₂ (t i.succ) ω - N₂ (t i.castSucc) ω) P :=
      hind.comp hφ hφ
    have hpair := iIndepFun_prodMk
      (A := fun i ω ↦ N₁ (t i.succ) ω - N₁ (t i.castSucc) ω)
      (B := fun i ω ↦ N₂ (t i.succ) ω - N₂ (t i.castSucc) ω)
      (fun i ↦ (h₁.hasLaw_sub (ht (Fin.castSucc_le_succ i))).aemeasurable)
      (fun i ↦ (h₂.hasLaw_sub (ht (Fin.castSucc_le_succ i))).aemeasurable)
      (h₁.hasIndepIncrements n t ht) (h₂.hasIndepIncrements n t ht) hvec
    refine (hpair.comp (fun _ p ↦ p.1 + p.2) fun _ ↦ measurable_of_countable _).congr
      fun i ↦ ?_
    filter_upwards [hmono] with ω hω
    exact (hω _ _ (ht (Fin.castSucc_le_succ i))).symm
  · intro s t hst
    have h := (hind.comp (measurable_incr s t) (measurable_incr s t)).hasLaw_add_poissonMeasure
      (h₁.hasLaw_sub hst) (h₂.hasLaw_sub hst)
    rw [← add_mul] at h
    refine h.congr ?_
    filter_upwards [hmono] with ω hω
    exact hω s t hst

private lemma poisson_binomial_split (r : ℝ≥0) (p : unitInterval) (j k : ℕ) :
    poissonMeasure r {j + k} * binomial (j + k) p {k} =
      poissonMeasure (unitInterval.toNNReal p * r) {k} *
        poissonMeasure (unitInterval.toNNReal (unitInterval.symm p) * r) {j} := by
  rw [poissonMeasure_singleton, binomial_singleton,
    poissonMeasure_singleton, poissonMeasure_singleton,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_mul, unitInterval.coe_toNNReal, unitInterval.symm,
    Nat.add_sub_cancel_right, pow_add, mul_pow]
  rw [show ((j + k).choose k : ℝ) =
      ((j + k).factorial : ℝ) / ((j.factorial : ℝ) * (k.factorial : ℝ)) by
    apply (eq_div_iff (by positivity : ((j.factorial : ℝ) * (k.factorial : ℝ) : ℝ) ≠ 0)).2
    exact_mod_cast (by simpa [mul_assoc] using
      Nat.add_choose_mul_factorial_mul_factorial j k)]
  have he : Real.exp (-(↑p * ↑r)) * Real.exp (-((1 - ↑p) * ↑r)) =
      Real.exp (-(r : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  field_simp

private lemma poisson_binomial_mixture (r : ℝ≥0) (p : unitInterval) (k : ℕ) :
    (∑' m, poissonMeasure r {m} * binomial m p {k}) =
      poissonMeasure (unitInterval.toNNReal p * r) {k} := by
  have hshift :
      (∑' j, poissonMeasure r {j + k} * binomial (j + k) p {k}) =
        ∑' m, poissonMeasure r {m} * binomial m p {k} := by
    apply (show Function.Injective (fun j : ℕ ↦ j + k) from
      fun _ _ h ↦ Nat.add_right_cancel h).tsum_eq
      (f := fun m ↦ poissonMeasure r {m} * binomial m p {k})
    intro m hm
    have hkm : k ≤ m := by
      by_contra hkm
      have hz : binomial m p {k} = 0 := by
        rw [binomial_singleton, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      exact hm (by simp [hz])
    exact ⟨m - k, Nat.sub_add_cancel hkm⟩
  rw [← hshift]
  simp_rw [poisson_binomial_split]
  rw [ENNReal.tsum_mul_left]
  have htotal (q : ℝ≥0) : (∑' j : ℕ, poissonMeasure q {j}) = 1 := by
    rw [← measure_iUnion (by intro i j hij; simpa using hij)
      (fun j ↦ measurableSet_singleton j)]
    rw [show (⋃ i : ℕ, ({i} : Set ℕ)) = Set.univ by ext x; simp]
    exact measure_univ
  rw [htotal, mul_one]

private lemma bool_mark_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (B : Ω → Bool) (p : unitInterval)
    (hm : Measurable B) (hp : P.real {ω | B ω = true} = (p : ℝ)) :
    HasLaw B (bernoulliMeasure true false p) P := by
  refine ⟨hm.aemeasurable, Measure.ext_of_singleton fun b ↦ ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  rw [Measure.map_apply hm (measurableSet_singleton b)]
  change P.real {ω | B ω = b} = (bernoulliMeasure true false p).real {b}
  cases b
  · have hc : {ω | B ω = false} = {ω | B ω = true}ᶜ := by
      ext ω
      cases B ω <;> simp
    rw [hc, measureReal_compl (measurableSet_eq_fun hm measurable_const)]
    simp [hp]
  · simpa using hp

private lemma fixed_marks_binomial {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (B : ℕ → Ω → Bool) (p : unitInterval) (u : Finset ℕ)
    (hm : ∀ i, Measurable (B i)) (hp : ∀ i, P.real {ω | B i ω = true} = (p : ℝ))
    (hi : iIndepFun B P) :
    HasLaw (fun ω ↦ (u.filter fun i ↦ B i ω).card) (binomial u.card p) P := by
  classical
  let X (i : ℕ) (ω : Ω) : Prop := i ∈ u ∧ B i ω = true
  have hmX (i : ℕ) : Measurable (X i) :=
    (Measurable.of_discrete (f := fun b : Bool ↦ i ∈ u ∧ b = true)).comp (hm i)
  have hiX : iIndepFun X P := hi.comp
    (fun i b ↦ i ∈ u ∧ b = true) (fun _ ↦ Measurable.of_discrete)
  have hmapX (i : ℕ) :
      P.map (X i) = bernoulliMeasure (i ∈ u) False p := by
    change P.map ((fun b : Bool ↦ i ∈ u ∧ b = true) ∘ B i) = _
    rw [← Measure.map_map Measurable.of_discrete (hm i),
      (bool_mark_law (B i) p (hm i) (hp i)).map_eq, map_bernoulliMeasure]
    simp
  have hset : HasLaw (fun ω ↦ {i | X i ω}) (setBernoulli (↑u) p) P := by
    have hs : Measurable (fun ω ↦ {i | X i ω}) :=
      MeasurableEquiv.setOfPred.measurable.comp (Measurable.of_eval hmX)
    refine ⟨hs.aemeasurable, ?_⟩
    rw [setBernoulli_eq_map]
    change P.map ((fun f : ℕ → Prop ↦ {i | f i}) ∘ (fun ω i ↦ X i ω)) = _
    rw [← Measure.map_map
      (show Measurable (fun f : ℕ → Prop ↦ {i | f i}) from by fun_prop)
      (Measurable.of_eval hmX),
      hiX.map_fun_eq_infinitePi_map hmX]
    simp_rw [hmapX]
    rfl
  have hn := (hasLaw_map measurable_ncard.aemeasurable).comp hset
  have hcard : (fun ω ↦ (u.filter fun i ↦ B i ω).card) =
      (Set.ncard ∘ (fun ω ↦ {i | X i ω})) := by
    funext ω
    change _ = {i | i ∈ u ∧ B i ω = true}.ncard
    rw [show {i | i ∈ u ∧ B i ω = true} =
      (↑(u.filter fun i ↦ B i ω) : Set ℕ) by ext i; simp]
    exact (Set.ncard_coe_finset _).symm
  rw [hcard]
  convert hn using 1
  apply Measure.ext_of_singleton
  intro k
  rw [map_ncard_setBernoulli_singleton (Finset.finite_toSet u), binomial_singleton,
    Set.ncard_coe_finset]

private lemma disjoint_marks_indep {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : ℕ → Ω → Bool)
    (u : ι → Finset ℕ) (hm : ∀ i, Measurable (B i)) (hi : iIndepFun B P)
    (hu : Pairwise (fun i j ↦ Disjoint (u i) (u j))) :
    iIndepFun (fun i ω ↦ ((u i).filter fun j ↦ B j ω).card) P := by
  classical
  let f (x : (i : ι) × (u i)) : ℕ := x.2
  have hf : Function.Injective f := by
    rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ hab
    change a = b at hab
    subst b
    have hij : i = j := by
      by_contra hij
      exact (Finset.disjoint_left.1 (hu hij)) ha hb
    subst j
    rfl
  have hflat := hi.precomp hf
  have hmflat (x : (i : ι) × (u i)) : Measurable (B (f x)) := hm _
  let e := MeasurableEquiv.piCurry (fun (i : ι) (_ : u i) ↦ Bool)
  have hgroup : iIndepFun (fun i ω (j : u i) ↦ B j ω) P := by
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun i ↦ Measurable.of_eval fun (j : u i) ↦ hm j)).2
    calc
      P.map (fun ω i (j : u i) ↦ B j ω) =
          (P.map (fun ω (x : (i : ι) × (u i)) ↦ B (f x) ω)).map e := by
        rw [Measure.map_map e.measurable (Measurable.of_eval hmflat)]
        rfl
      _ = Measure.infinitePi (fun i ↦ Measure.infinitePi
          (fun j : u i ↦ P.map (B j))) := by
        rw [hflat.map_fun_eq_infinitePi_map hmflat]
        simpa [e, f] using Measure.infinitePi_map_piCurry
          (fun i (j : u i) ↦ P.map (B j))
      _ = Measure.infinitePi (fun i ↦ P.map (fun ω (j : u i) ↦ B j ω)) := by
        congr 1
        funext i
        exact ((hi.precomp (Subtype.val_injective : Function.Injective
          (fun j : u i ↦ (j : ℕ)))).map_fun_eq_infinitePi_map (fun (j : u i) ↦ hm (j : ℕ))).symm
  have hcount := hgroup.comp
    (fun i (b : u i → Bool) ↦ ∑ j : u i, if b j then 1 else 0)
    (fun i ↦ Measurable.of_discrete)
  convert hcount using 1
  funext i ω
  simp only [Function.comp_apply, Finset.card_filter]
  exact (Finset.sum_coe_sort (u i) (fun j ↦ if B j ω then 1 else 0)).symm

private lemma marked_count_measurable (u : Finset ℕ) :
    Measurable (fun b : ℕ → Bool ↦ (u.filter fun i ↦ b i).card) := by
  simp only [Finset.card_filter]
  exact u.measurable_sum fun i _ ↦
    (Measurable.of_discrete (f := fun b : Bool ↦ if b then (1 : ℕ) else 0)).comp
      (measurable_pi_apply i)

private lemma lintegral_prod_indep_ae {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} (f : ι → Ω → ℝ≥0∞) (hm : ∀ i, AEMeasurable (f i) P)
    (hi : iIndepFun f P) :
    (∫⁻ ω, ∏ i, f i ω ∂P) = ∏ i, ∫⁻ ω, f i ω ∂P := by
  classical
  let g i := (hm i).mk (f i)
  have hg (i : ι) : Measurable (g i) := (hm i).measurable_mk
  have hie : iIndepFun g P := hi.congr fun i ↦ (hm i).ae_eq_mk
  have he : (fun ω ↦ ∏ i, f i ω) =ᵐ[P] (fun ω ↦ ∏ i, g i ω) := by
    filter_upwards [MeasureTheory.ae_all_iff.2 (fun i ↦ (hm i).ae_eq_mk)] with ω hω
    exact Finset.prod_congr rfl fun i _ ↦ hω i
  rw [lintegral_congr_ae he, lintegral_prod_eq_prod_lintegral_of_indepFun
    Finset.univ g hie hg]
  exact Finset.prod_congr rfl fun i _ ↦
    (lintegral_congr_ae (hm i).ae_eq_mk).symm

private lemma random_blocks_poisson {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (n : ℕ)
    (X : Ω → Fin (n + 1) → ℕ) (B : ℕ → Ω → Bool) (p : unitInterval)
    (rates : Fin n → ℝ≥0) (hmX : AEMeasurable X P)
    (hmB : ∀ i, Measurable (B i)) (hpB : ∀ i, P.real {ω | B i ω = true} = (p : ℝ))
    (hiB : iIndepFun B P) (hXB : IndepFun X (fun ω i ↦ B i ω) P)
    (hmono : ∀ᵐ ω ∂P, Monotone (X ω))
    (hD : ∀ i : Fin n, HasLaw (fun ω ↦ X ω i.succ - X ω i.castSucc)
      (poissonMeasure (rates i)) P)
    (hiD : iIndepFun (fun (i : Fin n) ω ↦ X ω i.succ - X ω i.castSucc) P) :
    HasLaw (fun ω (i : Fin n) ↦
      ((Finset.Ico (X ω i.castSucc) (X ω i.succ)).filter fun j ↦ B j ω).card)
      (Measure.pi fun i ↦ poissonMeasure (unitInterval.toNNReal p * rates i)) P := by
  classical
  let C (x : (Fin (n + 1) → ℕ) × (ℕ → Bool)) (i : Fin n) : ℕ :=
    ((Finset.Ico (x.1 i.castSucc) (x.1 i.succ)).filter fun j ↦ x.2 j).card
  have hmC : Measurable C := measurable_from_prod_countable_right fun c ↦
    Measurable.of_eval fun (i : Fin n) ↦ by
      simpa only [C] using marked_count_measurable (Finset.Ico (c i.castSucc) (c i.succ))
  have hmBs : Measurable (fun ω i ↦ B i ω) := Measurable.of_eval hmB
  have hmPair := hmX.prodMk hmBs.aemeasurable
  have hmRet := hmC.comp_aemeasurable hmPair
  refine ⟨hmRet, ?_⟩
  change P.map (C ∘ (fun ω ↦ (X ω, fun i ↦ B i ω))) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hmC.aemeasurable hmPair,
    hXB.map_prod_eq_prod_map_map hmX hmBs.aemeasurable]
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.map_apply hmC (measurableSet_singleton y),
    Measure.prod_apply (hmC (measurableSet_singleton y)), Measure.pi_singleton]
  have hcAE : ∀ᵐ c ∂P.map X, Monotone c :=
    (ae_map_iff hmX (MeasurableSet.of_discrete)).2 hmono
  have hcond :
      (∫⁻ c, (P.map (fun ω i ↦ B i ω))
        (Prod.mk c ⁻¹' (C ⁻¹' {y})) ∂P.map X) =
      ∫⁻ c, ∏ i : Fin n, binomial (c i.succ - c i.castSucc) p {y i} ∂P.map X := by
    apply lintegral_congr_ae
    filter_upwards [hcAE] with c hc
    let u (i : Fin n) := Finset.Ico (c i.castSucc) (c i.succ)
    have hu : Pairwise (fun i j ↦ Disjoint (u i) (u j)) := by
      intro i j hij
      apply Finset.disjoint_left.2
      intro k hki hkj
      simp only [u, Finset.mem_Ico] at hki hkj
      rcases lt_or_gt_of_ne hij with hij | hij
      · have hle := hc (show i.succ ≤ j.castSucc by
          change i.val + 1 ≤ j.val
          exact Nat.succ_le_of_lt hij)
        omega
      · have hle := hc (show j.succ ≤ i.castSucc by
          change j.val + 1 ≤ i.val
          exact Nat.succ_le_of_lt hij)
        omega
    have hfixed (i : Fin n) := fixed_marks_binomial B p (u i) hmB hpB hiB
    have hfixedMap := (disjoint_marks_indep B u hmB hiB hu).map_fun_eq_pi_map
      (fun i ↦ (hfixed i).aemeasurable)
    simp_rw [(hfixed _).map_eq] at hfixedMap
    rw [Measure.map_apply hmBs
      (show MeasurableSet (Prod.mk c ⁻¹' (C ⁻¹' {y})) from
        (hmC (measurableSet_singleton y)).preimage
          (measurable_const.prodMk measurable_id))]
    change P ((fun ω i ↦ ((u i).filter fun j ↦ B j ω).card) ⁻¹' {y}) = _
    rw [← Measure.map_apply_of_aemeasurable
      (AEMeasurable.of_eval fun i ↦ (hfixed i).aemeasurable)
      (measurableSet_singleton y), hfixedMap, Measure.pi_singleton]
    simp only [u, Nat.card_Ico]
  rw [hcond, lintegral_map' Measurable.of_discrete.aemeasurable hmX]
  let f (i : Fin n) (ω : Ω) :=
    binomial (X ω i.succ - X ω i.castSucc) p {y i}
  have hmf (i : Fin n) : AEMeasurable (f i) P := by
    simpa only [f, Function.comp_def] using
      (Measurable.of_discrete (f := fun m : ℕ ↦ binomial m p {y i})).comp_aemeasurable
        (hD i).aemeasurable
  have hif : iIndepFun f P :=
    hiD.comp (fun i m ↦ binomial m p {y i}) (fun _ ↦ Measurable.of_discrete)
  rw [lintegral_prod_indep_ae f hmf hif]
  apply Finset.prod_congr rfl
  intro i _
  change (∫⁻ ω, binomial (X ω i.succ - X ω i.castSucc) p {y i} ∂P) = _
  rw [(hD i).lintegral_comp
    (Measurable.of_discrete (f := fun m : ℕ ↦ binomial m p {y i})).aemeasurable,
    lintegral_countable']
  simpa only [mul_comm] using poisson_binomial_mixture (rates i) p (y i)

private lemma marked_prefix_sub (B : ℕ → Bool) {a b : ℕ} (hab : a ≤ b) :
    ((Finset.range b).filter fun i ↦ B i).card -
      ((Finset.range a).filter fun i ↦ B i).card =
      ((Finset.Ico a b).filter fun i ↦ B i).card := by
  rw [← Finset.card_sdiff_of_subset
    (Finset.filter_subset_filter _ (Finset.range_mono hab))]
  congr 1
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  by_cases hBi : B i = true <;> simp [hBi, not_lt, and_comm]

/-- The thinning of `N` by the marks `B`: the number of indices `i < N t` with `B i`, i.e. the
number of points of `N` in `[0, t]` that are kept when the `i`-th point (in time order, from
`0`) is kept iff `B i`. -/
noncomputable def PoissonProcess.thinning (N : ℝ≥0 → Ω → ℕ) (B : ℕ → Ω → Bool) (t : ℝ≥0)
    (ω : Ω) : ℕ :=
  ((Finset.range (N t ω)).filter fun i ↦ B i ω).card

private lemma thinned_vector_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : ℝ≥0 → Ω → ℕ} {r p : ℝ≥0}
    {B : ℕ → Ω → Bool} (hN : IsPoissonProcess N r P) (hp : p ≤ 1)
    (hmB : ∀ i, Measurable (B i)) (hpB : ∀ i, P.real {ω | B i ω = true} = p)
    (hiB : iIndepFun B P) (hNB : IndepFun (fun ω t ↦ N t ω) (fun ω i ↦ B i ω) P)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    HasLaw (fun ω (i : Fin n) ↦
      PoissonProcess.thinning N B (t i.succ) ω - PoissonProcess.thinning N B (t i.castSucc) ω)
      (Measure.pi fun i ↦ poissonMeasure ((p * r) * (t i.succ - t i.castSucc))) P := by
  let q : unitInterval := ⟨(p : ℝ), p.2, by exact_mod_cast hp⟩
  have hq : unitInterval.toNNReal q = p := Subtype.ext rfl
  have hmN (s : ℝ≥0) : AEMeasurable (N s) P := by
    apply (hN.hasLaw_sub (s := 0) (t := s) bot_le).aemeasurable.congr
    filter_upwards [hN.ae_zero] with ω hω
    simp [hω]
  have hl := random_blocks_poisson n (fun ω i ↦ N (t i) ω) B q
    (fun i ↦ r * (t i.succ - t i.castSucc)) (AEMeasurable.of_eval fun i ↦ hmN (t i))
    hmB hpB hiB
    (hNB.comp (Measurable.of_eval fun i ↦ measurable_pi_apply (t i)) measurable_id)
    (by
      filter_upwards [hN.ae_monotone] with ω hω
      exact hω.comp ht)
    (fun i ↦ hN.hasLaw_sub (ht i.castSucc_le_succ))
    (hN.hasIndepIncrements n t ht)
  rw [hq] at hl
  simp only [← mul_assoc] at hl
  apply hl.congr
  filter_upwards [hN.ae_monotone] with ω hω
  funext i
  exact marked_prefix_sub (fun j ↦ B j ω) (hω (ht i.castSucc_le_succ))

/-- **Thinning** (Kingman 1993, §5.1; Karlin–Taylor 1975, §4.1): keeping each point of a Poisson
process of rate `r` independently with probability `p`, independently of the process, gives a
Poisson process of rate `p r`. The marks `B i` are i.i.d. with `P(B i) = p` and independent of
`N` as a random path. -/
theorem IsPoissonProcess.thinning {N : ℝ≥0 → Ω → ℕ} {r p : ℝ≥0} {B : ℕ → Ω → Bool}
    [IsProbabilityMeasure P] (hN : IsPoissonProcess N r P) (hp : p ≤ 1)
    (hBm : ∀ i, Measurable (B i)) (hB : ∀ i, P.real {ω | B i ω = true} = p)
    (hBind : iIndepFun B P) (hNB : IndepFun (fun ω t ↦ N t ω) (fun ω i ↦ B i ω) P) :
    IsPoissonProcess (PoissonProcess.thinning N B) (p * r) P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hN.ae_zero] with ω hω
    simp [PoissonProcess.thinning, hω]
  · filter_upwards [hN.ae_monotone] with ω hω
    intro s t hst
    exact Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.range_mono (hω hst)))
  · intro n t ht
    have hl := thinned_vector_law hN hp hBm hB hBind hNB n t ht
    have hiLaw (i : Fin n) :=
      (measurePreserving_eval
        (fun (i : Fin n) ↦ poissonMeasure ((p * r) * (t i.succ - t i.castSucc)))
        i).fun_comp_hasLaw hl
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hiLaw i).aemeasurable)).2
    rw [hl.map_eq]
    congr 1
    funext i
    exact (hiLaw i).map_eq.symm
  · intro s t hst
    let ts : Fin 2 → ℝ≥0 := ![s, t]
    have hts : Monotone ts := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [ts]
    have hl := thinned_vector_law hN hp hBm hB hBind hNB 1 ts hts
    have hl0 := (measurePreserving_eval
      (fun (i : Fin 1) ↦ poissonMeasure ((p * r) * (ts i.succ - ts i.castSucc)))
      (0 : Fin 1)).fun_comp_hasLaw hl
    simpa [ts] using hl0

/-! ### Exponential interarrivals give a Poisson process

The joint law of the counts is computed on the canonical space `ℕ → ℝ` of interarrival sequences
with the i.i.d. product law. For a list of blocks `(u₁, k₁), …, (uₙ, kₙ)`, the event that exactly
`k₁ + ⋯ + k_j` arrivals lie in `[0, u₁ + ⋯ + u_j]` for every `j` has probability
`∏ Poisson(r u_j){k_j}`. The proof conditions on the first interarrival time `a`: if the first
block has `k₁ = 0`, memorylessness (`a > u₁` and `a - u₁` is again exponential) removes the block;
if `k₁ > 0`, removing the first arrival lowers `k₁` by one and shortens the block to `u₁ - a`, and
the convolution `∫₀^u r e^{-ra} Poisson(r (u - a)){m} da = Poisson(r u){m + 1}` closes the
induction. -/

namespace PoissonProcess

/-- The i.i.d. product of rate-`r` exponential laws on sequences `ℕ → ℝ`. -/
private noncomputable abbrev expSeq (r : ℝ≥0) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ expMeasure r

/-- `seqCons a y` prepends `a` to the sequence `y`. -/
private def seqCons (a : ℝ) (y : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | i + 1 => y i

/-- `InGaps x s m L` for `L = [(u₁, k₁), …, (uₙ, kₙ)]`: for every `j`, with
`t_j = s + u₁ + ⋯ + u_j` and `K_j = m + k₁ + ⋯ + k_j`, the partial sums of `x` satisfy
`x 0 + ⋯ + x (K_j - 1) ≤ t_j < x 0 + ⋯ + x K_j`. -/
private def InGaps (x : ℕ → ℝ) : ℝ → ℕ → List (ℝ≥0 × ℕ) → Prop
  | _, _, [] => True
  | s, m, p :: L =>
      (∑ i ∈ Finset.range (m + p.2), x i ≤ s + p.1 ∧
        s + p.1 < ∑ i ∈ Finset.range (m + p.2 + 1), x i) ∧ InGaps x (s + p.1) (m + p.2) L


private theorem lintegral_poisson_step {r : ℝ≥0} (hr : 0 < r) (u : ℝ≥0) (m : ℕ) :
    ∫⁻ a, {a : ℝ | a ≤ u}.indicator
        (fun a ↦ poissonMeasure (r * Real.toNNReal (u - a)) {m}) a ∂expMeasure r =
      poissonMeasure (r * u) {m + 1} := by
  have hr' : (0 : ℝ) < r := hr
  have hpois : (fun a : ℝ ↦ poissonMeasure (r * Real.toNNReal (u - a)) {m}) = fun a ↦
      ENNReal.ofReal (Real.exp (-(r * Real.toNNReal (u - a) : ℝ)) *
        ((r * Real.toNNReal (u - a) : ℝ≥0) : ℝ) ^ m / (m.factorial : ℝ)) := by
    funext a
    rw [poissonMeasure_singleton]
    push_cast
    rfl
  have hmeas : Measurable fun a : ℝ ↦ {a : ℝ | a ≤ u}.indicator
      (fun a ↦ poissonMeasure (r * Real.toNNReal (u - a)) {m}) a := by
    refine Measurable.indicator ?_ (measurableSet_le measurable_id measurable_const)
    rw [hpois]
    fun_prop
  have hint : ∀ a : ℝ, gammaPDF 1 r a * {a : ℝ | a ≤ u}.indicator
      (fun a ↦ poissonMeasure (r * Real.toNNReal (u - a)) {m}) a =
      (Icc 0 (u : ℝ)).indicator (fun a ↦ ENNReal.ofReal
        (r ^ (m + 1) * Real.exp (-(r * u)) / (m.factorial : ℝ) * (u - a) ^ m)) a := by
    intro a
    by_cases ha : 0 ≤ a
    · by_cases hau : a ≤ u
      · rw [indicator_of_mem (show a ∈ {a : ℝ | a ≤ u} from hau),
          indicator_of_mem (show a ∈ Icc 0 (u : ℝ) from ⟨ha, hau⟩), poissonMeasure_singleton]
        change exponentialPDF r a * _ = _
        rw [exponentialPDF_of_nonneg ha, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sub_nonneg.mpr hau)]
        have he : Real.exp (-(r * a)) * Real.exp (-(r * (u - a))) = Real.exp (-(r * u)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← he, mul_pow, pow_succ]
        field_simp
      · rw [indicator_of_notMem (show a ∉ {a : ℝ | a ≤ u} from hau),
          indicator_of_notMem (fun h ↦ hau h.2), mul_zero]
    · rw [gammaPDF_of_neg (lt_of_not_ge ha), zero_mul,
        indicator_of_notMem (fun h ↦ ha h.1)]
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
    (by unfold gammaPDF; fun_prop) hmeas]
  simp only [Pi.mul_apply]
  simp_rw [hint]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun a : ℝ ↦
      r ^ (m + 1) * Real.exp (-(r * u)) / (m.factorial : ℝ) * (u - a) ^ m).integrableOn_Icc)]
  · rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le u.coe_nonneg,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ m), integral_pow,
      poissonMeasure_singleton]
    congr 1
    simp only [sub_self, sub_zero, zero_pow (Nat.succ_ne_zero m), NNReal.coe_mul,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [mul_pow, pow_succ]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    have : 0 ≤ (u : ℝ) - a := sub_nonneg.mpr ha.2
    positivity

private theorem lintegral_memoryless {r : ℝ≥0} (hr : 0 < r) (u : ℝ≥0) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ a, (Ioi (u : ℝ)).indicator (fun a ↦ g (a - u)) a ∂expMeasure r =
      ENNReal.ofReal (Real.exp (-(r * u))) * ∫⁻ a, g a ∂expMeasure r := by
  have hr' : (0 : ℝ) < r := hr
  have hpdf : Measurable (gammaPDF 1 r) := by unfold gammaPDF; fun_prop
  have hint : ∀ a : ℝ, gammaPDF 1 r a * (Ioi (u : ℝ)).indicator (fun a ↦ g (a - u)) a =
      ENNReal.ofReal (Real.exp (-(r * u))) *
        (Ioi (0 : ℝ)).indicator (fun b ↦ gammaPDF 1 r b * g b) (a - u) := by
    intro a
    by_cases hau : (u : ℝ) < a
    · rw [indicator_of_mem (show a ∈ Ioi (u : ℝ) from hau),
        indicator_of_mem (show a - u ∈ Ioi (0 : ℝ) from sub_pos.mpr hau)]
      change exponentialPDF r a * _ = _ * (exponentialPDF r (a - u) * _)
      rw [exponentialPDF_of_nonneg (by linarith [u.coe_nonneg]),
        exponentialPDF_of_nonneg (by linarith), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have he : Real.exp (-(r * u)) * Real.exp (-(r * (a - u))) = Real.exp (-(r * a)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← he]
      ring
    · rw [indicator_of_notMem (show a ∉ Ioi (u : ℝ) from hau),
        indicator_of_notMem (show a - u ∉ Ioi (0 : ℝ) from fun h ↦ hau (sub_pos.mp h)),
        mul_zero, mul_zero]
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hpdf
    (show Measurable fun a ↦ (Ioi (u : ℝ)).indicator (fun a ↦ g (a - u)) a from
      (hg.comp (measurable_id.sub_const _)).indicator measurableSet_Ioi),
    lintegral_withDensity_eq_lintegral_mul _ hpdf hg]
  simp only [Pi.mul_apply]
  simp_rw [hint]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sub_right_eq_self
      (fun b ↦ (Ioi (0 : ℝ)).indicator (fun b ↦ gammaPDF 1 r b * g b) b) (u : ℝ)]
  congr 1
  apply lintegral_congr_ae
  have h0 : ∀ᵐ b : ℝ ∂volume, b ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with b hb
  by_cases hb' : 0 < b
  · rw [indicator_of_mem (show b ∈ Ioi (0 : ℝ) from hb')]
  · rw [indicator_of_notMem (show b ∉ Ioi (0 : ℝ) from hb'),
      gammaPDF_of_neg (lt_of_le_of_ne (not_lt.mp hb') hb), zero_mul]

private theorem map_seqCons_expSeq {r : ℝ≥0} (hr : 0 < r) :
    ((expMeasure r).prod (expSeq r)).map (fun p ↦ seqCons p.1 p.2) = expSeq r := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) ↦ seqCons p.1 p.2) := by
    rw [measurable_pi_iff]
    intro i
    cases i with
    | zero => exact measurable_fst
    | succ i => exact (measurable_pi_apply i).comp measurable_snd
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  classical
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range (N + 1) :=
    ⟨s.sup id, fun i hi ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
  set t' : ℕ → Set ℝ := fun i ↦ if i ∈ s then t i else univ with ht'
  have hmt' : ∀ i, MeasurableSet (t' i) := by
    intro i
    simp only [ht']
    split_ifs
    exacts [ht i, .univ]
  have hpi : Set.pi (s : Set ℕ) t = Set.pi (Finset.range (N + 1) : Set ℕ) t' := by
    ext x
    simp only [Set.mem_pi, Finset.mem_coe, ht']
    constructor
    · intro h i _
      split_ifs with hi
      exacts [h i hi, trivial]
    · intro h i hi
      simpa [hi] using h i (hN hi)
  have hprod : ∏ i ∈ s, expMeasure r (t i) =
      ∏ i ∈ Finset.range (N + 1), expMeasure r (t' i) := by
    rw [← Finset.prod_subset hN]
    · exact Finset.prod_congr rfl fun i hi ↦ by simp [ht', hi]
    · intro i _ hi
      simp [ht', hi]
  rw [hpi, hprod, Measure.map_apply hm (MeasurableSet.pi (Finset.countable_toSet _)
    fun i _ ↦ hmt' i)]
  have hpre : (fun p : ℝ × (ℕ → ℝ) ↦ seqCons p.1 p.2) ⁻¹'
      Set.pi (Finset.range (N + 1) : Set ℕ) t' =
      t' 0 ×ˢ Set.pi (Finset.range N : Set ℕ) (fun i ↦ t' (i + 1)) := by
    ext ⟨a, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_prod]
    constructor
    · intro h
      exact ⟨h 0 (Nat.succ_pos N), fun i hi ↦ h (i + 1) (by omega)⟩
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact h i (by omega)
  have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure (r : ℝ)) i) := fun _ ↦ this
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi (μ := fun _ : ℕ ↦ expMeasure (r : ℝ))
    (mt := fun i _ ↦ hmt' (i + 1)),
    Finset.prod_range_succ', mul_comm]

private theorem measurableSet_inGaps (s : ℝ) (m : ℕ) (L : List (ℝ≥0 × ℕ)) :
    MeasurableSet {x : ℕ → ℝ | InGaps x s m L} := by
  induction L generalizing s m with
  | nil => simp [InGaps]
  | cons p L ih =>
    simp only [InGaps, ofPred_and]
    refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) (ih _ _)
    · exact measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)
        measurable_const
    · exact measurableSet_lt measurable_const
        (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)

private lemma sum_range_succ_tail (x : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), x i = x 0 + ∑ i ∈ Finset.range n, x (i + 1) := by
  rw [Finset.sum_range_succ', add_comm]

private theorem inGaps_succ_iff (x : ℕ → ℝ) (s : ℝ) (m : ℕ) (L : List (ℝ≥0 × ℕ)) :
    InGaps x s (m + 1) L ↔ InGaps (fun i ↦ x (i + 1)) (s - x 0) m L := by
  induction L generalizing s m with
  | nil => simp [InGaps]
  | cons p L ih =>
    simp only [InGaps]
    rw [show m + 1 + p.2 = m + p.2 + 1 by omega, ih, sum_range_succ_tail,
      show m + p.2 + 1 + 1 = (m + p.2 + 1) + 1 by omega, sum_range_succ_tail x (m + p.2 + 1),
      show s + p.1 - x 0 = s - x 0 + p.1 by ring]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩

private lemma sum_seqCons (x : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), seqCons (x 0 - c) (fun i ↦ x (i + 1)) i =
      ∑ i ∈ Finset.range (n + 1), x i - c := by
  rw [sum_range_succ_tail, sum_range_succ_tail]
  simp only [seqCons]
  ring

private theorem inGaps_offset (x : ℕ → ℝ) {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') (m : ℕ)
    (L : List (ℝ≥0 × ℕ)) :
    InGaps x (s + s') m L ↔ InGaps (seqCons (x 0 - s) fun i ↦ x (i + 1)) s' m L := by
  induction L generalizing s' m with
  | nil => simp [InGaps]
  | cons p L ih =>
    have hp : (0 : ℝ) ≤ p.1 := p.1.coe_nonneg
    simp only [InGaps]
    rw [show s + s' + p.1 = s + (s' + p.1) by ring, ih (by positivity), sum_seqCons]
    have hlow : (∑ i ∈ Finset.range (m + p.2), x i ≤ s + (s' + p.1)) ↔
        (∑ i ∈ Finset.range (m + p.2), seqCons (x 0 - s) (fun i ↦ x (i + 1)) i ≤ s' + p.1) := by
      rcases Nat.eq_zero_or_eq_succ_pred (m + p.2) with h | h
      · rw [h]
        simp only [Finset.range_zero, Finset.sum_empty]
        constructor <;> intro <;> positivity
      · rw [h, sum_seqCons]
        constructor <;> intro <;> linarith
    rw [hlow]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by linarith⟩, h3⟩


private lemma measurable_poisson_indicator (r u : ℝ≥0) (m : ℕ) :
    Measurable fun a : ℝ ↦ {a : ℝ | a ≤ u}.indicator
      (fun a ↦ poissonMeasure (r * Real.toNNReal (u - a)) {m}) a := by
  refine Measurable.indicator ?_ (measurableSet_le measurable_id measurable_const)
  have hpois : (fun a : ℝ ↦ poissonMeasure (r * Real.toNNReal (u - a)) {m}) = fun a ↦
      ENNReal.ofReal (Real.exp (-(r * Real.toNNReal (u - a) : ℝ)) *
        ((r * Real.toNNReal (u - a) : ℝ≥0) : ℝ) ^ m / (m.factorial : ℝ)) := by
    funext a
    rw [poissonMeasure_singleton]
    push_cast
    rfl
  rw [hpois]
  fun_prop

private lemma measurable_seqCons :
    Measurable (fun p : ℝ × (ℕ → ℝ) ↦ seqCons p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  cases i with
  | zero => exact measurable_fst
  | succ i => exact (measurable_pi_apply i).comp measurable_snd

private lemma expSeq_eq_lintegral {r : ℝ≥0} (hr : 0 < r) {A : Set (ℕ → ℝ)}
    (hA : MeasurableSet A) :
    expSeq r A = ∫⁻ a, expSeq r {y | seqCons a y ∈ A} ∂expMeasure r := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure (r : ℝ)) i) := fun _ ↦ this
  conv_lhs => rw [← map_seqCons_expSeq hr]
  rw [Measure.map_apply measurable_seqCons hA, Measure.prod_apply (measurable_seqCons hA)]
  rfl

private lemma measurable_expSeq_seqCons {r : ℝ≥0} (hr : 0 < r) {A : Set (ℕ → ℝ)}
    (hA : MeasurableSet A) : Measurable fun a ↦ expSeq r {y | seqCons a y ∈ A} := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure (r : ℝ)) i) := fun _ ↦ this
  exact measurable_measure_prodMk_left (measurable_seqCons hA)

private lemma ae_expSeq_nonneg {r : ℝ≥0} (hr : 0 < r) : ∀ᵐ y ∂expSeq r, ∀ i, 0 ≤ y i := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  rw [ae_all_iff]
  intro i
  have hm : (expSeq r).map (fun y ↦ y i) = expMeasure r :=
    Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure (r : ℝ)) i
  have h0 : ∀ᵐ x ∂expMeasure r, 0 ≤ x := ae_nonneg_exp (r : ℝ)
  rw [← hm] at h0
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h0

private lemma inGaps_seqCons_succ (a : ℝ) (y : ℕ → ℝ) (u : ℝ≥0) (m : ℕ)
    (L : List (ℝ≥0 × ℕ)) :
    InGaps (seqCons a y) 0 0 ((u, m + 1) :: L) ↔ InGaps y (-a) 0 ((u, m) :: L) := by
  have hz : ∀ n, ∑ i ∈ Finset.range (n + 1), seqCons a y i = a + ∑ i ∈ Finset.range n, y i :=
    fun n ↦ sum_range_succ_tail _ n
  simp only [InGaps, zero_add]
  rw [hz, hz, inGaps_succ_iff]
  change ((a + _ ≤ (u : ℝ) ∧ (u : ℝ) < a + _) ∧ InGaps y ((u : ℝ) - a) m L) ↔ _
  rw [show (u : ℝ) - a = -a + u by ring]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h3⟩

private lemma inGaps_neg_offset {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (a : ℝ) (u : ℝ≥0) (m : ℕ)
    (L : List (ℝ≥0 × ℕ)) :
    InGaps y (-a) 0 ((u, m) :: L) ↔
      a ≤ u ∧ InGaps y 0 0 ((Real.toNNReal (u - a), m) :: L) := by
  by_cases hau : a ≤ u
  · have he : ((Real.toNNReal (u - a) : ℝ≥0) : ℝ) = u - a :=
      Real.coe_toNNReal _ (sub_nonneg.mpr hau)
    simp only [InGaps, he, hau, true_and]
    rw [show (0 : ℝ) + (u - a) = -a + u by ring]
  · simp only [hau, false_and, iff_false, InGaps]
    rintro ⟨⟨h1, _⟩, _⟩
    have : 0 ≤ ∑ i ∈ Finset.range (0 + m), y i := Finset.sum_nonneg fun i _ ↦ hy i
    exact hau (by linarith)

private theorem expSeq_inGaps {r : ℝ≥0} (hr : 0 < r) (L : List (ℝ≥0 × ℕ)) :
    expSeq r {x | InGaps x 0 0 L} = (L.map fun p ↦ poissonMeasure (r * p.1) {p.2}).prod := by
  have hP := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure (r : ℝ)) i) := fun _ ↦ hP
  induction L with
  | nil => simp [InGaps]
  | cons p L ih =>
    obtain ⟨u, k⟩ := p
    simp only [List.map_cons, List.prod_cons]
    induction k generalizing u with
    | zero =>
      have hset : {x | InGaps x 0 0 ((u, 0) :: L)} =
          {x | (u : ℝ) < x 0 ∧ InGaps (seqCons (x 0 - u) fun i ↦ x (i + 1)) 0 0 L} := by
        ext x
        have h := inGaps_offset x u.coe_nonneg le_rfl 0 L
        rw [add_zero] at h
        simp only [InGaps, mem_ofPred_eq, add_zero, zero_add, Finset.range_zero,
          Finset.sum_empty, Finset.sum_range_one, h, u.coe_nonneg, true_and]
      have hA := measurableSet_inGaps 0 0 L
      have hint : ∀ a, expSeq r {y | seqCons a y ∈ {x | (u : ℝ) < x 0 ∧
          InGaps (seqCons (x 0 - u) fun i ↦ x (i + 1)) 0 0 L}} =
          (Ioi (u : ℝ)).indicator (fun a ↦ expSeq r {y | seqCons (a - u) y ∈
            {x | InGaps x 0 0 L}}) a := by
        intro a
        by_cases ha : (u : ℝ) < a
        · rw [indicator_of_mem (show a ∈ Ioi (u : ℝ) from ha)]
          congr 1
          ext y
          change (u : ℝ) < a ∧ InGaps (seqCons (a - u) y) 0 0 L ↔ _
          simp only [ha, true_and]
          rfl
        · rw [indicator_of_notMem (show a ∉ Ioi (u : ℝ) from ha)]
          convert measure_empty (μ := expSeq r)
          ext y
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          exact fun h ↦ absurd h ha
      rw [hset, expSeq_eq_lintegral hr (by rw [← hset]; exact measurableSet_inGaps 0 0 _)]
      simp_rw [hint]
      rw [lintegral_memoryless hr u (g := fun b ↦ expSeq r {y | seqCons b y ∈
        {x | InGaps x 0 0 L}}) (measurable_expSeq_seqCons hr hA), ← expSeq_eq_lintegral hr hA,
        ih, poissonMeasure_singleton]
      simp
    | succ m ihm =>
      have hA := measurableSet_inGaps 0 0 ((u, m + 1) :: L)
      rw [expSeq_eq_lintegral hr hA]
      have hint : ∀ a, expSeq r {y | seqCons a y ∈ {x | InGaps x 0 0 ((u, m + 1) :: L)}} =
          {a : ℝ | a ≤ u}.indicator
            (fun a ↦ poissonMeasure (r * Real.toNNReal (u - a)) {m}) a *
            (L.map fun p ↦ poissonMeasure (r * p.1) {p.2}).prod := by
        intro a
        have hcongr : expSeq r {y | seqCons a y ∈ {x | InGaps x 0 0 ((u, m + 1) :: L)}} =
            expSeq r {y | a ≤ u ∧ InGaps y 0 0 ((Real.toNNReal (u - a), m) :: L)} := by
          apply measure_congr
          filter_upwards [ae_expSeq_nonneg hr] with y hy
          apply propext
          rw [inGaps_seqCons_succ, inGaps_neg_offset hy]
        rw [hcongr]
        by_cases hau : a ≤ (u : ℝ)
        · rw [indicator_of_mem (show a ∈ {a : ℝ | a ≤ u} from hau)]
          simp only [hau, true_and]
          exact ihm _
        · rw [indicator_of_notMem (show a ∉ {a : ℝ | a ≤ u} from hau), zero_mul]
          simp [hau]
      simp_rw [hint]
      rw [lintegral_mul_const _ (measurable_poisson_indicator r u m),
        lintegral_poisson_step hr u m]

/-- Along the list `L`, the path `c` takes the values `m + k₁ + ⋯ + k_j` at the times
`s + u₁ + ⋯ + u_j`. -/
private def CountsAlong (c : ℝ≥0 → ℕ) : ℝ≥0 → ℕ → List (ℝ≥0 × ℕ) → Prop
  | _, _, [] => True
  | s, m, p :: L => c (s + p.1) = m + p.2 ∧ CountsAlong c (s + p.1) (m + p.2) L

private lemma countsAlong_ofFn {c : ℝ≥0 → ℕ} (hc : Monotone c) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ (k : Fin n → ℕ),
    (CountsAlong c (t 0) (c (t 0)) (List.ofFn fun i ↦ (t i.succ - t i.castSucc, k i)) ↔
      ∀ i, c (t i.succ) - c (t i.castSucc) = k i)
  | 0, t, _, k => by simp [CountsAlong]
  | n + 1, t, ht, k => by
    rw [List.ofFn_succ, Fin.forall_fin_succ]
    simp only [CountsAlong, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    have h01 : t 0 ≤ t 1 := ht (Fin.zero_le _)
    have hc01 : c (t 0) ≤ c (t 1) := hc h01
    rw [add_tsub_cancel_of_le h01]
    have ih := countsAlong_ofFn hc n (fun i ↦ t i.succ)
      (fun i j hij ↦ ht (Fin.succ_le_succ_iff.2 hij)) (fun i ↦ k i.succ)
    simp only [Fin.succ_zero_eq_one] at ih
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rw [← h1] at h2
      exact ih.1 h2
    · rintro ⟨h1, h2⟩
      have h1' : c (t 1) = c (t 0) + k 0 := by omega
      refine ⟨h1', ?_⟩
      rw [← h1']
      exact ih.2 h2

private lemma count_eq_iff {T : ℕ → Ω → ℝ} {ω : Ω} (hpos : ∀ i, 0 < T i ω)
    (htend : Filter.Tendsto (fun n ↦ arrivalTime T n ω) Filter.atTop Filter.atTop)
    (t : ℝ≥0) (K : ℕ) :
    count T t ω = K ↔ arrivalTime T K ω ≤ t ∧ (t : ℝ) < arrivalTime T (K + 1) ω := by
  refine ⟨?_, count_of_gap T t ω (fun i ↦ (hpos i).le) K⟩
  rintro rfl
  have hex : ∃ j, (t : ℝ) < arrivalTime T (j + 1) ω := by
    obtain ⟨j, hj⟩ := Filter.eventually_atTop.1 (htend.eventually_gt_atTop (t : ℝ))
    exact ⟨j, hj (j + 1) (by omega)⟩
  classical
  have hgap : arrivalTime T (Nat.find hex) ω ≤ t ∧
      (t : ℝ) < arrivalTime T (Nat.find hex + 1) ω := by
    refine ⟨?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h | h
    · rw [h]
      simp [arrivalTime]
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [h]
      exact not_lt.mp hmin
  rw [count_of_gap T t ω (fun i ↦ (hpos i).le) _ hgap]
  exact hgap

private lemma inGaps_iff_countsAlong {T : ℕ → Ω → ℝ} {ω : Ω} (hpos : ∀ i, 0 < T i ω)
    (htend : Filter.Tendsto (fun n ↦ arrivalTime T n ω) Filter.atTop Filter.atTop) :
    ∀ (s : ℝ≥0) (m : ℕ) (L : List (ℝ≥0 × ℕ)),
      InGaps (fun i ↦ T i ω) s m L ↔ CountsAlong (fun t ↦ count T t ω) s m L
  | s, m, [] => by simp [InGaps, CountsAlong]
  | s, m, p :: L => by
    simp only [InGaps, CountsAlong]
    rw [← NNReal.coe_add, count_eq_iff hpos htend, inGaps_iff_countsAlong hpos htend (s + p.1)]
    rfl

private lemma tsum_poissonMeasure_singleton (q : ℝ≥0) :
    (∑' j : ℕ, poissonMeasure q {j}) = 1 := by
  rw [← measure_iUnion (by intro i j hij; simpa using hij)
    (fun j ↦ measurableSet_singleton j)]
  rw [show (⋃ i : ℕ, ({i} : Set ℕ)) = Set.univ by ext x; simp]
  exact measure_univ

/-- The joint law of the increments of the exponential counting process over consecutive
intervals is the product of the Poisson laws of means `r (t (i + 1) - t i)`. -/
private theorem measure_increments_eq {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) (n : ℕ)
    (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) (k : Fin n → ℕ) :
    P {ω | ∀ i, count T (t i.succ) ω - count T (t i.castSucc) ω = k i} =
      ∏ i, poissonMeasure (r * (t i.succ - t i.castSucc)) {k i} := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hP : IsProbabilityMeasure P := (hT 0).isProbabilityMeasure
  have hX : AEMeasurable (fun ω i ↦ T i ω) P :=
    aemeasurable_pi_iff.2 fun i ↦ (hT i).aemeasurable
  have hlaw : P.map (fun ω i ↦ T i ω) = expSeq r := by
    rw [hind.map_fun_eq_infinitePi_map₀' fun i ↦ (hT i).aemeasurable]
    congr 1
    funext i
    exact (hT i).map_eq
  have hgap : ∀ L, P {ω | InGaps (fun i ↦ T i ω) 0 0 L} =
      (L.map fun p ↦ poissonMeasure (r * p.1) {p.2}).prod := by
    intro L
    rw [← expSeq_inGaps hr L, ← hlaw,
      Measure.map_apply_of_aemeasurable hX (measurableSet_inGaps 0 0 L)]
    rfl
  let G : ℕ → Set Ω := fun k₀ ↦ {ω | InGaps (fun i ↦ T i ω) 0 0
    ((t 0, k₀) :: List.ofFn fun i ↦ (t i.succ - t i.castSucc, k i))}
  have hmem : ∀ᵐ ω ∂P, ∀ k₀, ω ∈ G k₀ ↔ count T (t 0) ω = k₀ ∧
      ∀ i, count T (t i.succ) ω - count T (t i.castSucc) ω = k i := by
    filter_upwards [ae_interarrival_pos hr hT, ae_arrivalTime_tendsto hr hT hind,
      ae_count_monotone hr hT hind] with ω hpos htend hmono k₀
    change InGaps (fun i ↦ T i ω) ((0 : ℝ≥0) : ℝ) 0 _ ↔ _
    rw [inGaps_iff_countsAlong hpos htend]
    simp only [CountsAlong, zero_add]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, ?_⟩
      rw [← h0] at h
      exact (countsAlong_ofFn hmono n t ht k).1 h
    · rintro ⟨h0, h⟩
      refine ⟨h0, ?_⟩
      rw [← h0]
      exact (countsAlong_ofFn hmono n t ht k).2 h
  have hE : P {ω | ∀ i, count T (t i.succ) ω - count T (t i.castSucc) ω = k i} =
      P (⋃ k₀, G k₀) := by
    apply measure_congr
    filter_upwards [hmem] with ω hω
    apply propext
    simp only [mem_iUnion, hω]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨_, _, h⟩
      exact h
  rw [hE, measure_iUnion₀]
  · simp only [G, hgap, List.map_cons, List.prod_cons, List.map_ofFn, List.prod_ofFn,
      Function.comp_def]
    rw [ENNReal.tsum_mul_right, tsum_poissonMeasure_singleton, one_mul]
  · intro i j hij
    change P (G i ∩ G j) = 0
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hmem] with ω hω
    rintro ⟨hi, hj⟩
    exact hij (((hω i).1 hi).1.symm.trans ((hω j).1 hj).1)
  · intro k₀
    exact hX.nullMeasurableSet_preimage (measurableSet_inGaps (0 : ℝ) 0
      ((t 0, k₀) :: List.ofFn fun i ↦ (t i.succ - t i.castSucc, k i)))

/-- The increments of the counting process of i.i.d. rate-`r` exponential interarrivals over
consecutive intervals `(t i, t (i + 1)]` are independent with the Poisson laws of means
`r (t (i + 1) - t i)`: the increment vector has the product law (Kingman 1993, ch. 4;
Karlin–Taylor 1975, ch. 4). -/
theorem hasLaw_count_increments {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) (n : ℕ)
    (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    HasLaw (fun ω (i : Fin n) ↦ count T (t i.succ) ω - count T (t i.castSucc) ω)
      (Measure.pi fun i ↦ poissonMeasure (r * (t i.succ - t i.castSucc))) P := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hP : IsProbabilityMeasure P := (hT 0).isProbabilityMeasure
  have hN : ∀ s, AEMeasurable (count T s) P := fun s ↦ (hasLaw_count hr hT hind s).aemeasurable
  have hm : AEMeasurable
      (fun ω (i : Fin n) ↦ count T (t i.succ) ω - count T (t i.castSucc) ω) P :=
    aemeasurable_pi_iff.2 fun i ↦
      (measurable_of_countable fun p : ℕ × ℕ ↦ p.1 - p.2).comp_aemeasurable
        ((hN _).prodMk (hN _))
  refine ⟨hm, Measure.ext_of_singleton fun y ↦ ?_⟩
  rw [Measure.map_apply_of_aemeasurable hm (measurableSet_singleton y), Measure.pi_singleton,
    ← measure_increments_eq hr hT hind n t ht y]
  congr 1
  ext ω
  simp [funext_iff]

/-- **Exponential interarrivals give a Poisson process** (Kingman 1993, ch. 4; Karlin–Taylor
1975, ch. 4): the counting process of i.i.d. rate-`r` exponential interarrival times is a Poisson
process of rate `r`. -/
theorem isPoissonProcess_count {T : ℕ → Ω → ℝ} {r : ℝ≥0} (hr : 0 < r)
    (hT : ∀ i, HasLaw (T i) (expMeasure r) P) (hind : iIndepFun T P) :
    IsPoissonProcess (count T) r P := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hP : IsProbabilityMeasure P := (hT 0).isProbabilityMeasure
  refine ⟨ae_count_zero hr hT, ae_count_monotone hr hT hind, ?_, ?_⟩
  · intro n t ht
    have hl := hasLaw_count_increments hr hT hind n t ht
    have hiLaw (i : Fin n) :=
      (measurePreserving_eval
        (fun (i : Fin n) ↦ poissonMeasure (r * (t i.succ - t i.castSucc))) i).fun_comp_hasLaw hl
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hiLaw i).aemeasurable)).2
    rw [hl.map_eq]
    congr 1
    funext i
    exact (hiLaw i).map_eq.symm
  · intro s t hst
    let ts : Fin 2 → ℝ≥0 := ![s, t]
    have hts : Monotone ts := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [ts]
    have hl := hasLaw_count_increments hr hT hind 1 ts hts
    have hl0 := (measurePreserving_eval
      (fun (i : Fin 1) ↦ poissonMeasure (r * (ts i.succ - ts i.castSucc)))
      (0 : Fin 1)).fun_comp_hasLaw hl
    simpa [ts] using hl0

end PoissonProcess

end ProbabilityTheory
