/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Measure.Real

/-!
# The Kaplan–Meier product-limit estimator

Right-censored survival data are grouped at `k` distinct observation times
`t₀ < t₁ < ⋯ < t_{k-1}`: at time `tⱼ`, `dⱼ` subjects die (the event is observed) and `cⱼ`
subjects are censored (last seen alive at `tⱼ`). As usual, a subject censored at `tⱼ` is at risk
at `tⱼ` and is assumed to survive past `tⱼ` (censoring comes after the deaths at a tied time).
The number at risk at `tⱼ` is `nⱼ = ∑_{l ≥ j} (d_l + c_l)`, and the Kaplan–Meier estimate of the
survival function is

  `Ŝ(t) = ∏_{tⱼ ≤ t} (1 - dⱼ / nⱼ)`.

## Main results

* `kmMeasure_isProbabilityMeasure`, `kmMeasure_real_Ioi`: the Kaplan–Meier jumps
  `Ŝ(tⱼ₋) dⱼ / nⱼ` at the observation times, together with the leftover mass `Ŝ(t_{k-1})`
  placed at a point `τ`, form a probability measure whose survival function `t ↦ P(T > t)` is
  `Ŝ` on `(-∞, τ)`.
* `likelihood_le_kmMeasure`: **the nonparametric maximum likelihood property** (Kaplan–Meier
  1958): for every probability measure `μ` on `ℝ`, the censored-data likelihood
  `∏ⱼ μ{tⱼ}^{dⱼ} μ(tⱼ, ∞)^{cⱼ}` is at most its value at the Kaplan–Meier measure.
* `kmSurvival_of_censored_eq_zero`: **reduction to the empirical distribution**: without
  censoring, `Ŝ(t)` is the fraction of the `n` observations exceeding `t`, i.e. `1 - Fₙ(t)`.
* `size_mul_kmSurvival`: **self-consistency** (Efron 1967, equation (7.4)):
  `n Ŝ(t) = #{observations > t} + ∑_{tⱼ ≤ t} cⱼ Ŝ(t) / Ŝ(tⱼ)`, i.e. each subject censored by `t`
  is redistributed to the right in proportion to `Ŝ`. The censored-at-`tⱼ` terms are well defined
  because `Ŝ(tⱼ) > 0` whenever `cⱼ > 0` (`kmSurvival_pos_of_censored_pos`).

The likelihood depends on `μ` only through the atoms `μ{tⱼ}` and the tails `μ(tⱼ, ∞)`, so the
maximizer is not unique: the leftover mass may be placed anywhere after the last observation time
(here at `τ`). The NPMLE theorem needs `τ` after every observation time.

## References

* E. L. Kaplan and P. Meier, *Nonparametric estimation from incomplete observations*, J. Amer.
  Statist. Assoc. 53 (1958), 457–481.
* B. Efron, *The two sample problem with censored data*, Proc. Fifth Berkeley Symp. Math.
  Statist. Probab., Vol. 4 (1967), 831–853, Section 7 (self-consistency, Corollary 7.1).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.KaplanMeier

open MeasureTheory Finset

/-- Right-censored survival data grouped at `k` distinct, increasing observation times: `deaths j`
subjects die and `censored j` subjects are censored at `time j`. -/
structure CensoredData (k : ℕ) where
  /-- The distinct observation times, in increasing order. -/
  time : Fin k → ℝ
  /-- The observation times are strictly increasing. -/
  strictMono_time : StrictMono time
  /-- The number of observed deaths at each time. -/
  deaths : Fin k → ℕ
  /-- The number of subjects censored at each time. -/
  censored : Fin k → ℕ

namespace CensoredData

variable {k : ℕ} (D : CensoredData k)

/-- The number of subjects in the sample. -/
def size : ℕ := ∑ j, (D.deaths j + D.censored j)

/-- The number at risk at `time j`: subjects whose observation time is at least `time j`. -/
def atRisk (j : Fin k) : ℕ := ∑ l with j ≤ l, (D.deaths l + D.censored l)

/-- The Kaplan–Meier factor `1 - dⱼ / nⱼ` at `time j` (it is `1` if nobody is at risk, where
also `dⱼ = 0`). -/
noncomputable def kmFactor (j : Fin k) : ℝ := 1 - (D.deaths j : ℝ) / D.atRisk j

/-- The Kaplan–Meier estimate `Ŝ(t) = ∏_{tⱼ ≤ t} (1 - dⱼ / nⱼ)` of the survival function. -/
noncomputable def kmSurvival (t : ℝ) : ℝ := ∏ j with D.time j ≤ t, D.kmFactor j

/-- The Kaplan–Meier jump at `time j`: `Ŝ(tⱼ₋) · dⱼ / nⱼ`. -/
noncomputable def kmMass (j : Fin k) : ℝ :=
  (∏ l with l < j, D.kmFactor l) * ((D.deaths j : ℝ) / D.atRisk j)

/-- The Kaplan–Meier mass left after the last observation time, `∏ⱼ (1 - dⱼ / nⱼ)`. -/
noncomputable def kmTail : ℝ := ∏ j, D.kmFactor j

/-- The Kaplan–Meier measure: the jumps `kmMass j` at `time j` and the leftover mass `kmTail` at
a chosen point `τ` (taken after the last observation time). -/
noncomputable def kmMeasure (τ : ℝ) : Measure ℝ :=
  ∑ j, ENNReal.ofReal (D.kmMass j) • Measure.dirac (D.time j) +
    ENNReal.ofReal D.kmTail • Measure.dirac τ

/-- The censored-data likelihood of a law `μ` of the survival time:
`∏ⱼ μ{tⱼ}^{dⱼ} · μ(tⱼ, ∞)^{cⱼ}`. -/
noncomputable def likelihood (μ : Measure ℝ) : ℝ :=
  ∏ j, μ.real {D.time j} ^ D.deaths j * μ.real (Set.Ioi (D.time j)) ^ D.censored j

/-- The deaths at a time are among those at risk. -/
theorem deaths_le_atRisk (j : Fin k) : D.deaths j ≤ D.atRisk j :=
  (Nat.le_add_right _ _).trans
    (single_le_sum (f := fun l => D.deaths l + D.censored l) (fun _ _ => Nat.zero_le _)
      (by simp))

/-- The Kaplan–Meier factor is at most `1`. -/
theorem kmFactor_le_one (j : Fin k) : D.kmFactor j ≤ 1 := by
  have : (0 : ℝ) ≤ D.deaths j / D.atRisk j := by positivity
  rw [kmFactor]; linarith

/-- The Kaplan–Meier factor is non-negative. -/
theorem kmFactor_nonneg (j : Fin k) : 0 ≤ D.kmFactor j := by
  rw [kmFactor, sub_nonneg]
  exact div_le_one_of_le₀ (by exact_mod_cast D.deaths_le_atRisk j) (Nat.cast_nonneg _)

/-- The Kaplan–Meier jumps are non-negative. -/
theorem kmMass_nonneg (j : Fin k) : 0 ≤ D.kmMass j :=
  mul_nonneg (prod_nonneg fun l _ => D.kmFactor_nonneg l) (by positivity)

/-- The leftover Kaplan–Meier mass is non-negative. -/
theorem kmTail_nonneg : 0 ≤ D.kmTail := prod_nonneg fun l _ => D.kmFactor_nonneg l

/-- The Kaplan–Meier jumps over an initial segment `A` add up to `1 - ∏_{l ∈ A} (1 - d_l / n_l)`. -/
private lemma sum_kmMass_of_downClosed (A : Finset (Fin k))
    (hA : ∀ i j, i ≤ j → j ∈ A → i ∈ A) :
    ∑ j ∈ A, D.kmMass j = 1 - ∏ l ∈ A, D.kmFactor l := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs : ∀ i j, i ≤ j → j ∈ s → i ∈ s := fun i j hij hj => by
      rcases mem_insert.1 (hA i j hij (mem_insert_of_mem hj)) with rfl | hi
      · exact absurd (lt_of_le_of_lt hij (hlt j hj)) (lt_irrefl _)
      · exact hi
    have hlt' : univ.filter (· < a) = s := by
      ext l
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun hl => ?_, hlt l⟩
      rcases mem_insert.1 (hA l a hl.le (mem_insert_self a s)) with rfl | h
      · exact absurd hl (lt_irrefl _)
      · exact h
    rw [sum_insert has, prod_insert has, ih hs, kmMass, hlt', kmFactor]
    ring

/-- The Kaplan–Meier jumps and the leftover mass add up to `1`. -/
theorem sum_kmMass_add_kmTail : ∑ j, D.kmMass j + D.kmTail = 1 := by
  rw [D.sum_kmMass_of_downClosed univ (fun _ _ _ _ => mem_univ _), kmTail]
  ring

open Classical in
/-- The mass of a measurable set under the Kaplan–Meier measure. -/
theorem kmMeasure_real_apply (τ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    (D.kmMeasure τ).real B =
      ∑ j, (if D.time j ∈ B then D.kmMass j else 0) + if τ ∈ B then D.kmTail else 0 := by
  have hfin : ∀ j, ENNReal.ofReal (D.kmMass j) * B.indicator 1 (D.time j) ≠ ⊤ := fun j => by
    by_cases h : D.time j ∈ B <;> simp [h]
  rw [measureReal_def, kmMeasure, Measure.add_apply, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_add (ENNReal.sum_ne_top.2 fun j _ => by
      simpa [Measure.smul_apply, Measure.dirac_apply' _ hB] using hfin j)
      (by by_cases h : τ ∈ B <;> simp [Measure.smul_apply, Measure.dirac_apply' _ hB, h]),
    ENNReal.toReal_sum fun j _ => by
      simpa [Measure.smul_apply, Measure.dirac_apply' _ hB] using hfin j]
  congr 1
  · refine sum_congr rfl fun j _ => ?_
    by_cases h : D.time j ∈ B <;>
      simp [Measure.smul_apply, Measure.dirac_apply' _ hB, h, D.kmMass_nonneg j]
  · by_cases h : τ ∈ B <;>
      simp [Measure.smul_apply, Measure.dirac_apply' _ hB, h, D.kmTail_nonneg]

/-- The Kaplan–Meier measure is a probability measure. -/
theorem kmMeasure_isProbabilityMeasure (τ : ℝ) : IsProbabilityMeasure (D.kmMeasure τ) := by
  have hfin : D.kmMeasure τ Set.univ ≠ ⊤ := by
    simp [kmMeasure, Measure.add_apply, Measure.smul_apply]
  refine ⟨?_⟩
  have h := D.kmMeasure_real_apply τ MeasurableSet.univ
  simp only [Set.mem_univ, ite_true, sum_kmMass_add_kmTail] at h
  rw [measureReal_def] at h
  exact (ENNReal.toReal_eq_one_iff _).1 h

/-- The survival function of the Kaplan–Meier measure is the Kaplan–Meier estimate on
`(-∞, τ)`: `P(T > t) = Ŝ(t)` for `t < τ`. -/
theorem kmMeasure_real_Ioi {τ : ℝ} {t : ℝ} (ht : t < τ) :
    (D.kmMeasure τ).real (Set.Ioi t) = D.kmSurvival t := by
  classical
  have hdown := D.sum_kmMass_of_downClosed (univ.filter (D.time · ≤ t)) fun i j hij hj => by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact (D.strictMono_time.monotone hij).trans hj
  have htot := D.sum_kmMass_add_kmTail
  have hsplit : ∑ j, D.kmMass j = ∑ j with D.time j ≤ t, D.kmMass j +
      ∑ j, (if D.time j ∈ Set.Ioi t then D.kmMass j else 0) := by
    rw [← sum_filter, ← sum_filter_add_sum_filter_not univ (fun j => D.time j ≤ t)]
    congr 1
    refine Finset.sum_congr (by ext j; simp [not_le]) fun _ _ => rfl
  rw [D.kmMeasure_real_apply τ measurableSet_Ioi, kmSurvival]
  simp only [Set.mem_Ioi, ht, ite_true] at hsplit ⊢
  linarith

open Real in
/-- Weighted AM–GM in homogeneous form: `x^d y^m ≤ (d/(d+m))^d (m/(d+m))^m (x + y)^(d+m)`. -/
private lemma pow_mul_pow_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (d m : ℕ) :
    x ^ d * y ^ m ≤ ((d : ℝ) / (d + m)) ^ d * ((m : ℝ) / (d + m)) ^ m * (x + y) ^ (d + m) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      simp only [pow_zero, one_mul, zero_add, CharP.cast_eq_zero, div_self hm'.ne', one_pow]
      exact pow_le_pow_left₀ hy (le_add_of_nonneg_left hx) m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [pow_zero, mul_one, add_zero, CharP.cast_eq_zero, div_self hd'.ne', one_pow]
    rw [one_mul]
    exact pow_le_pow_left₀ hx (le_add_of_nonneg_right hy) d
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = d + m := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  have hamgm := geom_mean_le_arith_mean2_weighted (w₁ := d / n) (w₂ := m / n)
    (p₁ := x * n / d) (p₂ := y * n / m) (by positivity) (by positivity) (by positivity)
    (by positivity) (by rw [hn_def]; field_simp)
  have hrhs : d / n * (x * n / d) + m / n * (y * n / m) = x + y := by field_simp
  rw [hrhs] at hamgm
  have hpow := pow_le_pow_left₀ (by positivity) hamgm (d + m)
  rw [mul_pow, ← rpow_natCast, ← rpow_natCast (_ ^ (m / n : ℝ)), ← rpow_mul (by positivity),
    ← rpow_mul (by positivity)] at hpow
  have e1 : (d : ℝ) / n * ((d + m : ℕ) : ℝ) = d := by push_cast; rw [← hn_def]; field_simp
  have e2 : (m : ℝ) / n * ((d + m : ℕ) : ℝ) = m := by push_cast; rw [← hn_def]; field_simp
  rw [e1, e2, rpow_natCast, rpow_natCast, div_pow, div_pow, mul_pow, mul_pow] at hpow
  have key : x ^ d * y ^ m * n ^ (d + m) ≤ (d : ℝ) ^ d * (m : ℝ) ^ m * (x + y) ^ (d + m) := by
    have := hpow
    rw [div_mul_div_comm, div_le_iff₀ (by positivity)] at this
    calc x ^ d * y ^ m * n ^ (d + m) = x ^ d * n ^ d * (y ^ m * n ^ m) := by ring
      _ ≤ _ := by linarith
  rw [← hn_def, div_pow, div_pow]
  rw [show ((d : ℝ) ^ d / n ^ d * ((m : ℝ) ^ m / n ^ m)) * (x + y) ^ (d + m) =
    (d : ℝ) ^ d * (m : ℝ) ^ m * (x + y) ^ (d + m) / n ^ (d + m) by
      rw [pow_add, pow_add]; field_simp]
  rw [le_div_iff₀ (by positivity)]
  exact key

/-- The binomial factor `ĥ^d (1 - ĥ)^(n - d)` at `time j`, with hazard `ĥ = d / n`. -/
private noncomputable def binomFactor (j : Fin k) : ℝ :=
  ((D.deaths j : ℝ) / D.atRisk j) ^ D.deaths j * D.kmFactor j ^ (D.atRisk j - D.deaths j)

private lemma binomFactor_nonneg (j : Fin k) : 0 ≤ D.binomFactor j :=
  mul_nonneg (by positivity) (pow_nonneg (D.kmFactor_nonneg j) _)

private lemma atRisk_eq (j : Fin k) :
    D.atRisk j = D.deaths j + D.censored j + ∑ l with j < l, (D.deaths l + D.censored l) := by
  rw [atRisk, show univ.filter (j ≤ ·) = insert j (univ.filter (j < ·)) by
    ext l; simp [le_iff_eq_or_lt, eq_comm], sum_insert (by simp)]

/-- The binomial bound `x^d y^m ≤ ĥ^d (1 - ĥ)^m (x + y)^n` when `n = d + m` is the number at
risk. -/
private lemma pow_mul_pow_le_binomFactor (j : Fin k) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {m : ℕ}
    (hm : D.atRisk j = D.deaths j + m) :
    x ^ D.deaths j * y ^ m ≤ D.binomFactor j * (x + y) ^ D.atRisk j := by
  have h := pow_mul_pow_le x y hx hy (D.deaths j) m
  have hsub : D.atRisk j - D.deaths j = m := by omega
  rcases Nat.eq_zero_or_pos (D.atRisk j) with h0 | hpos
  · have hd : D.deaths j = 0 := by omega
    have hm0 : m = 0 := by omega
    simp [binomFactor, h0, hd, hm0]
  have hn : ((D.atRisk j : ℕ) : ℝ) = D.deaths j + m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < D.atRisk j := by exact_mod_cast hpos
  have hf : D.kmFactor j = (m : ℝ) / (D.deaths j + m) := by
    rw [kmFactor, hn, eq_div_iff (by rw [← hn]; exact hnpos.ne'), sub_mul,
      div_mul_cancel₀ _ (by rw [← hn]; exact hnpos.ne')]
    ring
  rw [binomFactor, hsub, hf, hn, hm]
  simpa [hm] using h

/-- The likelihood bound over an up-closed set `U` of time indices, for any `g` dominating
`μ [tₗ, ∞)` on `U`. -/
private lemma prod_le_of_upClosed (μ : Measure ℝ) [IsFiniteMeasure μ] (U : Finset (Fin k))
    (hU : ∀ i j, i ≤ j → i ∈ U → j ∈ U) (g : ℝ) (hg : 0 ≤ g)
    (hG : ∀ l ∈ U, μ.real (Set.Ici (D.time l)) ≤ g) :
    ∏ l ∈ U, μ.real {D.time l} ^ D.deaths l * μ.real (Set.Ioi (D.time l)) ^ D.censored l ≤
      (∏ l ∈ U, D.binomFactor l) * g ^ (∑ l ∈ U, (D.deaths l + D.censored l)) := by
  induction U using Finset.induction_on_min generalizing g with
  | empty => simp
  | insert b s hlt ih =>
    have hbs : b ∉ s := fun h => lt_irrefl b (hlt b h)
    have hs : ∀ i j, i ≤ j → i ∈ s → j ∈ s := fun i j hij hi => by
      rcases mem_insert.1 (hU i j hij (mem_insert_of_mem hi)) with rfl | hj
      · exact absurd (lt_of_lt_of_le (hlt i hi) hij) (lt_irrefl _)
      · exact hj
    have hUeq : univ.filter (b ≤ ·) = insert b s := by
      ext l
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun hl => hU b l hl (mem_insert_self b s), fun hl => ?_⟩
      rcases mem_insert.1 hl with rfl | hl
      · exact le_rfl
      · exact (hlt l hl).le
    have hN : D.atRisk b = D.deaths b + (D.censored b + ∑ l ∈ s, (D.deaths l + D.censored l)) := by
      rw [atRisk, hUeq, sum_insert hbs]
      ring
    set A := μ.real {D.time b}
    set B := μ.real (Set.Ioi (D.time b))
    have hA : 0 ≤ A := measureReal_nonneg
    have hB : 0 ≤ B := measureReal_nonneg
    have hAB : A + B = μ.real (Set.Ici (D.time b)) := by
      rw [← Set.Ioi_insert, Set.insert_eq, measureReal_union (by simp) measurableSet_Ioi]
    have hG' : ∀ l ∈ s, μ.real (Set.Ici (D.time l)) ≤ B := fun l hl =>
      measureReal_mono (Set.Ici_subset_Ioi.2 (D.strictMono_time (hlt l hl)))
    have hih := ih hs B hB hG'
    have hBs : 0 ≤ ∏ l ∈ s, D.binomFactor l := prod_nonneg fun l _ => D.binomFactor_nonneg l
    have hstep := D.pow_mul_pow_le_binomFactor b hA hB hN
    have hAg : A + B ≤ g := hAB ▸ hG b (mem_insert_self b s)
    rw [prod_insert hbs, prod_insert hbs, sum_insert hbs]
    calc A ^ D.deaths b * B ^ D.censored b *
          ∏ l ∈ s, μ.real {D.time l} ^ D.deaths l * μ.real (Set.Ioi (D.time l)) ^ D.censored l
        ≤ A ^ D.deaths b * B ^ D.censored b *
            ((∏ l ∈ s, D.binomFactor l) * B ^ (∑ l ∈ s, (D.deaths l + D.censored l))) :=
          mul_le_mul_of_nonneg_left hih (by positivity)
      _ = (∏ l ∈ s, D.binomFactor l) * (A ^ D.deaths b *
            B ^ (D.censored b + ∑ l ∈ s, (D.deaths l + D.censored l))) := by ring
      _ ≤ (∏ l ∈ s, D.binomFactor l) * (D.binomFactor b * (A + B) ^ D.atRisk b) :=
          mul_le_mul_of_nonneg_left hstep hBs
      _ ≤ (∏ l ∈ s, D.binomFactor l) * (D.binomFactor b * g ^ D.atRisk b) := by
          gcongr
          exact D.binomFactor_nonneg b
      _ = _ := by rw [hN]; ring

/-- The likelihood of the Kaplan–Meier measure is the product of the binomial factors. -/
private lemma likelihood_kmMeasure {τ : ℝ} (hτ : ∀ j, D.time j < τ) :
    D.likelihood (D.kmMeasure τ) = ∏ j, D.binomFactor j := by
  classical
  set P : Fin k → ℝ := fun j => ∏ l with l < j, D.kmFactor l
  have hatom : ∀ j, (D.kmMeasure τ).real {D.time j} = P j * (D.deaths j / D.atRisk j) := by
    intro j
    rw [D.kmMeasure_real_apply τ (measurableSet_singleton _)]
    simp only [Set.mem_singleton_iff, D.strictMono_time.injective.eq_iff, (hτ j).ne', ite_false,
      add_zero, sum_ite_eq', mem_univ, ite_true]
    rfl
  have hsurv : ∀ j, (D.kmMeasure τ).real (Set.Ioi (D.time j)) = P j * D.kmFactor j := by
    intro j
    rw [D.kmMeasure_real_Ioi (hτ j), kmSurvival,
      show univ.filter (D.time · ≤ D.time j) = insert j (univ.filter (· < j)) by
        ext l; simp [D.strictMono_time.le_iff_le, le_iff_eq_or_lt],
      prod_insert (by simp), mul_comm]
  -- `∏ⱼ Pⱼ^(dⱼ + cⱼ) = ∏ⱼ fⱼ^(∑_{l > j} (d_l + c_l))`
  have hswap : ∏ j, P j ^ (D.deaths j + D.censored j) =
      ∏ j, D.kmFactor j ^ (∑ l with j < l, (D.deaths l + D.censored l)) := by
    simp only [P, ← prod_pow_eq_pow_sum, ← prod_pow]
    exact (prod_comm' fun x y => by simp).symm
  rw [likelihood]
  simp only [hatom, hsurv]
  have hb : ∀ j, D.binomFactor j = ((D.deaths j : ℝ) / D.atRisk j) ^ D.deaths j *
      D.kmFactor j ^ D.censored j *
        D.kmFactor j ^ (∑ l with j < l, (D.deaths l + D.censored l)) := fun j => by
    rw [binomFactor, mul_assoc, ← pow_add]
    congr 2
    rw [D.atRisk_eq j]
    omega
  simp only [hb, prod_mul_distrib, ← hswap, mul_pow, pow_add]
  ring

/-- **Kaplan–Meier is the nonparametric MLE** (Kaplan–Meier 1958): every probability measure on
`ℝ` has censored-data likelihood at most that of the Kaplan–Meier measure. -/
theorem likelihood_le_kmMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] {τ : ℝ}
    (hτ : ∀ j, D.time j < τ) : D.likelihood μ ≤ D.likelihood (D.kmMeasure τ) := by
  have h := D.prod_le_of_upClosed μ univ (fun _ _ _ _ => mem_univ _) 1 zero_le_one
    fun _ _ => measureReal_le_one
  rw [one_pow, mul_one] at h
  rw [D.likelihood_kmMeasure hτ]
  exact h

/-- A time at which some subject is censored has positive Kaplan–Meier survival. -/
theorem kmSurvival_pos_of_censored_pos {j : Fin k} (hj : 0 < D.censored j) :
    0 < D.kmSurvival (D.time j) := by
  refine prod_pos fun l hl => ?_
  have hlj : l ≤ j := D.strictMono_time.le_iff_le.1 (mem_filter.1 hl).2
  have key : D.deaths l + D.censored j ≤ D.atRisk l := by
    rcases hlj.lt_or_eq with h | rfl
    · have hsub : ({l, j} : Finset (Fin k)) ⊆ univ.filter (l ≤ ·) := by
        intro m hm
        simp only [mem_insert, mem_singleton] at hm
        rcases hm with rfl | rfl <;> simp [h.le]
      calc D.deaths l + D.censored j
          ≤ (D.deaths l + D.censored l) + (D.deaths j + D.censored j) := by omega
        _ = ∑ m ∈ {l, j}, (D.deaths m + D.censored m) :=
          (sum_pair (f := fun m => D.deaths m + D.censored m) h.ne).symm
        _ ≤ D.atRisk l := sum_le_sum_of_subset hsub
    · exact single_le_sum (f := fun m => D.deaths m + D.censored m) (fun _ _ => Nat.zero_le _)
        (by simp)
  have hpos : (0 : ℝ) < D.atRisk l := by exact_mod_cast (by omega : 0 < D.atRisk l)
  rw [kmFactor, sub_pos, div_lt_one hpos]
  exact_mod_cast (by omega : D.deaths l < D.atRisk l)

/-- The Kaplan–Meier factor times the number at risk is the number at risk minus the deaths. -/
private lemma kmFactor_mul_atRisk (j : Fin k) :
    D.kmFactor j * D.atRisk j = (D.atRisk j : ℝ) - D.deaths j := by
  rcases Nat.eq_zero_or_pos (D.atRisk j) with h | h
  · have hd : D.deaths j = 0 := Nat.le_zero.1 (h ▸ D.deaths_le_atRisk j)
    simp [h, hd]
  · rw [kmFactor, sub_mul, div_mul_cancel₀ _ (by exact_mod_cast h.ne'), one_mul]

/-- Self-consistency over a down-closed set `A` of time indices (an initial segment). -/
private lemma size_mul_prod_of_downClosed (A : Finset (Fin k))
    (hA : ∀ i j, i ≤ j → j ∈ A → i ∈ A) :
    (D.size : ℝ) * ∏ l ∈ A, D.kmFactor l =
      (∑ l with l ∉ A, ((D.deaths l : ℝ) + D.censored l)) +
        ∑ j ∈ A, (D.censored j : ℝ) *
          ((∏ l ∈ A, D.kmFactor l) / D.kmSurvival (D.time j)) := by
  induction A using Finset.induction_on_max with
  | empty => simp [size]
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs : ∀ i j, i ≤ j → j ∈ s → i ∈ s := fun i j hij hj => by
      have hi := hA i j hij (mem_insert_of_mem hj)
      rcases mem_insert.1 hi with rfl | hi
      · exact absurd (lt_of_le_of_lt hij (hlt j hj)) (lt_irrefl _)
      · exact hi
    have hnot : ∀ l, l ∉ s ↔ a ≤ l := fun l => by
      refine ⟨fun hl => ?_, fun hl hls => lt_irrefl a (lt_of_le_of_lt hl (hlt l hls))⟩
      by_contra hla
      push Not at hla
      rcases mem_insert.1 (hA l a hla.le (mem_insert_self a s)) with rfl | h
      · exact lt_irrefl _ hla
      · exact hl h
    have hle : ∀ l, l ∈ insert a s ↔ l ≤ a := fun l => by
      rw [mem_insert]
      refine ⟨fun h => h.elim le_of_eq fun h => (hlt l h).le, fun h => ?_⟩
      rcases h.lt_or_eq with h | h
      · exact Or.inr (by by_contra h'; exact absurd h ((hnot l).1 h').not_gt)
      · exact Or.inl h
    have hS : D.kmSurvival (D.time a) = ∏ l ∈ insert a s, D.kmFactor l := by
      unfold kmSurvival
      congr 1
      ext l
      simp [D.strictMono_time.le_iff_le, hle]
    have hR : (∑ l with l ∉ s, ((D.deaths l : ℝ) + D.censored l)) =
        (D.deaths a + D.censored a) +
          ∑ l with l ∉ insert a s, ((D.deaths l : ℝ) + D.censored l) := by
      have hset : univ.filter (· ∉ s) = insert a (univ.filter (· ∉ insert a s)) := by
        ext l
        by_cases hl : l = a <;> simp [hl, has]
      rw [hset, sum_insert (by simp)]
    have hAt : (D.atRisk a : ℝ) = ∑ l with l ∉ s, ((D.deaths l : ℝ) + D.censored l) := by
      rw [atRisk]
      push_cast
      congr 1
      ext l
      simp [hnot]
    have hS' : D.kmSurvival (D.time a) = D.kmFactor a * ∏ l ∈ s, D.kmFactor l := by
      rw [hS, prod_insert has]
    have hca : (D.censored a : ℝ) * ((D.kmFactor a * ∏ l ∈ s, D.kmFactor l) /
        D.kmSurvival (D.time a)) = D.censored a := by
      rcases Nat.eq_zero_or_pos (D.censored a) with h | h
      · simp [h]
      · rw [← hS', div_self (D.kmSurvival_pos_of_censored_pos h).ne', mul_one]
    rw [prod_insert has, sum_insert has, hca]
    have e1 : ∑ j ∈ s, (D.censored j : ℝ) *
        ((D.kmFactor a * ∏ l ∈ s, D.kmFactor l) / D.kmSurvival (D.time j)) =
        D.kmFactor a * ∑ j ∈ s, (D.censored j : ℝ) *
          ((∏ l ∈ s, D.kmFactor l) / D.kmSurvival (D.time j)) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring
    have hfa := D.kmFactor_mul_atRisk a
    calc (D.size : ℝ) * (D.kmFactor a * ∏ l ∈ s, D.kmFactor l)
        = D.kmFactor a * ((D.size : ℝ) * ∏ l ∈ s, D.kmFactor l) := by ring
      _ = D.kmFactor a * D.atRisk a + D.kmFactor a * ∑ j ∈ s, (D.censored j : ℝ) *
            ((∏ l ∈ s, D.kmFactor l) / D.kmSurvival (D.time j)) := by rw [ih hs, hAt]; ring
      _ = _ := by
          rw [hfa, hAt, hR, e1]
          ring

/-- **Self-consistency** (Efron 1967, (7.4)): `n Ŝ(t)` is the number of observations exceeding
`t` plus, for each subject censored at or before `t`, the conditional survival `Ŝ(t) / Ŝ(tⱼ)`. -/
theorem size_mul_kmSurvival (t : ℝ) :
    (D.size : ℝ) * D.kmSurvival t =
      (∑ j with t < D.time j, ((D.deaths j : ℝ) + D.censored j)) +
        ∑ j with D.time j ≤ t,
          (D.censored j : ℝ) * (D.kmSurvival t / D.kmSurvival (D.time j)) := by
  have h := D.size_mul_prod_of_downClosed (univ.filter (D.time · ≤ t)) fun i j hij hj => by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact (D.strictMono_time.monotone hij).trans hj
  rw [kmSurvival, h]
  congr 1
  rw [sum_filter, sum_filter]
  refine sum_congr rfl fun j _ => ?_
  simp [not_le]

/-- Without censoring, the Kaplan–Meier estimate is the empirical survival function: the
fraction `#{observations > t} / n = 1 - Fₙ(t)`. -/
theorem kmSurvival_of_censored_eq_zero (hc : ∀ j, D.censored j = 0) (hn : 0 < D.size)
    (t : ℝ) : D.kmSurvival t = (∑ j with t < D.time j, (D.deaths j : ℝ)) / D.size := by
  have h := D.size_mul_kmSurvival t
  simp only [hc, Nat.cast_zero, add_zero, zero_mul, sum_const_zero] at h
  rw [eq_div_iff (by exact_mod_cast hn.ne'), ← h, mul_comm]

end CensoredData

end MathlibExt.Probability.Statistics.KaplanMeier
