/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGrayAsymptotics
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxAsymptotics
open MathlibExt.Probability.Statistics.FineGrayAsymptotics
open MathlibExt.Probability.Statistics.ConcaveScore

namespace MathlibExtTest.Probability.Statistics.FineGrayAsymptotics

/-! ### A two-cause population: the subdistribution hazard from the definition

`ω` is uniform on `[0, 1]`. A subject with `ω < 1/2` fails from cause `0` at time `T = 2ω`; a
subject with `ω ≥ 1/2` fails from cause `1` at time `T = 2ω - 1`. So `T` is uniform on `[0, 1]`
and the cause is an independent fair coin, `F₀(t) = t / 2` on `[0, 1]`. At `t = 1/2` the risk
event `{T ≥ 1/2} ∪ {T < 1/2, J = 1}` has probability `3/4` (the cause-`1` failures stay at risk),
and the subdistribution hazard is `λ*₀(1/2) = (1/2) / (3/4) = 2/3`, whereas the cause-specific
hazard is `(1/2) / (1/2) = 1`. -/

/-- The uniform distribution on `[0, 1]`. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unif01 :=
  ⟨by simp [unif01, Real.volume_Icc]⟩

/-- The failure time of the two-cause population. -/
noncomputable def T₂c (ω : ℝ) : ℝ := if ω < 1 / 2 then 2 * ω else 2 * ω - 1

/-- The failure cause of the two-cause population. -/
noncomputable def J₂c (ω : ℝ) : Fin 2 := if ω < 1 / 2 then 0 else 1

theorem measurable_T₂c : Measurable T₂c :=
  Measurable.ite measurableSet_Iio (by fun_prop) (by fun_prop)

theorem setOf_J₂c : {ω | J₂c ω = 0} = Set.Iio (1 / 2) := by
  ext ω
  simp only [J₂c, Set.mem_ofPred_eq, Set.mem_Iio]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

theorem measurableSet_J₂c : MeasurableSet {ω | J₂c ω = 0} := by
  rw [setOf_J₂c]; exact measurableSet_Iio

/-- `F₀(s-) = s / 2` for `s ∈ [0, 1]`, computed from the definition. -/
theorem cifBefore_two_cause {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    cifBefore unif01 T₂c J₂c 0 s = s / 2 := by
  have hset : {ω | T₂c ω < s ∧ J₂c ω = 0} = Set.Iio (s / 2) := by
    ext ω
    simp only [T₂c, J₂c, Set.mem_ofPred_eq, Set.mem_Iio]
    split_ifs with h
    · simp only [and_true]; constructor <;> intro <;> linarith
    · simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, and_false, false_iff]
      intro; linarith
  have hI : Set.Iio (s / 2) ∩ Set.Icc 0 1 = Set.Ico 0 (s / 2) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨h, h', by linarith⟩
  rw [cifBefore, hset, unif01, measureReal_def, Measure.restrict_apply measurableSet_Iio, hI,
    Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by linarith)]

/-- The risk event at `1/2` has probability `1 - F₀(1/2-) = 3/4`. -/
example : unif01.real (subdistRiskSet T₂c J₂c 0 (1 / 2)) = 3 / 4 := by
  rw [measureReal_subdistRiskSet measurable_T₂c measurableSet_J₂c,
    cifBefore_two_cause (by norm_num) (by norm_num)]
  norm_num

/-- **The subdistribution hazard of cause `0` at `1/2` is `2/3`**, from the limit definition
through the right derivative `1/2` of `F₀(·-)`. -/
theorem hasSubdistHazardAt_two_cause : HasSubdistHazardAt unif01 T₂c J₂c 0 (1 / 2) (2 / 3) := by
  have hd : HasDerivWithinAt (cifBefore unif01 T₂c J₂c 0) (1 / 2) (Set.Ici (1 / 2)) (1 / 2) := by
    have h := ((hasDerivAt_id (1 / 2 : ℝ)).div_const 2).hasDerivWithinAt (s := Set.Ici (1 / 2))
    refine (h.congr_of_eventuallyEq ?_ ?_).congr_deriv (by norm_num)
    · filter_upwards [nhdsWithin_le_nhds (Icc_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))] with s hs
      exact cifBefore_two_cause hs.1 hs.2
    · exact cifBefore_two_cause (by norm_num) (by norm_num)
  have h := hasSubdistHazardAt_of_hasDerivWithinAt_cifBefore measurable_T₂c measurableSet_J₂c hd
  rwa [cifBefore_two_cause (by norm_num) (by norm_num),
    show (1 / 2 : ℝ) / (1 - 1 / 2 / 2) = 2 / 3 by norm_num] at h

example : subdistHazard unif01 T₂c J₂c 0 (1 / 2) = 2 / 3 :=
  hasSubdistHazardAt_two_cause.subdistHazard_eq

/-! ### A replicated two-cause sample: score, information limit and limit variance

At sample size `n`, with `k = n / 3`, subjects fall into four groups (`grp`):

* group `0` (`l < k`): cause-`0` failure at time `2`, covariate `1`;
* group `1` (`k ≤ l < 2k`): cause-`0` failure at time `2`, covariate `0`;
* group `2` (`2k ≤ l < 3k`): competing (cause-`1`) failure at time `1`, covariate `1`;
* group `3` (the remainder): censored at time `0`, covariate `0`.

The censoring survival is `Gex t = 1` for `t ≤ 1` and `1/2` after, so at time `2` every
competing-event subject has weight `Gex 2 / Gex 1 = 1/2`. With `a(b) = (3/2) exp b`, computed
from the definitions: `S₀ = k (a + 1)`, `S₁ = S₂ = k a`, the score is `Uₙ(b) = k (1 - 2 z̄)` with
`z̄ = a / (a + 1)`, and `Iₙ(b) = 2k a / (a + 1)²`. The score vanishes at `β₀ = log (2/3)`
(`a = 1`), and `Iₙ(b) / n → ifg b = (2/3) a / (a + 1)²` uniformly, with `v = ifg β₀ = 1/6`.
The Fine–Gray limit variance is `σ² / v² = 36 σ²`; here the data are deterministic, so `σ² = 0`. -/

/-- The group of subject `j` at sample size `n`. -/
def grp (n j : ℕ) : ℕ :=
  if j < n / 3 then 0 else if j < 2 * (n / 3) then 1 else if j < 3 * (n / 3) then 2 else 3

theorem grp_le (n j : ℕ) : grp n j ≤ 3 := by
  unfold grp; split_ifs <;> omega

/-- Summing a function of the group. -/
theorem sum_grp (n : ℕ) (f : ℕ → ℝ) :
    ∑ l : Fin n, f (grp n l) =
      ((n / 3 : ℕ) : ℝ) * (f 0 + f 1 + f 2) + ((n - 3 * (n / 3) : ℕ) : ℝ) * f 3 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (grp n j)) n]
  obtain ⟨k, hk⟩ : ∃ k, k = n / 3 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = n - 3 * k := ⟨_, rfl⟩
  have hg : ∀ j, grp n j = if j < k then 0 else if j < 2 * k then 1 else if j < 3 * k then 2
      else 3 := fun j => by simp only [grp, hk]
  simp only [hg]
  rw [← hk, ← ht]
  have hn : n = k + k + k + t := by omega
  rw [hn, sum_range_add, sum_range_add, sum_range_add]
  have h0 : ∑ x ∈ range k, f (if x < k then 0 else if x < 2 * k then 1 else if x < 3 * k then 2
      else 3) = ∑ _x ∈ range k, f 0 :=
    sum_congr rfl fun x hx => by rw [mem_range] at hx; rw [ite_eq_left hx]
  have h1 : ∑ x ∈ range k, f (if k + x < k then 0 else if k + x < 2 * k then 1
      else if k + x < 3 * k then 2 else 3) = ∑ _x ∈ range k, f 1 :=
    sum_congr rfl fun x hx => by
      rw [mem_range] at hx; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  have h2 : ∑ x ∈ range k, f (if k + k + x < k then 0 else if k + k + x < 2 * k then 1
      else if k + k + x < 3 * k then 2 else 3) = ∑ _x ∈ range k, f 2 :=
    sum_congr rfl fun x hx => by
      rw [mem_range] at hx
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  have h3 : ∑ x ∈ range t, f (if k + k + k + x < k then 0 else if k + k + k + x < 2 * k then 1
      else if k + k + k + x < 3 * k then 2 else 3) = ∑ _x ∈ range t, f 3 :=
    sum_congr rfl fun x _ => by
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [h0, h1, h2, h3]
  simp only [sum_const, card_range, nsmul_eq_mul]
  ring

/-- Observed time by group. -/
def Xg : ℕ → ℝ
  | 0 => 2
  | 1 => 2
  | 2 => 1
  | _ => 0

/-- Status by group. -/
def εg : ℕ → Option (Fin 2)
  | 0 => some 0
  | 1 => some 0
  | 2 => some 1
  | _ => none

/-- Covariate by group. -/
def zg : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | _ => 0

/-- The censoring survival used for the weights. -/
noncomputable def Gex (t : ℝ) : ℝ := if t ≤ 1 then 1 else 1 / 2

/-- Fine–Gray weight at time `2` by group. -/
noncomputable def wg : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1 / 2
  | _ => 0

/-- Observed times of the replicated design. -/
def Xd (n : ℕ) : Fin n → ℝ := fun l => Xg (grp n l)

/-- Statuses of the replicated design. -/
def εd (n : ℕ) : Fin n → Option (Fin 2) := fun l => εg (grp n l)

/-- Covariates of the replicated design. -/
def zd (n : ℕ) : Fin n → ℝ := fun l => zg (grp n l)

theorem grp_lt_two_of_event {n : ℕ} {i : Fin n} (hi : εd n i = some 0) : grp n i < 2 := by
  have := grp_le n i
  simp only [εd] at hi
  interval_cases h : grp n i <;> simp_all [εg]

theorem wg_spec {g : ℕ} (hg : g ≤ 3) :
    (if 2 ≤ Xg g then 1 else if εg g ≠ none ∧ εg g ≠ some 0 then Gex 2 / Gex (Xg g) else 0) =
      wg g := by
  interval_cases g <;> norm_num [Xg, εg, wg, Gex]

/-- At a cause-`0` failure (time `2`) the weight of subject `l` depends only on its group. -/
theorem fgWeight_d {n : ℕ} {i : Fin n} (hi : εd n i = some 0) (l : Fin n) :
    fgWeight (Xd n) (εd n) 0 Gex l i = wg (grp n l) := by
  have hXi : Xd n i = 2 := by
    have := grp_lt_two_of_event hi
    simp only [Xd]
    interval_cases grp n i <;> rfl
  unfold fgWeight
  rw [hXi]
  exact wg_spec (grp_le n l)

/-- `a(b) = (3/2) exp b`. -/
noncomputable def aex (b : ℝ) : ℝ := 3 / 2 * exp b

theorem aex_pos (b : ℝ) : 0 < aex b := by unfold aex; positivity

/-- The weighted sums at a cause-`0` failure: `S_k = k (a + 0 ^ k)`, i.e. `S₀ = k (a + 1)` and
`S₁ = S₂ = k a`. -/
theorem fgWeightedSum_d {n : ℕ} {i : Fin n} (hi : εd n i = some 0) (m : ℕ) (b : ℝ) :
    fgWeightedSum (Xd n) (εd n) 0 Gex (zd n) m b i =
      ((n / 3 : ℕ) : ℝ) * (aex b + (0 : ℝ) ^ m) := by
  rw [fgWeightedSum]
  simp only [fgWeight_d hi, zd]
  rw [sum_grp n (fun g => wg g * (zg g ^ m * exp (b * zg g)))]
  simp only [wg, zg, one_pow, mul_one, mul_zero, exp_zero, zero_mul, aex]
  ring

/-- The weighted mean at a cause-`0` failure. -/
noncomputable def meanex (n : ℕ) (b : ℝ) : ℝ :=
  ((n / 3 : ℕ) : ℝ) * aex b / (((n / 3 : ℕ) : ℝ) * (aex b + 1))

theorem fgMean_d {n : ℕ} {i : Fin n} (hi : εd n i = some 0) (b : ℝ) :
    fgMean (Xd n) (εd n) 0 Gex (zd n) b i = meanex n b := by
  rw [fgMean, fgWeightedSum_d hi, fgWeightedSum_d hi, meanex]
  norm_num

theorem filter_εd_sum (n : ℕ) (h : ℕ → ℝ) :
    ∑ i with εd n i = some 0, h (grp n i) = ((n / 3 : ℕ) : ℝ) * (h 0 + h 1) := by
  rw [sum_filter]
  simp only [εd]
  refine (sum_grp n (fun g => if εg g = some 0 then h g else 0)).trans ?_
  simp [εg]

/-- **The score of the replicated design**, computed from the definitions:
`Uₙ(b) = k (1 - 2 z̄(b))`. -/
theorem fgScore_d (n : ℕ) (b : ℝ) :
    fgScore (Xd n) (εd n) 0 Gex (zd n) b = ((n / 3 : ℕ) : ℝ) * (1 - 2 * meanex n b) := by
  rw [fgScore, sum_congr rfl fun i hi => by rw [fgMean_d (mem_filter.1 hi).2]]
  refine (filter_εd_sum n (fun g => zg g - meanex n b)).trans ?_
  simp only [zg]
  ring

/-- The true coefficient of the replicated design. -/
noncomputable def β₀ex : ℝ := log (2 / 3)

theorem aex_β₀ex : aex β₀ex = 1 := by
  rw [aex, β₀ex, exp_log (by norm_num)]; norm_num

/-- The score vanishes at `β₀ = log (2/3)`. -/
theorem fgScore_d_β₀ (n : ℕ) : fgScore (Xd n) (εd n) 0 Gex (zd n) β₀ex = 0 := by
  rw [fgScore_d, meanex, aex_β₀ex]
  rcases eq_or_ne ((n / 3 : ℕ) : ℝ) 0 with h | h
  · rw [h, zero_mul]
  · field_simp; ring

/-- `a / (a + 1)²`, the per-event variance. -/
noncomputable def uex (b : ℝ) : ℝ := aex b / (aex b + 1) ^ 2

/-- **The information of the replicated design**, computed from the definitions:
`Iₙ(b) = 2 k a / (a + 1)²`. -/
theorem fgInformation_d (n : ℕ) (b : ℝ) :
    fgInformation (Xd n) (εd n) 0 Gex (zd n) b = 2 * ((n / 3 : ℕ) : ℝ) * uex b := by
  have ha := aex_pos b
  rcases eq_or_ne ((n / 3 : ℕ) : ℝ) 0 with h | h
  · rw [fgInformation, sum_eq_zero fun i hi => ?_, h]
    · ring
    · rw [fgVar, fgMean_d (mem_filter.1 hi).2, fgWeightedSum_d (mem_filter.1 hi).2,
        fgWeightedSum_d (mem_filter.1 hi).2, meanex, h]
      simp
  · have hvar : ∀ i ∈ univ.filter (fun i => εd n i = some 0),
        fgVar (Xd n) (εd n) 0 Gex (zd n) b i = uex b := fun i hi => by
      rw [fgVar, fgMean_d (mem_filter.1 hi).2, fgWeightedSum_d (mem_filter.1 hi).2,
        fgWeightedSum_d (mem_filter.1 hi).2, meanex, uex]
      field_simp
      ring
    rw [fgInformation, sum_congr rfl hvar, sum_const, nsmul_eq_mul]
    have hcard := filter_εd_sum n (fun _ => 1)
    simp only [sum_const, nsmul_eq_mul, mul_one] at hcard
    rw [hcard]
    ring

/-- The limiting information `ifg b = (2/3) a / (a + 1)²`. -/
noncomputable def ifg (b : ℝ) : ℝ := 2 / 3 * uex b

theorem uex_nonneg (b : ℝ) : 0 ≤ uex b := by have := aex_pos b; unfold uex; positivity

theorem uex_le_one (b : ℝ) : uex b ≤ 1 := by
  have := aex_pos b
  rw [uex, div_le_one (by positivity)]
  nlinarith

theorem continuous_ifg : Continuous ifg := by
  unfold ifg uex aex
  exact continuous_const.mul ((continuous_const.mul continuous_exp).div (by fun_prop)
    fun b => by positivity)

/-- **The information limit at the true coefficient**, `v = ifg β₀ = 1/6`. -/
theorem ifg_β₀ex : ifg β₀ex = ((1 / 6 : NNReal) : ℝ) := by
  rw [ifg, uex, aex_β₀ex]; norm_num

/-- `|Iₙ(b) / n - ifg b| ≤ 2 / n`. -/
theorem abs_fgInformation_d_sub_le {n : ℕ} (hn : 0 < n) (b : ℝ) :
    |fgInformation (Xd n) (εd n) 0 Gex (zd n) b / n - ifg b| ≤ 2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 3 * ((n / 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n 3
  have h2 : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by
    have : n ≤ 3 * (n / 3) + 2 := by omega
    exact_mod_cast this
  rw [fgInformation_d, ifg, show 2 * ((n / 3 : ℕ) : ℝ) * uex b / n - 2 / 3 * uex b =
    -(uex b * (2 * (n - 3 * ((n / 3 : ℕ) : ℝ)) / (3 * n))) by field_simp; ring, abs_neg,
    abs_of_nonneg (mul_nonneg (uex_nonneg b) (div_nonneg (by linarith) (by positivity)))]
  calc uex b * (2 * (n - 3 * ((n / 3 : ℕ) : ℝ)) / (3 * n)) ≤ 1 * (2 / n) :=
        mul_le_mul (uex_le_one b) (by rw [div_le_div_iff₀ (by positivity) hn']; nlinarith)
          (div_nonneg (by linarith) (by positivity)) zero_le_one
    _ = 2 / n := one_mul _

/-- The Fine–Gray conditions hold for the replicated design on the one-point space, with
`β₀ = log (2/3)`, `r = 1`, `v = 1/6` and the deterministic score limit `Z = 0`. -/
theorem fineGrayConditions_d :
    FineGrayConditions (Measure.dirac ()) (Measure.dirac ()) (fun n _ => Xd n)
      (fun n _ => εd n) 0 (fun _ _ => Gex) (fun n _ => zd n) β₀ex 1 ifg (1 / 6)
      (fun _ => (0 : ℝ)) where
  weight_nonneg _ _ t := by unfold Gex; split_ifs <;> norm_num
  score := by
    simp only [fgScore_d_β₀, zero_div]
    exact tendstoInDistribution_const aemeasurable_const
  radius_pos := one_pos
  info_unif η hη := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop ⌈2 / η⌉₊] with n hn hnη
    symm
    convert measure_empty (μ := Measure.dirac ())
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ω ⟨b, -, hb⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : 2 / η < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hnη)
    have h2 : 2 / (n : ℝ) < η := by
      rw [div_lt_iff₀ hn']; rw [div_lt_iff₀ hη] at h1; linarith
    linarith [abs_fgInformation_d_sub_le hn b]
  info_continuousAt := continuous_ifg.continuousAt
  info_eq := ifg_β₀ex
  info_ne_zero := by norm_num

/-- **Consistency on the replicated design**: every Fine–Gray estimator is consistent for
`β₀ = log (2/3)`. -/
example (βhat : ℕ → Unit → ℝ)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (Xd n) (εd n) 0 Gex (zd n)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (Xd n) (εd n) 0 Gex (zd n)) Set.univ (βhat n ω)) :
    TendstoInMeasure (Measure.dirac ()) βhat atTop (fun _ => β₀ex) :=
  tendstoInMeasure_fgMPLE fineGrayConditions_d hβhat

/-- The constant `0` has the degenerate Gaussian law `N(0, 0)`. -/
theorem hasLaw_zero_gaussianReal :
    HasLaw (fun _ : Unit => (0 : ℝ)) (gaussianReal 0 0) (Measure.dirac ()) :=
  ⟨aemeasurable_const, by simp [gaussianReal_zero_var]⟩

/-- **Asymptotic normality on the replicated design**, with the limit variance
`σ² / v² = 0 / (1/6)² = 0`: `√n (βhat n - β₀) ⟶ 0`. -/
example (βhat : ℕ → Unit → ℝ)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (Xd n) (εd n) 0 Gex (zd n)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (Xd n) (εd n) 0 Gex (zd n)) Set.univ (βhat n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀ex)) atTop
      (fun _ => (0 : ℝ) / ((1 / 6 : NNReal) : ℝ)) (fun _ ↦ Measure.dirac ())
      (Measure.dirac ()) ∧
    HasLaw (fun _ : Unit => (0 : ℝ) / ((1 / 6 : NNReal) : ℝ)) (gaussianReal 0 0)
      (Measure.dirac ()) := by
  obtain ⟨h1, h2⟩ := tendstoInDistribution_fgMPLE_gaussian fineGrayConditions_d
    hasLaw_zero_gaussianReal hβhat (fun _ => (measurable_from_top (f := βhat _)).aemeasurable)
  exact ⟨h1, by simpa using h2⟩

/-- **The limit variance for this design's information limit `v = 1/6`**: a score limit
`N(0, σ²)` gives `√n (βhat n - β₀) ⟶ N(0, σ² / v²) = N(0, 36 σ²)`. -/
example (σ2 : NNReal) : σ2 / (1 / 6 : NNReal) ^ 2 = 36 * σ2 := by
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  norm_num

/-- The information at the estimator is consistent for `v = 1/6`. -/
example (βhat : ℕ → Unit → ℝ)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (Xd n) (εd n) 0 Gex (zd n)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (Xd n) (εd n) 0 Gex (zd n)) Set.univ (βhat n ω)) :
    TendstoInMeasure (Measure.dirac ())
      (fun n ω => fgInformation (Xd n) (εd n) 0 Gex (zd n) (βhat n ω) / n) atTop
      (fun _ => ((1 / 6 : NNReal) : ℝ)) :=
  tendstoInMeasure_fgInformation_fgMPLE fineGrayConditions_d hβhat

/-- `β₀ = log (2/3)` maximizes the criterion at every sample size (it is the root of the
score). -/
example (n : ℕ) : IsMaxOn (fgLogPartialLikelihood₁ (Xd n) (εd n) 0 Gex (zd n)) Set.univ β₀ex :=
  (isConcaveScore_fg (Xd n) (εd n) 0 (zd n) (fineGrayConditions_d.weight_nonneg n ())
    ).isMaxOn_of_score_eq_zero (fgScore_d_β₀ n)

/-! ### No competing events: the Cox case

Three subjects at times `1, 2, 3`, two cause-`0` failures and one censored subject, covariates
`1, 0, 4/5`. Computed from the definitions with `Gex`: at `b = 0` the first failure has weighted
mean `3/5` and the second `2/5` (the first subject left the risk set), so the Fine–Gray score
vanishes. Without competing events the Fine–Gray score, information and criterion are Cox's
for every `G`. -/

/-- Observed times. -/
noncomputable def X₃ : Fin 3 → ℝ := ![1, 2, 3]

/-- Two cause-`0` failures and a censored subject. -/
def ε₃ : Fin 3 → Option (Fin 2) := ![some 0, some 0, none]

/-- Covariates. -/
noncomputable def z₃ : Fin 3 → ℝ := ![1, 0, 4 / 5]

theorem noCompeting_ε₃ : ∀ l, ε₃ l = none ∨ ε₃ l = some 0 := by decide

theorem filter_ε₃ : univ.filter (fun i => ε₃ i = some 0) = {0, 1} := by decide

/-- The Fine–Gray score at `0`, computed from the definitions. -/
theorem fgScore_X₃ : fgScore X₃ ε₃ 0 Gex z₃ 0 = 0 := by
  rw [fgScore, filter_ε₃, sum_pair (by decide)]
  simp only [fgMean, fgWeightedSum, Fin.sum_univ_three, fgWeight]
  norm_num [X₃, ε₃, z₃]

/-- The reduction theorem gives the same value through the Cox score. -/
example : coxScore X₃ (causeIndicator ε₃ 0) z₃ 0 = 0 := by
  rw [← fgScore_eq_coxScore_of_noCompeting X₃ ε₃ 0 z₃ noCompeting_ε₃ (G := Gex), fgScore_X₃]

/-- The Fine–Gray information is the Cox information. -/
example (b : ℝ) : fgInformation X₃ ε₃ 0 Gex z₃ b = coxInformation X₃ (causeIndicator ε₃ 0) z₃ b :=
  fgInformation_eq_coxInformation_of_noCompeting X₃ ε₃ 0 z₃ noCompeting_ε₃ b

/-- The Fine–Gray estimator is the Cox estimator: `0` maximizes the Cox log partial
likelihood. -/
example : IsMaxOn (logPartialLikelihood₁ X₃ (causeIndicator ε₃ 0) z₃) Set.univ 0 := by
  rw [← fgLogPartialLikelihood₁_eq_of_noCompeting X₃ ε₃ 0 z₃ noCompeting_ε₃ (G := Gex)]
  exact (isConcaveScore_fg X₃ ε₃ 0 z₃ fun t => by unfold Gex; split_ifs <;> norm_num
    ).isMaxOn_of_score_eq_zero fgScore_X₃

/-! ### Degenerate weights: asymptotic normality is not claimed

Same group layout, but group `0` fails from cause `0` at time `2` with covariate `1`, groups `1`
and `2` fail from cause `1` at time `1` with covariate `0`, and group `3` is censored at `0`. The
censoring survival `Gdeg t = 1` for `t ≤ 1` and `0` after vanishes at the event time (positivity
fails), so every competing-event subject gets weight `Gdeg 2 / Gdeg 1 = 0`. The weighted risk set
of each failure is group `0`, where the covariate is constant: the information is identically
`0`, the score is identically `0`, and every `b` maximizes the criterion. The information limit
must then vanish at `β₀`, so `FineGrayConditions` (which needs `v ≠ 0`) cannot hold, and none of
the asymptotic theorems applies. With `G ≡ 1` the competing subjects return and the information
is positive. -/

/-- Status by group, degenerate design. -/
def εe : ℕ → Option (Fin 2)
  | 0 => some 0
  | 1 => some 1
  | 2 => some 1
  | _ => none

/-- Observed time by group, degenerate design. -/
def Xe : ℕ → ℝ
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | _ => 0

/-- Covariate by group, degenerate design. -/
def ze : ℕ → ℝ
  | 0 => 1
  | _ => 0

/-- A censoring survival vanishing after time `1`. -/
noncomputable def Gdeg (t : ℝ) : ℝ := if t ≤ 1 then 1 else 0

/-- Observed times of the degenerate design. -/
def Xde (n : ℕ) : Fin n → ℝ := fun l => Xe (grp n l)

/-- Statuses of the degenerate design. -/
def εde (n : ℕ) : Fin n → Option (Fin 2) := fun l => εe (grp n l)

/-- Covariates of the degenerate design. -/
def zde (n : ℕ) : Fin n → ℝ := fun l => ze (grp n l)

theorem grp_eq_zero_of_event_e {n : ℕ} {i : Fin n} (hi : εde n i = some 0) : grp n i = 0 := by
  have := grp_le n i
  simp only [εde] at hi
  interval_cases h : grp n i <;> simp_all [εe]

theorem wde_spec {g : ℕ} (hg : g ≤ 3) (hg0 : g ≠ 0) :
    (if 2 ≤ Xe g then 1 else if εe g ≠ none ∧ εe g ≠ some 0 then Gdeg 2 / Gdeg (Xe g) else 0) =
      0 := by
  interval_cases g
  · exact absurd rfl hg0
  all_goals norm_num [Xe, εe, Gdeg]

/-- At a failure, only group-`0` subjects (covariate `1`) have nonzero weight. -/
theorem fgWeight_de_eq_zero {n : ℕ} {i : Fin n} (hi : εde n i = some 0) {l : Fin n}
    (hl : grp n l ≠ 0) : fgWeight (Xde n) (εde n) 0 Gdeg l i = 0 := by
  have hXi : Xde n i = 2 := by simp [Xde, grp_eq_zero_of_event_e hi, Xe]
  unfold fgWeight
  rw [hXi]
  exact wde_spec (grp_le n l) hl

/-- All weighted sums at a failure coincide: `S_k = S₀`. -/
theorem fgWeightedSum_de {n : ℕ} {i : Fin n} (hi : εde n i = some 0) (k : ℕ) (b : ℝ) :
    fgWeightedSum (Xde n) (εde n) 0 Gdeg (zde n) k b i =
      fgWeightedSum (Xde n) (εde n) 0 Gdeg (zde n) 0 b i := by
  refine sum_congr rfl fun l _ => ?_
  by_cases hl : grp n l = 0
  · simp [zde, hl, ze]
  · simp [fgWeight_de_eq_zero hi hl]

theorem fgWeightedSum_de_pos {n : ℕ} (i : Fin n) (b : ℝ) :
    0 < fgWeightedSum (Xde n) (εde n) 0 Gdeg (zde n) 0 b i :=
  fgWeightedSum_zero_pos _ _ _ _ (fun t => by unfold Gdeg; split_ifs <;> norm_num) b i

/-- **The information of the degenerate design is identically zero.** -/
theorem fgInformation_de (n : ℕ) (b : ℝ) : fgInformation (Xde n) (εde n) 0 Gdeg (zde n) b = 0 := by
  refine sum_eq_zero fun i hi => ?_
  have hi' := (mem_filter.1 hi).2
  rw [fgVar, fgMean, fgWeightedSum_de hi' 2 b, fgWeightedSum_de hi' 1 b,
    div_self (fgWeightedSum_de_pos i b).ne']
  ring

/-- **The score of the degenerate design is identically zero**, so every `b` maximizes the
criterion and the data carry no information about `β`. -/
theorem fgScore_de (n : ℕ) (b : ℝ) : fgScore (Xde n) (εde n) 0 Gdeg (zde n) b = 0 := by
  refine sum_eq_zero fun i hi => ?_
  have hi' := (mem_filter.1 hi).2
  rw [fgMean, fgWeightedSum_de hi' 1 b, div_self (fgWeightedSum_de_pos i b).ne']
  simp [zde, grp_eq_zero_of_event_e hi', ze]

example (n : ℕ) (b : ℝ) : IsMaxOn (fgLogPartialLikelihood₁ (Xde n) (εde n) 0 Gdeg (zde n))
    Set.univ b :=
  (isConcaveScore_fg _ _ _ _ fun t => by unfold Gdeg; split_ifs <;> norm_num
    ).isMaxOn_of_score_eq_zero (fgScore_de n b)

/-- **Asymptotic normality is not claimed for degenerate weights**: no choice of `β₀`, `r`, `i`,
`v`, `Z` satisfies `FineGrayConditions` for the degenerate design, because the uniform
information hypothesis forces `i β₀ = 0`. -/
theorem not_fineGrayConditions_de {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω')
    [IsProbabilityMeasure P'] (β₀ r : ℝ) (i : ℝ → ℝ) (v : NNReal) (Z : Ω' → ℝ) :
    ¬ FineGrayConditions (Measure.dirac ()) P' (fun n _ => Xde n) (fun n _ => εde n) 0
      (fun _ _ => Gdeg) (fun n _ => zde n) β₀ r i v Z := by
  intro h
  have hi0 : i β₀ = 0 := by
    by_contra hne
    have hlim := h.info_unif |i β₀| (abs_pos.2 hne)
    have hone : ∀ n : ℕ, Measure.dirac () {_ω : Unit | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
        |i β₀| ≤ |fgInformation (Xde n) (εde n) 0 Gdeg (zde n) b / n - i b|} = 1 := fun n => by
      rw [Measure.dirac_apply_of_mem]
      exact ⟨β₀, ⟨by linarith [h.radius_pos], by linarith [h.radius_pos]⟩, by
        rw [fgInformation_de, zero_div, zero_sub, abs_neg]⟩
    simp only [hone] at hlim
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
  have hv0 : (v : ℝ) = 0 := by rw [← h.info_eq, hi0]
  exact h.info_ne_zero (by exact_mod_cast hv0)

/-- With `G ≡ 1` (no positivity failure) the competing subjects stay at full weight and the same
data have positive information: at `n = 3`, one subject per group `0, 1, 2`, the information at
`b = 0` is `1/3 - 1/9 = 2/9`. -/
example : fgInformation (Xde 3) (εde 3) 0 (fun _ => 1) (zde 3) 0 = 2 / 9 := by
  have hf : univ.filter (fun i => εde 3 i = some 0) = {0} := by decide
  rw [fgInformation, hf, sum_singleton]
  simp only [fgVar, fgMean, fgWeightedSum, Fin.sum_univ_three, fgWeight]
  norm_num [Xde, εde, zde, grp, Xe, εe, ze]

/-! ### The pre-`ConcaveScore` names still resolve -/

example {ℓ U I : ℝ → ℝ} (h₁ : ∀ b, HasDerivAt ℓ (U b) b) (h₂ : ∀ b, HasDerivAt U (-I b) b)
    (h₃ : ∀ b, 0 ≤ I b) :
    MathlibExt.Probability.Statistics.FineGrayAsymptotics.IsConcaveScore ℓ U I :=
  ⟨h₁, h₂, h₃⟩

example {ℓ U I : ℝ → ℝ}
    (h : MathlibExt.Probability.Statistics.FineGrayAsymptotics.IsConcaveScore ℓ U I) :
    Antitone U ∧ ∀ b, 0 ≤ I b :=
  ⟨MathlibExt.Probability.Statistics.FineGrayAsymptotics.IsConcaveScore.antitone_score h,
    MathlibExt.Probability.Statistics.FineGrayAsymptotics.IsConcaveScore.info_nonneg h⟩

example {ℓ U I : ℝ → ℝ}
    (h : MathlibExt.Probability.Statistics.FineGrayAsymptotics.IsConcaveScore ℓ U I) :
    Continuous U :=
  h.continuous_score

example {n : ℕ} (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → ℝ) :
    MathlibExt.Probability.Statistics.FineGrayAsymptotics.IsConcaveScore
      (logPartialLikelihood₁ T δ z) (coxScore T δ z) (coxInformation T δ z) :=
  MathlibExt.Probability.Statistics.FineGrayAsymptotics.isConcaveScore_cox T δ z

#print axioms MathlibExt.Probability.Statistics.FineGrayAsymptotics.tendstoInMeasure_argmax
#print axioms MathlibExt.Probability.Statistics.FineGrayAsymptotics.IsConcaveScore.mk

#print axioms IsConcaveScore.isMaxOn_of_score_eq_zero
#print axioms IsConcaveScore.abs_sqrt_mul_sub_sub_le
#print axioms tendstoInMeasure_argmax
#print axioms tendstoInDistribution_argmax
#print axioms isConcaveScore_fg
#print axioms isConcaveScore_cox
#print axioms log_fgWeightedPartialLikelihood
#print axioms fgScore_eq_coxScore_of_noCompeting
#print axioms fgInformation_eq_coxInformation_of_noCompeting
#print axioms fgLogPartialLikelihood₁_eq_of_noCompeting
#print axioms tendsto_measure_not_exists_isMaxOn_fg
#print axioms tendstoInMeasure_fgMPLE
#print axioms tendstoInDistribution_fgMPLE
#print axioms tendstoInDistribution_fgMPLE_gaussian
#print axioms tendstoInMeasure_fgInformation_fgMPLE
#print axioms hasSubdistHazardAt_two_cause
#print axioms fineGrayConditions_d
#print axioms not_fineGrayConditions_de

end MathlibExtTest.Probability.Statistics.FineGrayAsymptotics
