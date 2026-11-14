/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGrayAsymptotics
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
import MathlibExt.Probability.Statistics.Slutsky

/-!
# A Fine–Gray score CLT on a product space

The Fine–Gray asymptotic-normality theorem `tendstoInDistribution_fgMPLE_gaussian` of
`FineGrayAsymptotics` assumes the score limit `Uₙ(β₀) / √n ⟶ N(0, σ²)` and a uniform law for the
information. This file gives a product-space model where both are proved, with a score variance
`σ² > 0` computed from the model, and instantiates the theorem there.

## The paired product model

A pair outcome `x : S` carries two statuses `εa x, εb x : Option ι` (`none` = censored, `some c`
= cause `c`, other causes competing). The sample space is `ℕ → S` with the product measure
`pairModel μ₀ = Measure.infinitePi (fun _ => μ₀)`: the pairs `ω 0, ω 1, …` are independent with
common law `μ₀`; the law of the two statuses within a pair is arbitrary. At sample size `n` the
first `2 (n / 2)` subjects form the pairs: subject `2k` has covariate `1` and status `εa (ω k)`,
subject `2k + 1` has covariate `0` and status `εb (ω k)`, and all are observed at time `1`
(`pairTime`, `pairCov`, `pairStatus`); an unpaired last subject is censored at time `0`.

Every Fine–Gray risk set then holds exactly the paired subjects with weight `1`, for every weight
function `G` (`fgWeight_pair`), so `S_k(b) = (n / 2) (eᵇ + 0ᵏ)`, the risk-set mean is
`m(b) = eᵇ / (eᵇ + 1)`, and

* `Uₙ(b) = ∑_{k < n / 2} pairScore b (ω k)` with
  `pairScore b x = (1 - m(b)) 1[εa x = c] - m(b) 1[εb x = c]` (`fgScore_pair`);
* `Iₙ(b) = (∑_{k < n / 2} pairEvents (ω k)) m(b) (1 - m(b))` (`fgInformation_pair`).

With `p_a = μ₀ {εa = c}` and `p_b = μ₀ {εb = c}`, the true coefficient is `β₀` with
`e^{β₀} p_b = p_a` (a subdistribution hazard ratio `e^{β₀}` between covariates `1` and `0`); then
`E[pairScore β₀] = 0` (`integral_pairScore_eq_zero`).

## Main results

* `tendstoInDistribution_fgScore_pair` (**score CLT**): `Uₙ(β₀) / √n ⟶ N(0, σ²)` with
  `σ² = pairσ2 = E[pairScore β₀ ²] / 2`, from Mathlib's i.i.d. central limit theorem over pairs,
  reindexing `n ↦ n / 2`, and Slutsky with the factor `√((n / 2) / n) → √(1 / 2)`.
* `pairσ2_pos`: `σ² > 0` as soon as `μ₀ {εa = c, εb ≠ c} > 0`.
* `tendstoInMeasure_pairEvents_div`: `(∑_{k < n / 2} pairEvents (ω k)) / n → (p_a + p_b) / 2` in
  probability (strong law of large numbers).
* `fineGrayConditions_pair`: the paired product model satisfies `FineGrayConditions` with
  information limit `i(b) = ((p_a + p_b) / 2) m(b) (1 - m(b))` and `v = i(β₀)` (`p_b > 0`).
* `tendstoInDistribution_fgMPLE_pair` (**asymptotic normality**): every Fine–Gray estimator
  satisfies `√n (βhat n - β₀) ⟶ Z / v ~ N(0, σ² / v²)`.

## Scope

The model ties all observation times, so the Fine–Gray weights do not involve `G` and the
estimated-censoring (`ψ`) terms of the general Fine–Gray score variance vanish; it is a
non-degenerate instance of the abstract theorem, not a derivation of the score CLT for general
continuous-time data. Independence across pairs is essential: the test file shows that copying one
pair to every coordinate (a dependent, non-product law with the same marginals) has no limit.

## Source receipt

* J. P. Fine and R. J. Gray, *A proportional hazards model for the subdistribution of a
  competing risk*, J. Amer. Statist. Assoc. 94 (1999), 496–509, Section 3.
* Reused, not reproved: `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` (CLT) and
  `ProbabilityTheory.strong_law_ae_real` (SLLN) from Mathlib; `fgScore`, `fgInformation`,
  `FineGrayConditions`, `tendstoInDistribution_fgMPLE_gaussian` from `FineGrayAsymptotics`;
  `TendstoInDistribution.mul_of_tendstoInMeasure_const`, `TendstoInDistribution.congr_hasLaw`
  from `Slutsky`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.FineGrayScoreCLT

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.FineGrayAsymptotics

/-! ### The paired design -/

section Design

variable {S ι : Type*} [DecidableEq ι] (εa εb : S → Option ι) (c : ι)

/-- Status of subject `j` of the infinite paired sequence: subject `2k` is the covariate-`1`
member of pair `k`, with status `εa (ω k)`, and subject `2k + 1` the covariate-`0` member, with
status `εb (ω k)`. -/
def pairStatusSeq (ω : ℕ → S) (j : ℕ) : Option ι :=
  if j % 2 = 0 then εa (ω (j / 2)) else εb (ω (j / 2))

/-- Observed times at sample size `n`: the `n / 2` complete pairs are observed at time `1`; an
unpaired last subject (odd `n`) is censored at time `0`. -/
def pairTime (n : ℕ) (j : Fin n) : ℝ := if (j : ℕ) < 2 * (n / 2) then 1 else 0

/-- Covariates at sample size `n`: `1` for the first member of each pair, `0` otherwise. -/
def pairCov (n : ℕ) (j : Fin n) : ℝ :=
  if (j : ℕ) < 2 * (n / 2) then (if (j : ℕ) % 2 = 0 then 1 else 0) else 0

/-- Statuses at sample size `n`: the paired statuses, and censored (`none`) for an unpaired last
subject. -/
def pairStatus (n : ℕ) (ω : ℕ → S) (j : Fin n) : Option ι :=
  if (j : ℕ) < 2 * (n / 2) then pairStatusSeq εa εb ω j else none

/-- The risk-set covariate mean `m(b) = eᵇ / (eᵇ + 1)` of the paired design. -/
noncomputable def pairMean (b : ℝ) : ℝ := exp b / (exp b + 1)

/-- The per-event covariate variance `m(b) (1 - m(b))` of the paired design. -/
noncomputable def pairVarFn (b : ℝ) : ℝ := pairMean b * (1 - pairMean b)

/-- The **score contribution of one pair** at `b`: `(1 - m(b))` if its covariate-`1` member
fails from cause `c`, minus `m(b)` if its covariate-`0` member does. -/
noncomputable def pairScore (b : ℝ) (x : S) : ℝ :=
  (if εa x = some c then 1 - pairMean b else 0) + (if εb x = some c then -pairMean b else 0)

/-- The number of cause-`c` events in one pair. -/
noncomputable def pairEvents (x : S) : ℝ :=
  (if εa x = some c then 1 else 0) + (if εb x = some c then 1 else 0)

/-- Summing over the complete pairs of a sample of size `n`. -/
theorem sum_fin_pair (n : ℕ) (F : ℕ → ℝ) :
    ∑ j : Fin n, (if (j : ℕ) < 2 * (n / 2) then F j else 0) =
      ∑ k ∈ range (n / 2), (F (2 * k) + F (2 * k + 1)) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < 2 * (n / 2) then F j else 0) n]
  rw [← sum_range_add_sum_Ico _ (show 2 * (n / 2) ≤ n by omega),
    sum_eq_zero (s := Ico _ _) fun x hx => ite_eq_right_iff.2 fun h => absurd h
      (by rw [mem_Ico] at hx; omega), add_zero,
    sum_congr rfl fun j hj => ite_eq_left_iff.2 fun h => absurd (mem_range.1 hj) h]
  generalize n / 2 = K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

variable {εa εb c}

omit [DecidableEq ι] in
/-- A cause-`c` event belongs to a complete pair. -/
theorem lt_of_pairStatus_eq {n : ℕ} {ω : ℕ → S} {i : Fin n}
    (hi : pairStatus εa εb n ω i = some c) : (i : ℕ) < 2 * (n / 2) := by
  by_contra h
  simp [pairStatus, h] at hi

/-- At a cause-`c` event every paired subject has weight `1` and the unpaired one weight `0`, for
every `G`. -/
theorem fgWeight_pair {n : ℕ} {ω : ℕ → S} (G : ℝ → ℝ) {i : Fin n}
    (hi : pairStatus εa εb n ω i = some c) (l : Fin n) :
    fgWeight (pairTime n) (pairStatus εa εb n ω) c G l i =
      if (l : ℕ) < 2 * (n / 2) then 1 else 0 := by
  have hi' := lt_of_pairStatus_eq hi
  unfold fgWeight
  by_cases hl : (l : ℕ) < 2 * (n / 2)
  · simp [pairTime, hi', hl]
  · simp [pairTime, pairStatus, hi', hl]

/-- The weighted sums of the paired design at a cause-`c` event:
`S_k(b) = (n / 2) (eᵇ + 0 ^ k)`. -/
theorem fgWeightedSum_pair {n : ℕ} {ω : ℕ → S} (G : ℝ → ℝ) {i : Fin n}
    (hi : pairStatus εa εb n ω i = some c) (k : ℕ) (b : ℝ) :
    fgWeightedSum (pairTime n) (pairStatus εa εb n ω) c G (pairCov n) k b i =
      ((n / 2 : ℕ) : ℝ) * (exp b + (0 : ℝ) ^ k) := by
  rw [fgWeightedSum]
  simp only [fgWeight_pair G hi, pairCov, ite_mul, one_mul, zero_mul]
  rw [sum_congr rfl fun l _ => ?_, sum_fin_pair n
    (fun j => (if j % 2 = 0 then (1 : ℝ) else 0) ^ k * exp (b * if j % 2 = 0 then 1 else 0))]
  · simp [Nat.add_mod]
    ring
  · split_ifs <;> rfl

/-- The risk-set mean of the paired design at a cause-`c` event is `m(b)`. -/
theorem fgMean_pair {n : ℕ} {ω : ℕ → S} (G : ℝ → ℝ) {i : Fin n}
    (hi : pairStatus εa εb n ω i = some c) (b : ℝ) :
    fgMean (pairTime n) (pairStatus εa εb n ω) c G (pairCov n) b i = pairMean b := by
  have hK : ((n / 2 : ℕ) : ℝ) ≠ 0 := by
    have := lt_of_pairStatus_eq hi
    exact_mod_cast (show n / 2 ≠ 0 by omega)
  rw [fgMean, fgWeightedSum_pair G hi, fgWeightedSum_pair G hi, pairMean, pow_one, pow_zero,
    add_zero, mul_div_mul_left _ _ hK]

/-- The per-event variance of the paired design at a cause-`c` event is `m(b) (1 - m(b))`. -/
theorem fgVar_pair {n : ℕ} {ω : ℕ → S} (G : ℝ → ℝ) {i : Fin n}
    (hi : pairStatus εa εb n ω i = some c) (b : ℝ) :
    fgVar (pairTime n) (pairStatus εa εb n ω) c G (pairCov n) b i = pairVarFn b := by
  have hK : ((n / 2 : ℕ) : ℝ) ≠ 0 := by
    have := lt_of_pairStatus_eq hi
    exact_mod_cast (show n / 2 ≠ 0 by omega)
  rw [fgVar, fgMean_pair G hi, fgWeightedSum_pair G hi, fgWeightedSum_pair G hi, pairVarFn,
    pow_zero, zero_pow two_ne_zero, add_zero, mul_div_mul_left _ _ hK, ← pairMean]
  ring

/-- A sum over the cause-`c` events of the paired design is a sum over pairs. -/
theorem sum_filter_pairStatus (n : ℕ) (ω : ℕ → S) (f : ℕ → ℝ) :
    ∑ i with pairStatus εa εb n ω i = some c, f i =
      ∑ k ∈ range (n / 2), ((if εa (ω k) = some c then f (2 * k) else 0) +
        (if εb (ω k) = some c then f (2 * k + 1) else 0)) := by
  rw [sum_filter]
  have h : ∀ j : Fin n, (if pairStatus εa εb n ω j = some c then f j else 0) =
      if (j : ℕ) < 2 * (n / 2) then
        (if pairStatusSeq εa εb ω j = some c then f j else 0) else 0 := fun j => by
    by_cases hj : (j : ℕ) < 2 * (n / 2) <;> simp [pairStatus, hj]
  rw [sum_congr rfl fun j _ => h j, sum_fin_pair n
    (fun j => if pairStatusSeq εa εb ω j = some c then f j else 0)]
  refine sum_congr rfl fun k _ => ?_
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [pairStatusSeq, h1, h2]

/-- **The Fine–Gray score of the paired design is a sum over pairs**: for every `G`,
`Uₙ(b) = ∑_{k < n / 2} pairScore b (ω k)`. -/
theorem fgScore_pair (n : ℕ) (ω : ℕ → S) (G : ℝ → ℝ) (b : ℝ) :
    fgScore (pairTime n) (pairStatus εa εb n ω) c G (pairCov n) b =
      ∑ k ∈ range (n / 2), pairScore εa εb c b (ω k) := by
  rw [fgScore, sum_congr rfl fun i hi => by
    rw [fgMean_pair G (mem_filter.1 hi).2, pairCov],
    sum_filter_pairStatus n ω (fun j =>
      (if j < 2 * (n / 2) then (if j % 2 = 0 then 1 else 0) else 0) - pairMean b)]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.1 hk
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : 2 * k < 2 * (n / 2) := by omega
  have h3 : 2 * k + 1 < 2 * (n / 2) := by omega
  simp [pairScore, h1, h2, h3]

/-- **The Fine–Gray information of the paired design**: for every `G`,
`Iₙ(b) = (∑_{k < n / 2} pairEvents (ω k)) m(b) (1 - m(b))`. -/
theorem fgInformation_pair (n : ℕ) (ω : ℕ → S) (G : ℝ → ℝ) (b : ℝ) :
    fgInformation (pairTime n) (pairStatus εa εb n ω) c G (pairCov n) b =
      (∑ k ∈ range (n / 2), pairEvents εa εb c (ω k)) * pairVarFn b := by
  rw [fgInformation, sum_congr rfl fun i hi => fgVar_pair G (mem_filter.1 hi).2 b,
    sum_filter_pairStatus n ω (fun _ => pairVarFn b), sum_mul]
  refine sum_congr rfl fun k _ => ?_
  simp only [pairEvents, add_mul, ite_mul, one_mul, zero_mul]

end Design

/-! ### Elementary facts about `m(b)` -/

theorem pairMean_pos (b : ℝ) : 0 < pairMean b := by unfold pairMean; positivity

theorem pairMean_lt_one (b : ℝ) : pairMean b < 1 := by
  rw [pairMean, div_lt_one (by positivity)]
  linarith

theorem pairVarFn_pos (b : ℝ) : 0 < pairVarFn b :=
  mul_pos (pairMean_pos b) (sub_pos.2 (pairMean_lt_one b))

theorem pairVarFn_le_one (b : ℝ) : pairVarFn b ≤ 1 := by
  have h0 := pairMean_pos b
  have h1 := pairMean_lt_one b
  unfold pairVarFn
  nlinarith

theorem continuous_pairMean : Continuous pairMean :=
  continuous_exp.div (continuous_exp.add continuous_const) fun b => by positivity

theorem continuous_pairVarFn : Continuous pairVarFn :=
  continuous_pairMean.mul (continuous_const.sub continuous_pairMean)

/-! ### The product-space model -/

section Model

variable {S ι : Type*} [DecidableEq ι] {mS : MeasurableSpace S} (μ₀ : Measure S)
  (εa εb : S → Option ι) (c : ι)

/-- **The product-space model**: the pairs `ω k`, `k : ℕ`, are independent with common law `μ₀`
(the law of the two statuses within a pair is arbitrary). -/
noncomputable abbrev pairModel : Measure (ℕ → S) := Measure.infinitePi fun _ : ℕ => μ₀

/-- `p_a`: the probability that the covariate-`1` member of a pair fails from cause `c`. -/
noncomputable def pairProbA : ℝ := μ₀.real {x | εa x = some c}

/-- `p_b`: the probability that the covariate-`0` member of a pair fails from cause `c`. -/
noncomputable def pairProbB : ℝ := μ₀.real {x | εb x = some c}

/-- **The limit variance of the normalized score**, `σ² = E[pairScore β₀ ²] / 2`: the variance of
one pair's score contribution, halved because a sample of size `n` holds `n / 2` pairs. -/
noncomputable def pairσ2 (β₀ : ℝ) : NNReal :=
  ⟨(∫ x, pairScore εa εb c β₀ x ^ 2 ∂μ₀) / 2,
    div_nonneg (integral_nonneg fun _ => sq_nonneg _) zero_le_two⟩

/-- The information limit `i(b) = ((p_a + p_b) / 2) m(b) (1 - m(b))`. -/
noncomputable def pairInfoLimit (b : ℝ) : ℝ :=
  (pairProbA μ₀ εa c + pairProbB μ₀ εb c) / 2 * pairVarFn b

omit [DecidableEq ι] in
theorem pairInfoLimit_nonneg (b : ℝ) : 0 ≤ pairInfoLimit μ₀ εa εb c b :=
  mul_nonneg (div_nonneg (add_nonneg measureReal_nonneg measureReal_nonneg) zero_le_two)
    (pairVarFn_pos b).le

/-- The information limit at `β₀`, `v = i(β₀)`. -/
noncomputable def pairV (β₀ : ℝ) : NNReal := ⟨pairInfoLimit μ₀ εa εb c β₀, pairInfoLimit_nonneg ..⟩

variable {εa εb c}

theorem pairScore_eq_indicator (b : ℝ) :
    pairScore εa εb c b = fun x => {x | εa x = some c}.indicator (fun _ => 1 - pairMean b) x +
      {x | εb x = some c}.indicator (fun _ => -pairMean b) x := by
  funext x
  simp [pairScore, Set.indicator_apply]

theorem pairEvents_eq_indicator :
    pairEvents εa εb c = fun x => {x | εa x = some c}.indicator (fun _ => (1 : ℝ)) x +
      {x | εb x = some c}.indicator (fun _ => 1) x := by
  funext x
  simp [pairEvents, Set.indicator_apply]

variable (hA : MeasurableSet {x | εa x = some c}) (hB : MeasurableSet {x | εb x = some c})
include hA hB

theorem measurable_pairScore (b : ℝ) : Measurable (pairScore εa εb c b) :=
  (Measurable.ite hA measurable_const measurable_const).add
    (Measurable.ite hB measurable_const measurable_const)

theorem measurable_pairEvents : Measurable (pairEvents εa εb c) :=
  (Measurable.ite hA measurable_const measurable_const).add
    (Measurable.ite hB measurable_const measurable_const)

omit hA hB in
theorem abs_pairScore_le (b : ℝ) (x : S) : |pairScore εa εb c b x| ≤ 2 := by
  have h0 := pairMean_pos b
  have h1 := pairMean_lt_one b
  unfold pairScore
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

omit hA hB in
theorem abs_pairEvents_le (x : S) : |pairEvents εa εb c x| ≤ 2 := by
  unfold pairEvents
  split_ifs <;> norm_num

variable [IsProbabilityMeasure μ₀]

theorem integral_pairScore (b : ℝ) :
    ∫ x, pairScore εa εb c b x ∂μ₀ =
      pairProbA μ₀ εa c * (1 - pairMean b) - pairProbB μ₀ εb c * pairMean b := by
  rw [pairScore_eq_indicator, integral_add ((integrable_const _).indicator hA)
    ((integrable_const _).indicator hB), integral_indicator_const _ hA,
    integral_indicator_const _ hB, pairProbA, pairProbB, smul_eq_mul, smul_eq_mul]
  ring

theorem integral_pairEvents :
    ∫ x, pairEvents εa εb c x ∂μ₀ = pairProbA μ₀ εa c + pairProbB μ₀ εb c := by
  rw [pairEvents_eq_indicator, integral_add ((integrable_const _).indicator hA)
    ((integrable_const _).indicator hB), integral_indicator_const _ hA,
    integral_indicator_const _ hB, pairProbA, pairProbB, smul_eq_mul, smul_eq_mul, mul_one,
    mul_one]

/-- **Centering**: under the proportional subdistribution-hazards relation `e^{β₀} p_b = p_a`, a
pair's score contribution at `β₀` has mean zero. -/
theorem integral_pairScore_eq_zero {β₀ : ℝ}
    (hβ₀ : exp β₀ * pairProbB μ₀ εb c = pairProbA μ₀ εa c) :
    ∫ x, pairScore εa εb c β₀ x ∂μ₀ = 0 := by
  rw [integral_pairScore μ₀ hA hB, ← hβ₀, pairMean]
  have : exp β₀ + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **Positivity of the score variance**: if with positive probability the covariate-`1` member of
a pair fails from cause `c` and the covariate-`0` member does not, then `σ² > 0`. -/
theorem pairσ2_pos (β₀ : ℝ)
    (hpos : 0 < μ₀.real {x | εa x = some c ∧ εb x ≠ some c}) :
    0 < pairσ2 μ₀ εa εb c β₀ := by
  set T := {x | εa x = some c ∧ εb x ≠ some c}
  have hT : MeasurableSet T := hA.inter hB.compl
  have hY := measurable_pairScore hA hB β₀ (εa := εa) (εb := εb) (c := c)
  have hle : ∫ x, T.indicator (fun _ => (1 - pairMean β₀) ^ 2) x ∂μ₀ ≤
      ∫ x, pairScore εa εb c β₀ x ^ 2 ∂μ₀ := by
    refine integral_mono ((integrable_const _).indicator hT)
      ((memLp_top_of_bound (hY.pow_const 2).aestronglyMeasurable 4 (ae_of_all _ fun x => ?_)
        ).integrable le_top) fun x => ?_
    · rw [Real.norm_eq_abs, abs_pow]
      have := abs_pairScore_le (εa := εa) (εb := εb) (c := c) β₀ x
      nlinarith [abs_nonneg (pairScore εa εb c β₀ x)]
    · by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        simp [pairScore, hx.1, hx.2]
      · rw [Set.indicator_of_notMem hx]
        exact sq_nonneg _
  rw [integral_indicator_const _ hT, smul_eq_mul] at hle
  have h1 : 0 < (1 - pairMean β₀) ^ 2 := pow_pos (sub_pos.2 (pairMean_lt_one β₀)) 2
  change 0 < (∫ x, pairScore εa εb c β₀ x ^ 2 ∂μ₀) / 2
  have := mul_pos hpos h1
  linarith

end Model

/-! ### Transfer from a coordinate to the component law -/

section Transfer

variable {S : Type*} {mS : MeasurableSpace S} (μ₀ : Measure S) [IsProbabilityMeasure μ₀]

theorem map_pairModel_comp {f : S → ℝ} (hf : Measurable f) (k : ℕ) :
    (pairModel μ₀).map (fun ω => f (ω k)) = μ₀.map f := by
  rw [show (fun ω : ℕ → S => f (ω k)) = f ∘ fun ω => ω k from rfl,
    ← Measure.map_map hf (measurable_pi_apply k), Measure.infinitePi_map_eval]

theorem identDistrib_pairModel {f : S → ℝ} (hf : Measurable f) (k : ℕ) :
    IdentDistrib (fun ω : ℕ → S => f (ω k)) (fun ω => f (ω 0)) (pairModel μ₀) (pairModel μ₀) :=
  ⟨(hf.comp (measurable_pi_apply k)).aemeasurable, (hf.comp (measurable_pi_apply 0)).aemeasurable,
    by rw [map_pairModel_comp μ₀ hf, map_pairModel_comp μ₀ hf]⟩

theorem iIndepFun_pairModel {f : S → ℝ} (hf : Measurable f) :
    iIndepFun (fun k (ω : ℕ → S) => f (ω k)) (pairModel μ₀) :=
  iIndepFun_infinitePi (P := fun _ : ℕ => μ₀) (X := fun _ => f) fun _ => hf

theorem integral_pairModel {f : S → ℝ} (hf : Measurable f) (k : ℕ) :
    ∫ ω, f (ω k) ∂(pairModel μ₀) = ∫ x, f x ∂μ₀ := by
  rw [← integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable,
    Measure.infinitePi_map_eval]

end Transfer

/-! ### Deterministic limits of the pair count -/

/-- `(n / 2) / n → 1 / 2`. -/
theorem tendsto_div_two_div : Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  have hlow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - (1 / 2) / n) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
    rw [show (1 / 2 : ℝ) - 1 / 2 / n = (n - 1) / (2 * n) by field_simp,
      div_le_div_iff₀ (by positivity) hn']
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : 2 * ((n / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n 2
    rw [div_le_iff₀ hn']
    linarith

/-! ### The score CLT -/

section ScoreCLT

variable {S ι : Type*} [DecidableEq ι] {mS : MeasurableSpace S} {μ₀ : Measure S}
  [IsProbabilityMeasure μ₀] {εa εb : S → Option ι} {c : ι} {β₀ : ℝ}

/-- The normalized score is `√((n / 2) / n)` times the CLT-normalized sum over pairs. -/
theorem fgScore_pair_div_sqrt (n : ℕ) (ω : ℕ → S) (G : ℝ → ℝ) :
    fgScore (pairTime n) (pairStatus εa εb n ω) c G (pairCov n) β₀ / √(n : ℝ) =
      (√((n / 2 : ℕ) : ℝ))⁻¹ * (∑ k ∈ range (n / 2), pairScore εa εb c β₀ (ω k)) *
        √(((n / 2 : ℕ) : ℝ) / n) := by
  rw [fgScore_pair, Real.sqrt_div (Nat.cast_nonneg _)]
  rcases Nat.eq_zero_or_pos (n / 2) with h | h
  · simp [h]
  · have hK : 0 < √((n / 2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h)
    field_simp

/-- **Score CLT on the product space.** In the paired design with i.i.d. pairs of law `μ₀`, if
`e^{β₀} p_b = p_a` then the normalized Fine–Gray score `Uₙ(β₀) / √n` converges in distribution to
`N(0, σ²)` with `σ² = pairσ2 = E[pairScore β₀ ²] / 2`, for every choice of weight functions `G`. -/
theorem tendstoInDistribution_fgScore_pair {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ} (G : ℕ → (ℕ → S) → ℝ → ℝ)
    (hA : MeasurableSet {x | εa x = some c}) (hB : MeasurableSet {x | εb x = some c})
    (hβ₀ : exp β₀ * pairProbB μ₀ εb c = pairProbA μ₀ εa c)
    (hZ : HasLaw Z (gaussianReal 0 (pairσ2 μ₀ εa εb c β₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ fgScore (pairTime n) (pairStatus εa εb n ω) c (G n ω) (pairCov n) β₀ /
        √(n : ℝ)) atTop Z (fun _ ↦ pairModel μ₀) P' := by
  set Y := pairScore εa εb c β₀ with hYdef
  have hY : Measurable Y := measurable_pairScore hA hB β₀
  set X : ℕ → (ℕ → S) → ℝ := fun k ω => Y (ω k) with hXdef
  have hmean : (pairModel μ₀)[X 0] = 0 := by
    rw [hXdef, integral_pairModel μ₀ hY, integral_pairScore_eq_zero μ₀ hA hB hβ₀]
  have hmemLp : MemLp (X 0) 2 (pairModel μ₀) :=
    MemLp.of_bound (hY.comp (measurable_pi_apply 0)).aestronglyMeasurable 2
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_pairScore_le β₀ _)
  have hvar : Var[X 0; pairModel μ₀] = ∫ x, Y x ^ 2 ∂μ₀ := by
    rw [hXdef, (measurePreserving_eval_infinitePi (fun _ : ℕ => μ₀) 0).variance_fun_comp
      hY.aemeasurable, variance_of_integral_eq_zero hY.aemeasurable
      (integral_pairScore_eq_zero μ₀ hA hB hβ₀)]
  -- Mathlib's CLT for the pair sums, with limit `id` under `N(0, Var)`.
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P' := gaussianReal 0 Var[X 0; pairModel μ₀].toNNReal) HasLaw.id hmemLp
    (iIndepFun_pairModel μ₀ hY) (identDistrib_pairModel μ₀ hY)
  simp only [hmean, mul_zero, sub_zero] at hCLT
  -- Reindex along `n ↦ n / 2`.
  have hre : TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√((n / 2 : ℕ) : ℝ))⁻¹ * ∑ k ∈ range (n / 2), X k ω) atTop id
      (fun _ ↦ pairModel μ₀) (gaussianReal 0 Var[X 0; pairModel μ₀].toNNReal) :=
    ⟨fun n => hCLT.forall_aemeasurable (n / 2), hCLT.aemeasurable_limit,
      hCLT.tendsto.comp (Nat.tendsto_div_const_atTop two_ne_zero)⟩
  -- Slutsky with the deterministic factor `√((n / 2) / n) → √(1 / 2)`.
  have hcoef : TendstoInMeasure (pairModel μ₀)
      (fun (n : ℕ) (_ : ℕ → S) => √(((n / 2 : ℕ) : ℝ) / n)) atTop (fun _ => √(1 / 2)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => (continuous_sqrt.tendsto _).comp tendsto_div_two_div)
  have hS := hre.mul_of_tendstoInMeasure_const hcoef fun _ => aemeasurable_const
  -- The limit `√(1 / 2) · N(0, Var)` is `N(0, σ²)`.
  have hlaw : HasLaw (fun y : ℝ => √(1 / 2) * id y) (gaussianReal 0 (pairσ2 μ₀ εa εb c β₀))
      (gaussianReal 0 Var[X 0; pairModel μ₀].toNNReal) := by
    refine ⟨by fun_prop, ?_⟩
    rw [show (fun y : ℝ => √(1 / 2) * id y) = fun y => √(1 / 2) * y from rfl,
      gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    rw [NNReal.coe_mul, NNReal.coe_mk, Real.sq_sqrt (by norm_num),
      Real.coe_toNNReal _ (variance_nonneg _ _), hvar]
    change 1 / 2 * ∫ x, Y x ^ 2 ∂μ₀ = (∫ x, Y x ^ 2 ∂μ₀) / 2
    ring
  refine (hS.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)).congr_hasLaw
    hlaw hZ
  exact (fgScore_pair_div_sqrt n ω (G n ω)).symm

end ScoreCLT

/-! ### The information limit and the Fine–Gray conditions -/

section Conditions

variable {S ι : Type*} [DecidableEq ι] {mS : MeasurableSpace S} {μ₀ : Measure S}
  [IsProbabilityMeasure μ₀] {εa εb : S → Option ι} {c : ι} {β₀ : ℝ}

/-- **Law of large numbers for the event count**: `(∑_{k < n / 2} pairEvents (ω k)) / n` converges
in probability to `(p_a + p_b) / 2`. -/
theorem tendstoInMeasure_pairEvents_div (hA : MeasurableSet {x | εa x = some c})
    (hB : MeasurableSet {x | εb x = some c}) :
    TendstoInMeasure (pairModel μ₀)
      (fun (n : ℕ) ω => (∑ k ∈ range (n / 2), pairEvents εa εb c (ω k)) / n) atTop
      (fun _ => (pairProbA μ₀ εa c + pairProbB μ₀ εb c) / 2) := by
  have hE : Measurable (pairEvents εa εb c) := measurable_pairEvents hA hB
  have hSLLN := strong_law_ae_real (μ := pairModel μ₀) (fun k ω => pairEvents εa εb c (ω k))
    ((integrable_map_measure hE.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).1 (by
        rw [Measure.infinitePi_map_eval]
        exact (memLp_top_of_bound hE.aestronglyMeasurable 2 (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]; exact abs_pairEvents_le x)).integrable le_top))
    (fun i j hij => (iIndepFun_pairModel μ₀ hE).indepFun hij) (identDistrib_pairModel μ₀ hE)
  rw [integral_pairModel μ₀ hE, integral_pairEvents μ₀ hA hB] at hSLLN
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact ((Finset.measurable_sum _ fun k _ => hE.comp (measurable_pi_apply k)).div_const
      _).aestronglyMeasurable
  · filter_upwards [hSLLN] with ω hω
    have h := (hω.comp (Nat.tendsto_div_const_atTop two_ne_zero)).mul tendsto_div_two_div
    rw [show (pairProbA μ₀ εa c + pairProbB μ₀ εb c) / 2 =
      (pairProbA μ₀ εa c + pairProbB μ₀ εb c) * (1 / 2) by ring]
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rcases Nat.eq_zero_or_pos (n / 2) with h0 | h0
    · simp [h0]
    · have : ((n / 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
      field_simp

/-- **The Fine–Gray conditions hold in the paired product model** with `β₀` given by
`e^{β₀} p_b = p_a` (`p_b > 0`), any radius `r > 0`, any nonnegative weight functions `G`, the
information limit `i(b) = ((p_a + p_b) / 2) m(b) (1 - m(b))`, `v = i(β₀)`, and any score limit
`Z ~ N(0, σ²)` with `σ² = pairσ2`. -/
theorem fineGrayConditions_pair {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Z : Ω' → ℝ} {G : ℕ → (ℕ → S) → ℝ → ℝ} {r : ℝ}
    (hA : MeasurableSet {x | εa x = some c}) (hB : MeasurableSet {x | εb x = some c})
    (hpb : 0 < pairProbB μ₀ εb c) (hβ₀ : exp β₀ * pairProbB μ₀ εb c = pairProbA μ₀ εa c)
    (hG : ∀ n ω t, 0 ≤ G n ω t) (hr : 0 < r)
    (hZ : HasLaw Z (gaussianReal 0 (pairσ2 μ₀ εa εb c β₀)) P') :
    FineGrayConditions (pairModel μ₀) P' (fun n _ => pairTime n)
      (fun n ω => pairStatus εa εb n ω) c G (fun n _ => pairCov n) β₀ r
      (pairInfoLimit μ₀ εa εb c) (pairV μ₀ εa εb c β₀) Z where
  weight_nonneg := hG
  score := tendstoInDistribution_fgScore_pair G hA hB hβ₀ hZ
  radius_pos := hr
  info_unif η hη := by
    have hLLN := tendstoInMeasure_iff_dist.1 (tendstoInMeasure_pairEvents_div (μ₀ := μ₀) hA hB)
      η hη
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLLN
      (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
    obtain ⟨b, -, hb⟩ := hω
    simp only [Set.mem_ofPred_eq]
    rw [fgInformation_pair, pairInfoLimit, Real.dist_eq] at *
    rw [show (∑ k ∈ range (n / 2), pairEvents εa εb c (ω k)) * pairVarFn b / n -
        (pairProbA μ₀ εa c + pairProbB μ₀ εb c) / 2 * pairVarFn b =
        ((∑ k ∈ range (n / 2), pairEvents εa εb c (ω k)) / n -
          (pairProbA μ₀ εa c + pairProbB μ₀ εb c) / 2) * pairVarFn b by ring, abs_mul,
      abs_of_pos (pairVarFn_pos b)] at hb
    exact hb.trans (mul_le_of_le_one_right (abs_nonneg _) (pairVarFn_le_one b))
  info_continuousAt := (continuous_const.mul continuous_pairVarFn).continuousAt
  info_eq := rfl
  info_ne_zero := by
    have hpa : 0 < pairProbA μ₀ εa c := hβ₀ ▸ mul_pos (exp_pos β₀) hpb
    intro h
    have h' := congrArg (fun x : NNReal => (x : ℝ)) h
    simp only [pairV, NNReal.coe_zero, pairInfoLimit] at h'
    exact (mul_pos (by positivity) (pairVarFn_pos β₀)).ne' h'

/-- **Asymptotic normality of the Fine–Gray estimator in the paired product model**, with score
variance `σ² = pairσ2` (positive whenever a pair's score contribution is not a.s. zero): for any
estimator `βhat` that maximizes the weighted log partial likelihood whenever a maximizer exists,
`√n (βhat n - β₀) ⟶ Z / v` and `Z / v ~ N(0, σ² / v²)`. -/
theorem tendstoInDistribution_fgMPLE_pair {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ} {G : ℕ → (ℕ → S) → ℝ → ℝ}
    {βhat : ℕ → (ℕ → S) → ℝ}
    (hA : MeasurableSet {x | εa x = some c}) (hB : MeasurableSet {x | εb x = some c})
    (hpb : 0 < pairProbB μ₀ εb c) (hβ₀ : exp β₀ * pairProbB μ₀ εb c = pairProbA μ₀ εa c)
    (hG : ∀ n ω t, 0 ≤ G n ω t)
    (hZ : HasLaw Z (gaussianReal 0 (pairσ2 μ₀ εa εb c β₀)) P')
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (pairTime n) (pairStatus εa εb n ω) c (G n ω)
        (pairCov n)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (pairTime n) (pairStatus εa εb n ω) c (G n ω)
          (pairCov n)) Set.univ (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) (pairModel μ₀)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (pairV μ₀ εa εb c β₀ : ℝ)) (fun _ ↦ pairModel μ₀) P' ∧
    HasLaw (fun ω => Z ω / (pairV μ₀ εa εb c β₀ : ℝ))
      (gaussianReal 0 (pairσ2 μ₀ εa εb c β₀ / pairV μ₀ εa εb c β₀ ^ 2)) P' :=
  tendstoInDistribution_fgMPLE_gaussian
    (fineGrayConditions_pair hA hB hpb hβ₀ hG one_pos hZ) hZ hβhat hβhat_meas

end Conditions

end MathlibExt.Probability.Statistics.FineGrayScoreCLT
