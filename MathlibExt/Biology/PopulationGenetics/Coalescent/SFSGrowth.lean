/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The site frequency spectrum under exponential population growth

A sample of `n` gene copies is drawn from a population whose size `s` units of `2N₀`
generations before the present is `N₀ η(s)`, `η(s) = exp(-ρ s)` (exponential growth at rate
`ρ ≥ 0` towards the present; `θ = 4N₀u`, mutations at rate `θ / 2` per lineage per unit of real
time). Pairs of lineages coalesce at rate `1 / η(s)`, so the cumulative intensity is
`R(s) = ∫_0^s 1/η = (exp(ρ s) - 1) / ρ` (`cumRate_expGrowthSize`).

**The Griffiths–Tavaré time change.** The genealogy is Kingman's coalescent run on the clock
`R`: a standard-coalescent event at standard time `u` happens at real time
`G(u) = R⁻¹(u) = log(1 + ρ u) / ρ` (`growthTime`; `cumRate_growthTime`, `growthTime_cumRate`).
With `V_k = T_k + ⋯ + T_n` the standard time at which the epoch with `k` lineages ends, that
epoch lasts `T^ρ_k = G(V_k) - G(V_{k+1})` in real time (`growthHolding`, `growthTimes`). This
time-change representation is taken as the definition of the coalescent under exponential
growth; the topology is untouched, so its independence from the holding times is inherited
from Kingman's coalescent.

**Expected spectrum.** By the Griffiths–Tavaré formula for coalescents whose holding times are
independent of the topology (`VariableSFS.integral_sfs_of_indep`),
`E ξ_i = (θ / 2) ∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · E T^ρ_k` for `1 ≤ i ≤ n - 1`
(`integral_sfs_growth`). Because `G` is `1`-Lipschitz on `[0, ∞)` (`G' = 1 / (1 + ρ u)`), every
epoch is shortened, `E T^ρ_k ≤ 1 / C(k,2)`, strictly when `ρ > 0`; hence growth lowers every
entry of the expected spectrum below Fu's constant-size value `θ / i`, strictly when `ρ > 0`
and `θ > 0` (`integral_sfs_growth_le`, `integral_sfs_growth_lt`), and `ρ = 0` recovers `θ / i`
(`integral_sfs_growth_zero`). The most recent epoch has mean Bhaskar–Song's first-coalescence
time, `E T^ρ_n = c_n = ∫_0^∞ exp(-C(n,2) R(s)) ds` (`integral_growthTimes_top`), and the real
time to the most recent common ancestor is `G` of the standard one (`sum_growthHolding`).

**Covariance.** With the conditionally Poisson counts of `SFSCovariance.SFSCondMoments` given
the time-changed genealogy, `Cov(ξ_i, ξ_j) = δ_{ij} E ξ_i + (θ / 2)² Cov(L^ρ_i, L^ρ_j)`
(`covariance_count_growth`, with the moment hypotheses packaged by `sfsCondMoments_growth`).

Not formalized here: closed forms of `E T^ρ_k` for `k < n` (Polanski, Bobrowski & Kimmel's
exponential-integral expressions), the normalized-spectrum statement that growth produces a
relative excess of rare variants, and the derivation of the time-change representation from a
time-inhomogeneous Wright–Fisher model.

Source: R. C. Griffiths and S. Tavaré (1994), the coalescent of a population of variable size
as Kingman's coalescent time-changed by the inverse of `R(s) = ∫_0^s 1/η`; exponential growth
`η(s) = exp(-ρ s)` with `R⁻¹(u) = log(1 + ρ u) / ρ` as in Slatkin & Hudson (1991); the expected
spectrum formula of Griffiths & Tavaré (1998) and Polanski & Kimmel (2003), formalized in
`VariableSFS`.

## Main results

* `cumRate_expGrowthSize`, `cumRate_growthTime`, `growthTime_cumRate`: `R` and `G = R⁻¹`.
* `growthTime_sub_le`, `growthTime_sub_lt`, `growthTime_lt_growthTime`: `G` is strictly
  increasing and `1`-Lipschitz on `[0, ∞)`, strictly contracting for `ρ > 0`.
* `integral_growthTimes_le`, `integral_growthTimes_lt`, `integral_growthTimes_zero`:
  `E T^ρ_k ≤ 1 / C(k,2)`, strict for `ρ > 0`, equal for `ρ = 0`.
* `integral_growthTimes_top`: `E T^ρ_n = firstCoalMean (expGrowthSize ρ) n`.
* `integral_sfs_growth`: the expected spectrum under exponential growth.
* `integral_sfs_growth_le`, `integral_sfs_growth_lt`, `integral_sfs_growth_zero`: comparison
  with `θ / i`.
* `covariance_count_growth`: the covariance of two spectrum entries under growth.

## References

* R. C. Griffiths and S. Tavaré, *Sampling theory for neutral alleles in a varying
  environment*, Phil. Trans. R. Soc. Lond. B 344 (1994), 403–410.
* M. Slatkin and R. R. Hudson, *Pairwise comparisons of mitochondrial DNA sequences in stable
  and exponentially growing populations*, Genetics 129 (1991), 555–562.
* R. C. Griffiths and S. Tavaré, *The age of a mutation in a general coalescent tree*,
  Stoch. Models 14 (1998), 273–295.
* A. Polanski and M. Kimmel, *New explicit expressions for relative frequencies of
  single-nucleotide polymorphisms with application to statistical inference on population
  growth*, Genetics 165 (2003), 427–436.
* A. Bhaskar and Y. S. Song, *Descartes' rule of signs and the identifiability of population
  demographic models from genomic variation data*, Ann. Statist. 42 (2014), 2469–2493.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SFSGrowth

open SiteFrequencySpectrum VariableSFS SFSCovariance

/-! ### Exponential growth and the Griffiths–Tavaré time change -/

/-- The relative population size `η(s) = exp(-ρ s)` at time `s` before the present (in units
of `2N₀` generations, `N₀` the present size) of a population that has grown exponentially at
rate `ρ`. -/
def expGrowthSize (ρ s : ℝ) : ℝ := Real.exp (-(ρ * s))

/-- The **Griffiths–Tavaré time change** for exponential growth: the real time
`G(u) = log(1 + ρ u) / ρ` (and `G(u) = u` when `ρ = 0`) at which the cumulative coalescence
intensity `R(s) = ∫_0^s 1/η = (exp(ρ s) - 1) / ρ` reaches `u` (`cumRate_growthTime`). A
standard-coalescent event at time `u` happens at real time `G(u)`. Meaningful for
`1 + ρ u > 0`. -/
def growthTime (ρ u : ℝ) : ℝ := if ρ = 0 then u else Real.log (1 + ρ * u) / ρ

/-- Without growth (`ρ = 0`) the time change is the identity. -/
@[simp] theorem growthTime_zero_left (u : ℝ) : growthTime 0 u = u := by simp [growthTime]

/-- The present is fixed by the time change: `G(0) = 0`. -/
@[simp] theorem growthTime_zero_right (ρ : ℝ) : growthTime ρ 0 = 0 := by simp [growthTime]

/-- The cumulative coalescence intensity under exponential growth:
`R(s) = ∫_0^s exp(ρ r) dr = (exp(ρ s) - 1) / ρ` for `ρ ≠ 0`. -/
theorem cumRate_expGrowthSize {ρ : ℝ} (hρ : ρ ≠ 0) (s : ℝ) :
    cumRate (expGrowthSize ρ) s = (Real.exp (ρ * s) - 1) / ρ := by
  simp only [cumRate, expGrowthSize, ← Real.exp_neg, neg_neg]
  rw [intervalIntegral.integral_comp_mul_left (fun r => Real.exp r) hρ, integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp

/-- With a constant population size (`ρ = 0`) the intensity is `R(s) = s`. -/
theorem cumRate_expGrowthSize_zero (s : ℝ) : cumRate (expGrowthSize 0) s = s := by
  simp [cumRate, expGrowthSize]

/-- `G` inverts `R`: `R(G(u)) = u` whenever `1 + ρ u > 0`. -/
theorem cumRate_growthTime {ρ u : ℝ} (hu : 0 < 1 + ρ * u) :
    cumRate (expGrowthSize ρ) (growthTime ρ u) = u := by
  by_cases hρ : ρ = 0
  · subst hρ
    simp [cumRate_expGrowthSize_zero]
  simp only [growthTime, hρ, ↓reduceIte]
  rw [cumRate_expGrowthSize hρ, mul_div_cancel₀ _ hρ, Real.exp_log hu]
  field_simp
  ring

/-- `R` inverts `G`: `G(R(s)) = s` for every `s`. -/
theorem growthTime_cumRate (ρ s : ℝ) :
    growthTime ρ (cumRate (expGrowthSize ρ) s) = s := by
  by_cases hρ : ρ = 0
  · subst hρ
    simp [cumRate_expGrowthSize_zero]
  simp only [growthTime, hρ, ↓reduceIte]
  rw [cumRate_expGrowthSize hρ, mul_div_cancel₀ _ hρ]
  simp only [add_sub_cancel, Real.log_exp]
  field_simp

private lemma one_add_mul_pos {ρ a : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) : 0 < 1 + ρ * a := by
  positivity

/-- `G` is monotone on `[0, ∞)` for `ρ ≥ 0`: `0 ≤ G(b) - G(a)` for `0 ≤ a ≤ b`. -/
theorem growthTime_sub_nonneg {ρ a b : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ growthTime ρ b - growthTime ρ a := by
  rcases hρ.eq_or_lt with rfl | hρ'
  · simpa using hab
  simp only [growthTime, hρ'.ne', ↓reduceIte, ← sub_div]
  refine div_nonneg (sub_nonneg.2 (Real.log_le_log (one_add_mul_pos hρ ha) ?_)) hρ
  nlinarith

/-- `G` is `1`-Lipschitz on `[0, ∞)` for `ρ ≥ 0` (its derivative is `1 / (1 + ρ u) ≤ 1`):
`G(b) - G(a) ≤ b - a` for `0 ≤ a ≤ b`. Growth shortens every coalescent epoch. -/
theorem growthTime_sub_le {ρ a b : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hab : a ≤ b) :
    growthTime ρ b - growthTime ρ a ≤ b - a := by
  rcases hρ.eq_or_lt with rfl | hρ'
  · simp
  have hA := one_add_mul_pos hρ ha
  have hB := one_add_mul_pos hρ (ha.trans hab)
  simp only [growthTime, hρ'.ne', ↓reduceIte, ← sub_div]
  rw [div_le_iff₀ hρ', ← Real.log_div hB.ne' hA.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hB hA)).trans ?_
  rw [div_sub_one hA.ne', div_le_iff₀ hA]
  nlinarith [mul_nonneg hρ (sub_nonneg.2 hab), mul_nonneg (mul_nonneg hρ (sub_nonneg.2 hab))
    (mul_nonneg hρ ha)]

/-- For strict growth (`ρ > 0`) every nondegenerate epoch is strictly shortened:
`G(b) - G(a) < b - a` for `0 ≤ a < b`. -/
theorem growthTime_sub_lt {ρ a b : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a) (hab : a < b) :
    growthTime ρ b - growthTime ρ a < b - a := by
  have hA := one_add_mul_pos hρ.le ha
  have hB := one_add_mul_pos hρ.le (ha.trans hab.le)
  simp only [growthTime, hρ.ne', ↓reduceIte, ← sub_div]
  rw [div_lt_iff₀ hρ, ← Real.log_div hB.ne' hA.ne']
  have hne : (1 + ρ * b) / (1 + ρ * a) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hA.ne']
    intro h
    nlinarith
  refine (Real.log_lt_sub_one_of_pos (div_pos hB hA) hne).trans_le ?_
  rw [div_sub_one hA.ne', div_le_iff₀ hA]
  nlinarith [mul_nonneg hρ.le (sub_nonneg.2 hab.le), mul_nonneg (mul_nonneg hρ.le
    (sub_nonneg.2 hab.le)) (mul_nonneg hρ.le ha)]

/-- The time change `G` is measurable. -/
theorem measurable_growthTime (ρ : ℝ) : Measurable (growthTime ρ) := by
  unfold growthTime
  split_ifs
  · exact measurable_id
  · exact (Real.measurable_log.comp (measurable_const.add (measurable_const.mul
      measurable_id))).div_const _

/-- `G` is strictly increasing on `[0, ∞)` for `ρ ≥ 0`. -/
theorem growthTime_lt_growthTime {ρ a b : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hab : a < b) :
    growthTime ρ a < growthTime ρ b := by
  rcases hρ.eq_or_lt with rfl | hρ'
  · simpa using hab
  simp only [growthTime, hρ'.ne', ↓reduceIte]
  refine div_lt_div_of_pos_right (Real.log_lt_log (one_add_mul_pos hρ ha) ?_) hρ'
  nlinarith

/-- The cumulative intensity is nonnegative at nonnegative times (`ρ ≥ 0`). -/
theorem cumRate_expGrowthSize_nonneg {ρ s : ℝ} (hρ : 0 ≤ ρ) (hs : 0 ≤ s) :
    0 ≤ cumRate (expGrowthSize ρ) s := by
  rcases hρ.eq_or_lt with rfl | hρ'
  · rwa [cumRate_expGrowthSize_zero]
  rw [cumRate_expGrowthSize hρ'.ne']
  refine div_nonneg (sub_nonneg.2 (Real.one_le_exp (by positivity))) hρ

/-- For `0 ≤ y` and `0 ≤ t`, `t < G(y) ↔ R(t) < y`: the real time of a standard event exceeds
`t` exactly when the standard time exceeds `R(t)`. -/
theorem lt_growthTime_iff {ρ t y : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (hy : 0 ≤ y) :
    t < growthTime ρ y ↔ cumRate (expGrowthSize ρ) t < y := by
  have hR := cumRate_expGrowthSize_nonneg hρ ht
  constructor
  · intro h
    by_contra hle
    rcases (not_lt.1 hle).eq_or_lt with heq | hlt
    · rw [heq, growthTime_cumRate] at h
      exact lt_irrefl _ h
    · have := growthTime_lt_growthTime hρ hy hlt
      rw [growthTime_cumRate] at this
      exact lt_asymm h this
  · intro h
    have := growthTime_lt_growthTime hρ hR h
    rwa [growthTime_cumRate] at this

/-! ### The time-changed genealogy -/

/-- The standard-coalescent time `V_k = ∑_{j=k}^{n} T_j` at which the epoch with `k` lineages
ends, for standard holding times `T` of a sample of size `n` (`V_{n+1} = 0`, and `V_2` is the
time to the most recent common ancestor). -/
def epochEnd (n : ℕ) (T : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Icc k n, T j

/-- The **holding times under exponential growth** (Griffiths–Tavaré time change): the epoch
with `k` lineages, which lasts from `V_{k+1}` to `V_k` in standard time, lasts
`G(V_k) - G(V_{k+1})` in real time. With `T` Kingman's holding times this is the genealogy of
a sample from an exponentially growing population. -/
def growthHolding (ρ : ℝ) (n : ℕ) (T : ℕ → ℝ) (k : ℕ) : ℝ :=
  growthTime ρ (epochEnd n T k) - growthTime ρ (epochEnd n T (k + 1))

/-- `V_k = T_k + V_{k+1}` for `k ≤ n`. -/
theorem epochEnd_eq_add {n k : ℕ} (hk : k ≤ n) (T : ℕ → ℝ) :
    epochEnd n T k = T k + epochEnd n T (k + 1) := by
  rw [epochEnd, epochEnd, ← add_sum_Ioc_eq_sum_Icc hk, Finset.Icc_add_one_left_eq_Ioc]

/-- `V_k = 0` beyond the sample size (`k > n`); in particular `V_{n+1} = 0`. -/
theorem epochEnd_of_lt {n k : ℕ} (hk : n < k) (T : ℕ → ℝ) : epochEnd n T k = 0 := by
  rw [epochEnd, Icc_eq_empty (by omega), sum_empty]

/-- With nonnegative holding times every `V_k`, `k ≥ 2`, is nonnegative. -/
theorem epochEnd_nonneg {n k : ℕ} {T : ℕ → ℝ} (hT : ∀ j ∈ Icc 2 n, 0 ≤ T j) (hk : 2 ≤ k) :
    0 ≤ epochEnd n T k :=
  sum_nonneg fun j hj => hT j (mem_Icc.2 ⟨hk.trans (mem_Icc.1 hj).1, (mem_Icc.1 hj).2⟩)

/-- Without growth the time change is the identity. -/
theorem growthHolding_zero {n k : ℕ} (hk : k ≤ n) (T : ℕ → ℝ) :
    growthHolding 0 n T k = T k := by
  rw [growthHolding, growthTime_zero_left, growthTime_zero_left, epochEnd_eq_add hk]
  ring

/-- The real time to the most recent common ancestor is `G` of the standard one:
`∑_{k=2}^{n} T^ρ_k = G(∑_{k=2}^{n} T_k)`. -/
theorem sum_growthHolding (ρ : ℝ) (n : ℕ) (T : ℕ → ℝ) :
    ∑ k ∈ Icc 2 n, growthHolding ρ n T k = growthTime ρ (∑ k ∈ Icc 2 n, T k) := by
  rcases lt_or_ge n 2 with hn | hn
  · simp [Icc_eq_empty_of_lt hn]
  have h := sum_Icc_sub (M := ℝ) hn (fun k => growthTime ρ (epochEnd n T k))
  rw [epochEnd_of_lt (by omega), growthTime_zero_right, zero_sub] at h
  have e : ∀ k, growthHolding ρ n T k =
      -(growthTime ρ (epochEnd n T (k + 1)) - growthTime ρ (epochEnd n T k)) := fun k => by
    rw [growthHolding, neg_sub]
  rw [sum_congr rfl fun k _ => e k, sum_neg_distrib, h, neg_neg, epochEnd]

variable {ρ : ℝ} {n k : ℕ} {T : ℕ → ℝ}

/-- With `ρ ≥ 0` and nonnegative standard holding times, `0 ≤ T^ρ_k`. -/
theorem growthHolding_nonneg (hρ : 0 ≤ ρ) (hT : ∀ j ∈ Icc 2 n, 0 ≤ T j) (hk : k ∈ Icc 2 n) :
    0 ≤ growthHolding ρ n T k := by
  have hk' := mem_Icc.1 hk
  refine growthTime_sub_nonneg hρ (epochEnd_nonneg hT (by omega)) ?_
  rw [epochEnd_eq_add hk'.2]
  linarith [hT k hk]

/-- With `ρ ≥ 0` and nonnegative standard holding times, `T^ρ_k ≤ T_k`. -/
theorem growthHolding_le (hρ : 0 ≤ ρ) (hT : ∀ j ∈ Icc 2 n, 0 ≤ T j) (hk : k ∈ Icc 2 n) :
    growthHolding ρ n T k ≤ T k := by
  have hk' := mem_Icc.1 hk
  have h := growthTime_sub_le hρ (epochEnd_nonneg hT (show 2 ≤ k + 1 by omega))
    (show epochEnd n T (k + 1) ≤ epochEnd n T k by rw [epochEnd_eq_add hk'.2]; linarith [hT k hk])
  simpa only [growthHolding, epochEnd_eq_add hk'.2 T, add_sub_cancel_right] using h

/-- With `ρ > 0`, nonnegative standard holding times and `T_k > 0`, `T^ρ_k < T_k`. -/
theorem growthHolding_lt (hρ : 0 < ρ) (hT : ∀ j ∈ Icc 2 n, 0 ≤ T j) (hk : k ∈ Icc 2 n)
    (hTk : 0 < T k) : growthHolding ρ n T k < T k := by
  have hk' := mem_Icc.1 hk
  have h := growthTime_sub_lt hρ (epochEnd_nonneg hT (show 2 ≤ k + 1 by omega))
    (show epochEnd n T (k + 1) < epochEnd n T k by rw [epochEnd_eq_add hk'.2]; linarith)
  simpa only [growthHolding, epochEnd_eq_add hk'.2 T, add_sub_cancel_right] using h

/-- The growth holding times are a measurable function of the standard holding times. -/
theorem measurable_growthHolding (ρ : ℝ) (n : ℕ) :
    Measurable fun (T : ℕ → ℝ) (k : ℕ) => growthHolding ρ n T k := by
  refine measurable_pi_iff.2 fun k => ?_
  simp only [growthHolding, epochEnd]
  exact ((measurable_growthTime ρ).comp (Finset.measurable_sum _ fun j _ =>
    measurable_pi_apply j)).sub ((measurable_growthTime ρ).comp (Finset.measurable_sum _
      fun j _ => measurable_pi_apply j))

/-! ### Monotonicity of the variable-size spectrum in the mean holding times -/

/-- The Griffiths–Tavaré kernel is nonnegative. -/
theorem sfsKernel_nonneg (n i k : ℕ) : 0 ≤ sfsKernel n i k := by
  unfold sfsKernel
  positivity

/-- For a spectrum class `1 ≤ i < n`, the kernel entry for the last epoch (two lineages) is
`2 / (n - 1) > 0`: either lineage can carry `i` copies. -/
theorem sfsKernel_two_pos {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) : 0 < sfsKernel n i 2 := by
  have h : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  simp only [sfsKernel, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one,
    show 2 - 1 = 1 from rfl, Nat.choose_one_right]
  positivity

/-- The expected spectrum is monotone in the mean holding times (for `θ ≥ 0`). -/
theorem variableSFS_le_variableSFS {θ : ℝ} (hθ : 0 ≤ θ) {n : ℕ} {t t' : ℕ → ℝ}
    (h : ∀ k ∈ Icc 2 n, t k ≤ t' k) (i : ℕ) : variableSFS θ n t i ≤ variableSFS θ n t' i := by
  unfold variableSFS
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => ?_) (by positivity)
  exact mul_le_mul_of_nonneg_left (h k hk) (sfsKernel_nonneg n i k)

/-- Strict monotonicity: shortening every epoch, and strictly the last one, strictly lowers
every entry `1 ≤ i < n` of the expected spectrum (for `θ > 0`). -/
theorem variableSFS_lt_variableSFS {θ : ℝ} (hθ : 0 < θ) {n : ℕ} {t t' : ℕ → ℝ}
    (h : ∀ k ∈ Icc 2 n, t k ≤ t' k) (h2 : t 2 < t' 2) {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    variableSFS θ n t i < variableSFS θ n t' i := by
  have hn : 2 ≤ n := by omega
  unfold variableSFS
  refine mul_lt_mul_of_pos_left (sum_lt_sum (fun k hk => ?_) ⟨2, mem_Icc.2 ⟨le_rfl, hn⟩, ?_⟩)
    (by positivity)
  · exact mul_le_mul_of_nonneg_left (h k hk) (sfsKernel_nonneg n i k)
  · exact mul_lt_mul_of_pos_left h2 (sfsKernel_two_pos hi hin)

/-! ### Kingman's coalescent under exponential growth -/

section Kingman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- An exponentially distributed random variable is a.s. positive. -/
private lemma ae_pos_of_hasLaw_expMeasure {Y : Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (hY : HasLaw Y (expMeasure r) μ) : ∀ᵐ ω ∂μ, 0 < Y ω := by
  have := isProbabilityMeasure_expMeasure hr
  have h : ∀ᵐ x ∂expMeasure r, 0 < x := by
    rw [ae_iff]
    refine measure_mono_null (fun x (hx : ¬0 < x) => Set.mem_Iic.2 (not_lt.1 hx)) ?_
    rw [← ofReal_cdf, cdf_expMeasure_eq hr]
    simp
  rw [← hY.map_eq] at h
  exact ae_of_ae_map hY.aemeasurable h

variable {n : ℕ} (K : KingmanTimes μ n) (ρ : ℝ)

/-- The holding times of a Kingman genealogy after the Griffiths–Tavaré time change for
exponential growth at rate `ρ`: `T^ρ_k = G(V_k) - G(V_{k+1})`. -/
def growthTimes (k : ℕ) (ω : Ω) : ℝ := growthHolding ρ n (fun j => K.T j ω) k

/-- Kingman holding times are a.s. positive. -/
theorem ae_T_pos : ∀ᵐ ω ∂μ, ∀ k ∈ Icc 2 n, 0 < K.T k ω := by
  have h : ∀ᵐ ω ∂μ, ∀ k : Icc 2 n, 0 < K.T k ω :=
    ae_all_iff.2 fun k => ae_pos_of_hasLaw_expMeasure (KingmanTimes.choose_two_pos k.2)
      (K.hasLaw k k.2)
  filter_upwards [h] with ω hω k hk using hω ⟨k, hk⟩

variable {K ρ}

/-- The vector of time-changed holding times is measurable. -/
theorem measurable_growthTimes (hT : ∀ k, Measurable (K.T k)) :
    Measurable fun ω k => growthTimes K ρ k ω :=
  (measurable_growthHolding ρ n).comp (measurable_pi_iff.2 hT)

/-- Each time-changed holding time is measurable. -/
theorem measurable_growthTimes_apply (hT : ∀ k, Measurable (K.T k)) (k : ℕ) :
    Measurable (growthTimes K ρ k) :=
  (measurable_pi_apply k).comp (measurable_growthTimes hT)

/-- The time-changed genealogy is coarser than the Kingman one: its σ-algebra is contained in
that of the Kingman holding times. -/
theorem comap_growthTimes_le :
    MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi ≤
      MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi := by
  rw [show (fun ω k => growthTimes K ρ k ω) =
      (fun (T : ℕ → ℝ) (k : ℕ) => growthHolding ρ n T k) ∘ (fun ω k => K.T k ω) from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_growthHolding ρ n).comap_le

/-- A.s., `0 ≤ T^ρ_k ≤ T_k` (`< T_k` when `ρ > 0`) for every `k ∈ [2, n]`. -/
theorem ae_growthTimes_bounds (hρ : 0 ≤ ρ) : ∀ᵐ ω ∂μ, ∀ k ∈ Icc 2 n,
    0 ≤ growthTimes K ρ k ω ∧ growthTimes K ρ k ω ≤ K.T k ω ∧
      (0 < ρ → growthTimes K ρ k ω < K.T k ω) := by
  filter_upwards [ae_T_pos K] with ω hω k hk
  have h0 : ∀ j ∈ Icc 2 n, 0 ≤ K.T j ω := fun j hj => (hω j hj).le
  exact ⟨growthHolding_nonneg hρ h0 hk, growthHolding_le hρ h0 hk,
    fun hρ' => growthHolding_lt hρ' h0 hk (hω k hk)⟩

/-- Each time-changed holding time is integrable (it is dominated by the Kingman one). -/
theorem integrable_growthTimes (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k)) {k : ℕ}
    (hk : k ∈ Icc 2 n) : Integrable (growthTimes K ρ k) μ := by
  refine (K.integrable_T hk).mono' (measurable_growthTimes_apply hT k).aestronglyMeasurable ?_
  filter_upwards [ae_growthTimes_bounds (K := K) hρ] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (hω k hk).1]
  exact (hω k hk).2.1

/-- Growth shortens every epoch on average: `E T^ρ_k ≤ 1 / C(k,2)` for `ρ ≥ 0`. -/
theorem integral_growthTimes_le (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k)) {k : ℕ}
    (hk : k ∈ Icc 2 n) : μ[growthTimes K ρ k] ≤ ((k.choose 2 : ℕ) : ℝ)⁻¹ := by
  rw [← K.integral_T hk]
  refine integral_mono_ae (integrable_growthTimes hρ hT hk) (K.integrable_T hk) ?_
  filter_upwards [ae_growthTimes_bounds (K := K) hρ] with ω hω using (hω k hk).2.1

/-- Strict growth strictly shortens every epoch on average: `E T^ρ_k < 1 / C(k,2)` for
`ρ > 0`. -/
theorem integral_growthTimes_lt [IsProbabilityMeasure μ] (hρ : 0 < ρ)
    (hT : ∀ k, Measurable (K.T k)) {k : ℕ} (hk : k ∈ Icc 2 n) :
    μ[growthTimes K ρ k] < ((k.choose 2 : ℕ) : ℝ)⁻¹ := by
  rw [← K.integral_T hk, ← sub_pos, ← integral_sub (K.integrable_T hk)
    (integrable_growthTimes hρ.le hT hk)]
  have hpos : ∀ᵐ ω ∂μ, 0 < K.T k ω - growthTimes K ρ k ω := by
    filter_upwards [ae_growthTimes_bounds (K := K) hρ.le] with ω hω
    exact sub_pos.2 ((hω k hk).2.2 hρ)
  refine (integral_pos_iff_support_of_nonneg_ae (hpos.mono fun ω h => h.le)
    ((K.integrable_T hk).sub (integrable_growthTimes hρ.le hT hk))).2 ?_
  rw [pos_iff_ne_zero]
  intro h0
  obtain ⟨ω, h1, h2⟩ := (hpos.and (measure_eq_zero_iff_ae_notMem.1 h0)).exists
  exact h2 (Function.mem_support.2 h1.ne')

/-- Without growth, the time-changed genealogy is Kingman's: `E T^0_k = 1 / C(k,2)`. -/
theorem integral_growthTimes_zero {k : ℕ} (hk : k ∈ Icc 2 n) :
    μ[growthTimes K 0 k] = ((k.choose 2 : ℕ) : ℝ)⁻¹ := by
  simp only [growthTimes, growthHolding_zero (mem_Icc.1 hk).2]
  exact K.integral_T hk

end Kingman

/-! ### The expected spectrum and its covariance under exponential growth -/

section Spectrum

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {K : KingmanTimes μ n} {ρ : ℝ} {τ : Ω → List (List ℕ)} {θ : ℝ} {ξ : ℕ → Ω → ℝ}

/-- **Expected site frequency spectrum under exponential growth.** Let the genealogy of a
sample of `n` gene copies from a population that has grown exponentially at rate `ρ ≥ 0` be
Kingman's coalescent (holding times `K.T`, independent random-joining block-size history `τ`)
run through the Griffiths–Tavaré time change, so that the epoch with `k` lineages lasts
`T^ρ_k = G(V_k) - G(V_{k+1})` (`growthTimes`). If, given this genealogy, the count `ξ i` is
integrable with conditional mean `(θ / 2) L^ρ_i` (neutral infinite-sites mutation at rate
`θ / 2` per lineage per unit of real time), then for `1 ≤ i ≤ n - 1`,
`E ξ_i = (θ / 2) ∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · E T^ρ_k`.
The independence of the time-changed holding times and the topology, a hypothesis of
`VariableSFS.integral_sfs_of_indep`, is derived here from that of the Kingman ones. -/
theorem integral_sfs_growth (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] = variableSFS θ n (fun k => μ[growthTimes K ρ k]) i :=
  integral_sfs_of_indep (measurable_growthTimes_apply hT)
    (fun _ hk => integrable_growthTimes hρ hT hk) hτ hτ_law
    (indep_of_indep_of_le_right h_indep comap_growthTimes_le) hξ_int hξ hi hin

/-- **Growth lowers the expected spectrum**: under the hypotheses of `integral_sfs_growth`
with `θ ≥ 0`, `E ξ_i ≤ θ / i`, Fu's constant-size value. -/
theorem integral_sfs_growth_le (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] ≤ θ / i := by
  rw [integral_sfs_growth hρ hT hτ hτ_law h_indep hξ_int hξ hi hin,
    ← variableSFS_inv_choose_two θ hi hin]
  exact variableSFS_le_variableSFS hθ (fun k hk => integral_growthTimes_le hρ hT hk) i

/-- **Strict growth strictly lowers every entry of the expected spectrum**: under the
hypotheses of `integral_sfs_growth` with `θ > 0` and `ρ > 0`, `E ξ_i < θ / i` for every
`1 ≤ i ≤ n - 1`. -/
theorem integral_sfs_growth_lt (hθ : 0 < θ) (hρ : 0 < ρ) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] < θ / i := by
  have hn : 2 ≤ n := by omega
  rw [integral_sfs_growth hρ.le hT hτ hτ_law h_indep hξ_int hξ hi hin,
    ← variableSFS_inv_choose_two θ hi hin]
  exact variableSFS_lt_variableSFS hθ (fun k hk => integral_growthTimes_le hρ.le hT hk)
    (integral_growthTimes_lt hρ hT (mem_Icc.2 ⟨le_rfl, hn⟩)) hi hin

/-- **No growth recovers Fu's spectrum**: with `ρ = 0`, `E ξ_i = θ / i`. -/
theorem integral_sfs_growth_zero (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K 0 k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => growthTimes K 0 k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] = θ / i := by
  rw [integral_sfs_growth le_rfl hT hτ hτ_law h_indep hξ_int hξ hi hin,
    ← variableSFS_inv_choose_two θ hi hin]
  unfold variableSFS
  congr 1
  exact sum_congr rfl fun k hk => by simp only [integral_growthTimes_zero hk]

omit [IsProbabilityMeasure μ] in
/-- Each time-changed holding time is square integrable (it is dominated by the Kingman
one). -/
theorem memLp_growthTimes (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k)) {k : ℕ}
    (hk : k ∈ Icc 2 n) : MemLp (growthTimes K ρ k) 2 μ := by
  have hK : MemLp (K.T k) 2 μ := (K.hasLaw k hk).memLp_comp (f := id)
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_expMeasure (KingmanTimes.choose_two_pos hk) 2))
  refine hK.of_le (measurable_growthTimes_apply hT k).aestronglyMeasurable ?_
  filter_upwards [ae_growthTimes_bounds (K := K) hρ] with ω hω
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hω k hk).1,
    abs_of_nonneg ((hω k hk).1.trans (hω k hk).2.1)]
  exact (hω k hk).2.1

/-- Under exponential growth, each branch-length class `L^ρ_i = sfsLength n i τ T^ρ` is
square integrable. -/
theorem memLp_sfsLength_growth (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (i : ℕ) : MemLp (fun ω => sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω)) 2 μ := by
  obtain ⟨F, hF0, -⟩ := exists_finset_randomJoining (n - 1) (List.replicate n 1)
  have hae : ∀ᵐ ω ∂μ, τ ω ∈ F := by
    rw [ae_iff]
    have : {ω | ¬ τ ω ∈ F} = ⋃ ps : {ps // ps ∉ F}, τ ⁻¹' {ps.1} := by
      ext ω; simp
    rw [this]
    refine measure_iUnion_null fun ps => ?_
    rw [← measureReal_eq_zero_iff, hτ_law, hF0 _ ps.2]
  refine memLp_finsetSum _ fun k hk => ?_
  set g : List (List ℕ) → ℝ := fun ps => ((ps.getD (n - k) []).count i : ℝ)
  have hg : Measurable (fun ω => g (τ ω)) := by
    rw [measurable_iff_comap_le]
    refine le_trans ?_ hτ
    rw [show (fun ω => g (τ ω)) = g ∘ τ from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  have hbd : MemLp (fun ω => g (τ ω)) ⊤ μ := by
    refine memLp_top_of_bound hg.aestronglyMeasurable (∑ ps ∈ F, g ps) ?_
    filter_upwards [hae] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact single_le_sum (f := g) (fun _ _ => by positivity) hω
  exact hbd.fun_mul (memLp_growthTimes hρ hT hk)

/-- Build `SFSCondMoments` for the time-changed genealogy: square integrability of the
branch-length classes is automatic (`memLp_sfsLength_growth`). -/
theorem sfsCondMoments_growth (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (hξ2 : ∀ i, MemLp (ξ i) 2 μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω))
    (hξξ : ∀ i j, μ[fun ω => ξ i ω * ξ j ω | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => (θ / 2) ^ 2 * (sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω) *
        sfsLength n j (τ ω) (fun k => growthTimes K ρ k ω)) +
        if i = j then θ / 2 * sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω) else 0) :
    SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω)) :=
  ⟨hξ2, memLp_sfsLength_growth hρ hT hτ hτ_law, hξ, hξξ⟩

/-- **Covariance of SFS entries under exponential growth**: with the conditionally Poisson
counts of `SFSCondMoments` given the time-changed genealogy,
`Cov(ξ_i, ξ_j) = δ_{ij} E ξ_i + (θ / 2)² Cov(L^ρ_i, L^ρ_j)` for `1 ≤ i ≤ n - 1`, where the
diagonal term is the growth spectrum of `integral_sfs_growth`. -/
theorem covariance_count_growth (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => growthTimes K ρ k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω)))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) (j : ℕ) :
    cov[ξ i, ξ j; μ] =
      (if i = j then variableSFS θ n (fun k => μ[growthTimes K ρ k]) i else 0) +
        (θ / 2) ^ 2 * cov[fun ω => sfsLength n i (τ ω) (fun k => growthTimes K ρ k ω),
          fun ω => sfsLength n j (τ ω) (fun k => growthTimes K ρ k ω); μ] := by
  have hm := sup_le hτ (measurable_growthTimes (ρ := ρ) hT).comap_le
  rw [h.covariance_count hm i j, ← h.integral_count hm i,
    integral_sfs_growth hρ hT hτ hτ_law h_indep (fun j => (h.memLp_count j).integrable
      one_le_two) h.condExp_count hi hin]

end Spectrum

/-! ### The most recent epoch and the first-coalescence time -/

section FirstCoalescence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} {K : KingmanTimes μ n}
  {ρ : ℝ}

/-- The most recent epoch (`n` lineages) lasts `G(T_n)` in real time. -/
theorem growthTimes_top (ω : Ω) : growthTimes K ρ n ω = growthTime ρ (K.T n ω) := by
  simp [growthTimes, growthHolding, epochEnd]

/-- **The first coalescence under exponential growth** (Griffiths & Tavaré): the expected real
duration of the most recent epoch (`n` lineages) is Bhaskar–Song's first-coalescence time
`c_n = ∫_0^∞ exp(-C(n,2) R(s)) ds` for `η(s) = exp(-ρ s)`. Proof by the tail formula
`E X = ∫_0^∞ P(X > t) dt` and `P(G(T_n) > t) = P(T_n > R(t)) = exp(-C(n,2) R(t))`. -/
theorem integral_growthTimes_top (hρ : 0 ≤ ρ) (hT : ∀ k, Measurable (K.T k)) (hn : 2 ≤ n) :
    μ[growthTimes K ρ n] = firstCoalMean (expGrowthSize ρ) n := by
  have hk : n ∈ Icc 2 n := mem_Icc.2 ⟨hn, le_rfl⟩
  have hc := KingmanTimes.choose_two_pos hk
  have := isProbabilityMeasure_expMeasure hc
  have hnn : 0 ≤ᵐ[μ] growthTimes K ρ n := by
    filter_upwards [ae_growthTimes_bounds (K := K) hρ] with ω hω using (hω n hk).1
  rw [Integrable.integral_eq_integral_meas_lt (integrable_growthTimes hρ hT hk) hnn,
    firstCoalMean]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  have hset : {ω | t < growthTimes K ρ n ω} =ᵐ[μ]
      {ω | cumRate (expGrowthSize ρ) t < K.T n ω} := by
    filter_upwards [ae_T_pos K] with ω hω
    simp only [growthTimes_top, eq_iff_iff]
    exact lt_growthTime_iff hρ ht0 (hω n hk).le
  rw [measureReal_congr hset,
    (K.hasLaw n hk).measureReal_eq (p := fun y => cumRate (expGrowthSize ρ) t < y)
      measurableSet_Ioi, show {y : ℝ | cumRate (expGrowthSize ρ) t < y} =
      (Set.Iic (cumRate (expGrowthSize ρ) t))ᶜ by ext; simp,
    probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, cdf_expMeasure_eq hc]
  simp only [cumRate_expGrowthSize_nonneg hρ ht0, ↓reduceIte, neg_mul]
  ring

end FirstCoalescence

end MathlibExt.Biology.PopulationGenetics.Coalescent.SFSGrowth
