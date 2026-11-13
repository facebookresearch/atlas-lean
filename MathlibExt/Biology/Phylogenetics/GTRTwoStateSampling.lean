/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRLogDetRecovery
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.StickyKernel
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

/-!
# An i.i.d. sampling instance for the GTR log-det consistency theorems

`GTRLogDetRecovery.ae_tendsto_rateEstimate_empirical` and
`GTRLogDetRecovery.tendstoInMeasure_rateEstimate_empirical` (T158) assume a sequence of aligned
site pairs `X n : Ω → ι × ι` that are measurable, pairwise independent, identically distributed,
and whose common law is the GTR divergence law `P (X 0 = (i, j)) = π i * P(t) i j`. This file
builds such a sequence and so shows that those hypotheses are satisfiable.

## The sampling model

* `divergenceWeight π s t (i, j) = π i * P(t) i j`, `P(t) = exp (t • gtrRate π s)`;
* `divergenceLaw π s t = ∑ a, divergenceWeight π s t a • δ_a`, a measure on `ι × ι`; it is a
  probability measure when `π ≥ 0`, `∑ π = 1`, `s ≥ 0` off the diagonal and `t ≥ 0`;
* `sampleLaw π s t = Measure.infinitePi (fun _ : ℕ => divergenceLaw π s t)`, the law of an
  i.i.d. sequence of site pairs, and `site n ω = ω n` the `n`-th site pair.

## Main results

* `ctmcTransition_pos`: for a rate matrix with positive off-diagonal rates, every entry of
  `P(t)` is positive for `t > 0`; hence `divergenceWeight_pos`: the GTR divergence law has
  **full support** for `t > 0` and `π, s > 0`.
* `measurable_site`, `pairwise_indepFun_site`, `identDistrib_site`,
  `measureReal_site_preimage_singleton`: the four sampling hypotheses of T158 hold for `site`
  under `sampleLaw π s t` (built from `Measure.infinitePi`, `infinitePi_map_eval` and
  `iIndepFun_infinitePi`).
* `ae_tendsto_rateEstimate_sampleLaw`, `tendstoInMeasure_rateEstimate_sampleLaw`: T158's
  log-det recovery consistency, instantiated on this model.
* `not_indepFun_site_self`: the constant sample `X n = site 0` is **not** an instance. With full
  support, `site 0` is not independent of itself, so the degenerate-constant-sample trick used for
  laws concentrated on one point cannot discharge pairwise independence here.
* `gtrRate_two_eq_equalInputRate`, `ctmcTransition_gtrRate_two`, `divergenceWeight_two`: on two
  states the GTR matrix is the equal-input generator with rate `s 0 1`, so the divergence law is
  explicit: `π i * (e * δ i j + (1 - e) * π j)` with `e = exp (-(s 0 1 * t))`.
* `ae_tendsto_rateEstimate_sampleLaw_two`: the two-state instance of the consistency theorem.

## Source receipt (API-00)

* Source: the i.i.d. sites model of phylogenetic inference (Felsenstein 2004, chapter 16;
  Tavaré 1986), here for one pair of aligned sequences related by a GTR branch.
* Reused: T158 `GTRLogDetRecovery.ae_tendsto_rateEstimate_empirical`,
  `tendstoInMeasure_rateEstimate_empirical`, `empiricalDivergence`, `rateEstimate`,
  `logDetDistance`; `SubstitutionModels.gtrRate`, `isRateMatrix_gtrRate`;
  `IsRateMatrix.ctmcTransition_nonneg`, `IsRateMatrix.sum_ctmcTransition`,
  `IsRateMatrix.exists_add_smul_one_nonneg`, `ctmcTransition_eq_exp_smul_uniformized`;
  `equalInputRate`, `ctmcTransition_equalInputRate`, `stickyKernel_apply`; Mathlib's
  `Measure.infinitePi`, `Measure.infinitePi_map_eval`, `iIndepFun_infinitePi`.
* Proved here: the entrywise lower bound `1 + t A ≤ exp (t A)` for nonnegative `A`, positivity
  of `P(t)`, the sampling model and its four hypotheses, the two-state closed form, the
  non-independence of the constant sample, and the instantiated consistency theorems.
* Not covered elsewhere: no file in `MathlibExt` constructs a probability space carrying the
  sampling hypotheses of T158 or T67 (`GTRInference`) for a GTR law. T67's test discharges them
  with a constant sample on a point-mass law, and T158's test applies only the deterministic
  consistency statement to a constant sequence.

## References

* S. Tavaré, *Some probabilistic and statistical problems in the analysis of DNA sequences*,
  Lectures on Mathematics in the Life Sciences 17 (1986), 57–86.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory Filter Topology MeasureTheory

namespace MathlibExt.Biology.Phylogenetics.GTRTwoStateSampling

open SubstitutionModels GTRLogDetRecovery

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Positivity of the transition function -/

/-- For a matrix `A` with nonnegative entries and `t ≥ 0`, `exp (t • A)` dominates the first two
terms of its series entrywise: `1 i j + t * A i j ≤ exp (t • A) i j`. -/
theorem one_add_le_ctmcTransition_of_nonneg {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) {t : ℝ}
    (ht : 0 ≤ t) (i j : ι) : (1 : Matrix ι ι ℝ) i j + t * A i j ≤ ctmcTransition A t i j := by
  let := Matrix.linftyOpNormedRing (n := ι) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := ι) (α := ℝ)
  have hp (n : ℕ) : ∀ i j, 0 ≤ ((t • A) ^ n) i j := by
    induction n with
    | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
    | succ n hn =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hn i k) (mul_nonneg ht (hA k j))
  have hij := Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)) i) j
  have hle := sum_le_hasSum (Finset.range 2) (fun n _ => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hp n i j)) hij
  exact le_of_eq_of_le (by simp [Finset.sum_range_succ]) hle

/-- **Positivity of the transition function**: if `Q` is a rate matrix with positive
off-diagonal rates, every entry of `P(t) = exp (t • Q)` is positive for `t > 0`. -/
theorem ctmcTransition_pos {Q : Matrix ι ι ℝ} (hQ : IsRateMatrix Q)
    (hoff : ∀ i j, i ≠ j → 0 < Q i j) {t : ℝ} (ht : 0 < t) (i j : ι) :
    0 < ctmcTransition Q t i j := by
  obtain ⟨c, -, hc⟩ := hQ.exists_add_smul_one_nonneg
  rw [ctmcTransition_eq_exp_smul_uniformized Q c t, Matrix.smul_apply, smul_eq_mul]
  refine mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le ?_ (one_add_le_ctmcTransition_of_nonneg hc ht.le i j))
  by_cases h : i = j
  · subst h
    rw [one_apply_eq]
    have := mul_nonneg ht.le (hc i i)
    linarith
  · have hQc : (Q + c • (1 : Matrix ι ι ℝ)) i j = Q i j := by simp [one_apply_ne h]
    rw [one_apply_ne h, zero_add, hQc]
    exact mul_pos ht (hoff i j h)

/-! ## The GTR divergence law -/

section Law

variable {π : ι → ℝ} {s : Matrix ι ι ℝ} {t : ℝ}

/-- The **GTR divergence weight** `π i * P(t) i j` of the site pair `(i, j)`. -/
noncomputable def divergenceWeight (π : ι → ℝ) (s : Matrix ι ι ℝ) (t : ℝ) (a : ι × ι) : ℝ :=
  π a.1 * ctmcTransition (gtrRate π s) t a.1 a.2

theorem divergenceWeight_nonneg (hπ : ∀ i, 0 ≤ π i) (hs : ∀ i j, i ≠ j → 0 ≤ s i j)
    (ht : 0 ≤ t) (a : ι × ι) : 0 ≤ divergenceWeight π s t a :=
  mul_nonneg (hπ _) ((isRateMatrix_gtrRate hπ hs).ctmcTransition_nonneg ht _ _)

/-- **Full support**: for `t > 0`, positive base frequencies and positive off-diagonal
exchangeabilities, every site pair has positive GTR divergence weight. -/
theorem divergenceWeight_pos (hπ : ∀ i, 0 < π i) (hs : ∀ i j, i ≠ j → 0 < s i j) (ht : 0 < t)
    (a : ι × ι) : 0 < divergenceWeight π s t a := by
  refine mul_pos (hπ _) (ctmcTransition_pos
    (isRateMatrix_gtrRate (fun i => (hπ i).le) fun i j h => (hs i j h).le) (fun i j h => ?_) ht
    _ _)
  simpa [gtrRate, h] using mul_pos (hs i j h) (hπ j)

theorem sum_divergenceWeight (hπ : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (t : ℝ) : ∑ a, divergenceWeight π s t a = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [divergenceWeight, ← Finset.mul_sum, (isRateMatrix_gtrRate hπ hs).sum_ctmcTransition,
    mul_one, hπ1]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The **GTR divergence law** on site pairs: the point mass `divergenceWeight π s t a` at each
`a : ι × ι`. -/
noncomputable def divergenceLaw (π : ι → ℝ) (s : Matrix ι ι ℝ) (t : ℝ) : Measure (ι × ι) :=
  ∑ a, ENNReal.ofReal (divergenceWeight π s t a) • Measure.dirac a

theorem divergenceLaw_singleton (a : ι × ι) :
    divergenceLaw π s t {a} = ENNReal.ofReal (divergenceWeight π s t a) := by
  rw [divergenceLaw, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton a),
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a, ite_eq_left (mem_univ a)]

omit [MeasurableSingletonClass ι] in
theorem isProbabilityMeasure_divergenceLaw (hπ : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    (hs : ∀ i j, i ≠ j → 0 ≤ s i j) (ht : 0 ≤ t) : IsProbabilityMeasure (divergenceLaw π s t) := by
  constructor
  rw [divergenceLaw, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => divergenceWeight_nonneg hπ hs ht a,
    sum_divergenceWeight hπ hπ1 hs, ENNReal.ofReal_one]

theorem measureReal_divergenceLaw_singleton (hπ : ∀ i, 0 ≤ π i) (hs : ∀ i j, i ≠ j → 0 ≤ s i j)
    (ht : 0 ≤ t) (a : ι × ι) : (divergenceLaw π s t).real {a} = divergenceWeight π s t a := by
  rw [measureReal_def, divergenceLaw_singleton,
    ENNReal.toReal_ofReal (divergenceWeight_nonneg hπ hs ht a)]

end Law

/-! ## The i.i.d. sampling model -/

section Sampling

variable {π : ι → ℝ} {s : Matrix ι ι ℝ} {t : ℝ} [MeasurableSpace ι]

/-- The law of an i.i.d. sequence of aligned site pairs with the GTR divergence law. -/
noncomputable def sampleLaw (π : ι → ℝ) (s : Matrix ι ι ℝ) (t : ℝ) : Measure (ℕ → ι × ι) :=
  Measure.infinitePi fun _ : ℕ => divergenceLaw π s t

/-- The `n`-th aligned site pair. -/
def site (n : ℕ) (ω : ℕ → ι × ι) : ι × ι := ω n

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_site (n : ℕ) : Measurable (site (ι := ι) n) := measurable_pi_apply n

/-- The standing hypotheses on the GTR parameters that make `divergenceLaw π s t` a probability
measure. -/
structure IsSamplingParams (π : ι → ℝ) (s : Matrix ι ι ℝ) (t : ℝ) : Prop where
  nonneg_freq : ∀ i, 0 ≤ π i
  sum_freq : ∑ i, π i = 1
  nonneg_exch : ∀ i j, i ≠ j → 0 ≤ s i j
  nonneg_time : 0 ≤ t

theorem IsSamplingParams.isProbabilityMeasure (h : IsSamplingParams π s t) :
    IsProbabilityMeasure (divergenceLaw π s t) :=
  isProbabilityMeasure_divergenceLaw h.nonneg_freq h.sum_freq h.nonneg_exch h.nonneg_time

theorem isProbabilityMeasure_sampleLaw (h : IsSamplingParams π s t) :
    IsProbabilityMeasure (sampleLaw π s t) := by
  have := h.isProbabilityMeasure
  rw [sampleLaw]
  infer_instance

/-- Every site pair has law `divergenceLaw π s t` under `sampleLaw π s t`. -/
theorem map_site (h : IsSamplingParams π s t) (n : ℕ) :
    (sampleLaw π s t).map (site n) = divergenceLaw π s t := by
  have := h.isProbabilityMeasure
  exact Measure.infinitePi_map_eval (fun _ : ℕ => divergenceLaw π s t) n

/-- The site pairs are mutually independent under `sampleLaw π s t`. -/
theorem iIndepFun_site (h : IsSamplingParams π s t) :
    iIndepFun (site (ι := ι)) (sampleLaw π s t) := by
  have := h.isProbabilityMeasure
  exact iIndepFun_infinitePi (P := fun _ : ℕ => divergenceLaw π s t)
    (X := fun _ (x : ι × ι) => x) fun _ => measurable_id

/-- **Sampling hypothesis 1 of T158**: the site pairs are pairwise independent. -/
theorem pairwise_indepFun_site (h : IsSamplingParams π s t) :
    Pairwise fun m n => IndepFun (site m) (site n) (sampleLaw π s t) :=
  fun _ _ hij => (iIndepFun_site h).indepFun hij

/-- **Sampling hypothesis 2 of T158**: the site pairs are identically distributed. -/
theorem identDistrib_site (h : IsSamplingParams π s t) (n : ℕ) :
    IdentDistrib (site n) (site 0) (sampleLaw π s t) (sampleLaw π s t) where
  aemeasurable_fst := (measurable_site n).aemeasurable
  aemeasurable_snd := (measurable_site 0).aemeasurable
  map_eq := by rw [map_site h, map_site h]

theorem sampleLaw_site_preimage (h : IsSamplingParams π s t) (n : ℕ) {S : Set (ι × ι)}
    (hS : MeasurableSet S) : sampleLaw π s t (site n ⁻¹' S) = divergenceLaw π s t S := by
  rw [← Measure.map_apply (measurable_site n) hS, map_site h]

variable [MeasurableSingletonClass ι]

/-- **Sampling hypothesis 3 of T158**: the common law is the GTR divergence law. -/
theorem measureReal_site_preimage_singleton (h : IsSamplingParams π s t) (n : ℕ)
    (a : ι × ι) : (sampleLaw π s t).real (site n ⁻¹' {a}) = divergenceWeight π s t a := by
  rw [measureReal_def, sampleLaw_site_preimage h n (measurableSet_singleton a),
    ← measureReal_def,
    measureReal_divergenceLaw_singleton h.nonneg_freq h.nonneg_exch h.nonneg_time]

/-! ## The consistency theorems, instantiated -/

/-- **Log-det recovery consistency on the i.i.d. GTR sampling model (almost surely).** For
`t > 0`, positive base frequencies summing to `1`, symmetric exchangeabilities positive off the
diagonal and at least two states, the log-det rate estimate of the empirical divergence matrix of
`site 0, …, site (n - 1)` converges `sampleLaw π s t`-almost surely to `Q / (-tr Q)`, and the
log-det distance to `-t * tr Q`. -/
theorem ae_tendsto_rateEstimate_sampleLaw [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hπ1 : ∑ i, π i = 1) (hsymm : ∀ i j, s i j = s j i) (hs : ∀ i j, i ≠ j → 0 < s i j)
    (ht : 0 < t) :
    ∀ᵐ ω ∂sampleLaw π s t,
      Tendsto (fun n => rateEstimate (empiricalDivergence site n ω)) atTop
          (𝓝 ((-(gtrRate π s).trace)⁻¹ • gtrRate π s)) ∧
        Tendsto (fun n => logDetDistance (empiricalDivergence site n ω)) atTop
          (𝓝 (-t * (gtrRate π s).trace)) := by
  have hp : IsSamplingParams π s t :=
    ⟨fun i => (hπ i).le, hπ1, fun i j h => (hs i j h).le, ht.le⟩
  have := isProbabilityMeasure_sampleLaw hp
  exact ae_tendsto_rateEstimate_empirical hπ hsymm hs ht measurable_site
    (pairwise_indepFun_site hp) (identDistrib_site hp) (measureReal_site_preimage_singleton hp 0)

/-- **Log-det recovery consistency on the i.i.d. GTR sampling model (in probability)**,
entrywise, under the hypotheses of `ae_tendsto_rateEstimate_sampleLaw`. -/
theorem tendstoInMeasure_rateEstimate_sampleLaw [Nontrivial ι] (hπ : ∀ i, 0 < π i)
    (hπ1 : ∑ i, π i = 1) (hsymm : ∀ i j, s i j = s j i) (hs : ∀ i j, i ≠ j → 0 < s i j)
    (ht : 0 < t) :
    (∀ i j, TendstoInMeasure (sampleLaw π s t)
        (fun n ω => rateEstimate (empiricalDivergence site n ω) i j) atTop
        fun _ => ((-(gtrRate π s).trace)⁻¹ • gtrRate π s) i j) ∧
      TendstoInMeasure (sampleLaw π s t)
        (fun n ω => logDetDistance (empiricalDivergence site n ω)) atTop
        fun _ => -t * (gtrRate π s).trace := by
  have hp : IsSamplingParams π s t :=
    ⟨fun i => (hπ i).le, hπ1, fun i j h => (hs i j h).le, ht.le⟩
  have := isProbabilityMeasure_sampleLaw hp
  exact tendstoInMeasure_rateEstimate_empirical hπ hsymm hs ht measurable_site
    (pairwise_indepFun_site hp) (identDistrib_site hp) (measureReal_site_preimage_singleton hp 0)

/-! ## The constant sample is not an instance -/

/-- **The degenerate-constant-sample trick fails under full support.** For `t > 0`, positive
parameters and at least two states, `site 0` is not independent of itself under
`sampleLaw π s t`, so the constant sequence `X n = site 0` (identically distributed with the GTR
divergence law) violates the pairwise-independence hypothesis of T158. -/
theorem not_indepFun_site_self [Nontrivial ι] (hπ : ∀ i, 0 < π i) (hπ1 : ∑ i, π i = 1)
    (hs : ∀ i j, i ≠ j → 0 < s i j) (ht : 0 < t) :
    ¬ IndepFun (site (ι := ι) 0) (site 0) (sampleLaw π s t) := by
  intro hind
  have hp : IsSamplingParams π s t :=
    ⟨fun i => (hπ i).le, hπ1, fun i j h => (hs i j h).le, ht.le⟩
  have := isProbabilityMeasure_sampleLaw hp
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  set a : ι × ι := (i, i)
  set b : ι × ι := (j, j)
  have hab : a ≠ b := fun h => hij (congrArg Prod.fst h)
  have hmul := hind.measure_inter_preimage_eq_mul {a} {a} (measurableSet_singleton a)
    (measurableSet_singleton a)
  rw [Set.inter_self] at hmul
  have hreal : divergenceWeight π s t a = divergenceWeight π s t a * divergenceWeight π s t a := by
    have := congrArg ENNReal.toReal hmul
    rwa [ENNReal.toReal_mul, ← measureReal_def, measureReal_site_preimage_singleton hp] at this
  have hpa := divergenceWeight_pos hπ hs ht a
  have hpb := divergenceWeight_pos hπ hs ht b
  have hone : divergenceWeight π s t a = 1 := by
    have := mul_left_cancel₀ hpa.ne' (hreal.symm.trans (mul_one _).symm)
    exact this
  have hle : divergenceWeight π s t a + divergenceWeight π s t b ≤ 1 := by
    rw [← sum_divergenceWeight hp.nonneg_freq hπ1 hp.nonneg_exch t, ← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun x _ _ => divergenceWeight_nonneg hp.nonneg_freq hp.nonneg_exch ht.le x
  linarith

end Sampling

/-! ## Two states: the explicit divergence law -/

section TwoState

variable {π : Fin 2 → ℝ} {s : Matrix (Fin 2) (Fin 2) ℝ}

/-- On two states with `π 0 + π 1 = 1` and symmetric `s`, the GTR matrix is the equal-input
generator with rate `s 0 1`. -/
theorem gtrRate_two_eq_equalInputRate (hπ1 : ∑ i, π i = 1) (hsymm : ∀ i j, s i j = s j i) :
    gtrRate π s = equalInputRate π (s 0 1) := by
  rw [Fin.sum_univ_two] at hπ1
  have h10 := hsymm 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gtrRate, equalInputRate, Finset.sum_erase_eq_sub, Fin.sum_univ_two, h10] <;>
    linear_combination (-s 0 1) * hπ1

/-- **Closed-form two-state transition function**: `P(t) i j = e * δ i j + (1 - e) * π j` with
`e = exp (-(s 0 1 * t))`. -/
theorem ctmcTransition_gtrRate_two (hπ1 : ∑ i, π i = 1) (hsymm : ∀ i j, s i j = s j i)
    (t : ℝ) (i j : Fin 2) :
    ctmcTransition (gtrRate π s) t i j =
      Real.exp (-(s 0 1 * t)) * (if i = j then 1 else 0) +
        (1 - Real.exp (-(s 0 1 * t))) * π j := by
  rw [gtrRate_two_eq_equalInputRate hπ1 hsymm, ctmcTransition_equalInputRate hπ1,
    stickyKernel_apply]

/-- **Explicit two-state divergence law.** -/
theorem divergenceWeight_two (hπ1 : ∑ i, π i = 1) (hsymm : ∀ i j, s i j = s j i) (t : ℝ)
    (a : Fin 2 × Fin 2) :
    divergenceWeight π s t a =
      π a.1 * (Real.exp (-(s 0 1 * t)) * (if a.1 = a.2 then 1 else 0) +
        (1 - Real.exp (-(s 0 1 * t))) * π a.2) := by
  rw [divergenceWeight, ctmcTransition_gtrRate_two hπ1 hsymm]

/-- **The two-state instance of log-det recovery consistency**: with base frequencies
`π 0, π 1 > 0` summing to `1`, exchangeability `s 0 1 = s 1 0 > 0` and `t > 0`, the log-det rate
estimate of i.i.d. two-state site pairs converges almost surely to `Q / (-tr Q)`. -/
theorem ae_tendsto_rateEstimate_sampleLaw_two (hπ : ∀ i, 0 < π i) (hπ1 : ∑ i, π i = 1)
    (hsymm : ∀ i j, s i j = s j i) (hs : 0 < s 0 1) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂sampleLaw π s t,
      Tendsto (fun n => rateEstimate (empiricalDivergence site n ω)) atTop
          (𝓝 ((-(gtrRate π s).trace)⁻¹ • gtrRate π s)) ∧
        Tendsto (fun n => logDetDistance (empiricalDivergence site n ω)) atTop
          (𝓝 (-t * (gtrRate π s).trace)) := by
  refine ae_tendsto_rateEstimate_sampleLaw hπ hπ1 hsymm (fun i j hij => ?_) ht
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hs
  · simpa [hsymm 1 0] using hs
  · exact absurd rfl hij

end TwoState

end MathlibExt.Biology.Phylogenetics.GTRTwoStateSampling
