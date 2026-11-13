/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import MathlibExt.Probability.SupermartingaleOptionalStopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# E-values and e-processes: error control under optional stopping, FWER and FDR

An **e-value** for a null hypothesis is a nonnegative statistic `E` with `E_P[E] ≤ 1` under the
null `P`. Large values are evidence against the null; by Markov's inequality the test "reject
when `E ≥ 1 / α`" has type-I error at most `α`. An **e-process** is a nonnegative adapted
process `(E n)` whose value at every bounded stopping time is an e-value; nonnegative
supermartingales started at mean at most one (**test supermartingales**) are the main example.

This file formalizes the e-value branch of error control for repeated looks and multiple
endpoints:

* `IsEValue`, `IsEValue.measure_ge_le` (Markov: `μ {c ≤ E} ≤ 1 / c`) and the calibration
  `IsEValue.isValidPValue`: `(max E 1)⁻¹` is a valid p-value.
* `IsEProcess`; `IsTestSupermartingale.isEProcess`: a test supermartingale is an e-process
  (bounded optional stopping); `IsEProcess.isEValue_stoppedValue`: validity under optional
  stopping.
* **Ville's inequality for e-processes**: `IsEProcess.measure_exists_le_ge_le` (finite
  horizon) and `IsEProcess.measure_exists_ge_le` (`μ {∃ n, c ≤ E n} ≤ 1 / c`, time-uniform).
  Consequently the e-process evaluated at an *arbitrary* random time, not necessarily a
  stopping time, rejects with probability at most `α` (`IsEProcess.measure_ge_at_le`) and
  yields a valid p-value (`IsEProcess.isValidPValue_at`).
* **FWER** (e-Bonferroni): rejecting endpoint `i` at look `n` when `E i n ≥ m / α` controls the
  probability of *ever* rejecting a true null, over all looks and all endpoints, at
  `α |H0| / m ≤ α` (`measure_exists_mem_exists_eBonferroniRejections_le`), under arbitrary
  dependence across endpoints.
* **FDR** (e-BH, Wang–Ramdas): every *self-consistent* rejection set (each rejected `i`
  satisfies `E i ≥ m / (α |R|)`) has FDR at most `α |H0| / m` under arbitrary dependence
  (`lintegral_falseDiscoveryProportion_le_of_isEBHSelfConsistent`); the e-BH procedure is
  self-consistent (`eBHRejections_isEBHSelfConsistent`), and applying it to e-processes stopped
  at a common bounded stopping time keeps the guarantee
  (`lintegral_falseDiscoveryProportion_eBHRejections_stoppedValue_le`).

## Comparison with alpha spending

`AlphaSpending.lean` controls the type-I error of `K` *pre-planned* looks by splitting a
budget `α` across them and applying a union bound to per-look p-values. The e-process
guarantee here needs no look schedule: the event bounded is "some look `n ∈ ℕ` rejects", so
the number and timing of looks may depend on the data, and the trial may be continued past any
planned horizon. The price is that a single e-value threshold `1 / α` is typically more
conservative than a p-value threshold at a fixed sample size.

## Implementation notes

E-values are real-valued and nonnegative; their expectation is taken as a lower Lebesgue
integral `∫⁻ ofReal E`, so the condition `E[E] ≤ 1` needs no separate integrability hypothesis.
`IsEValue.of_integral_le_one` converts from the Bochner form. Ville's inequality for
nonnegative supermartingales in the measure-real form is `Supermartingale.ville_maximal_ineq`
in `Sequential/Ville.lean`; the version here is stated for e-processes, which need not be
supermartingales, and is proved by the same hitting-time argument directly from the
stopping-time definition.

## References

* J. Ville, *Étude critique de la notion de collectif*, Gauthier-Villars (1939).
* V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist. 49
  (2021), 1736–1754 (e-to-p calibration, e-Bonferroni).
* R. Wang and A. Ramdas, *False discovery rate control with e-values*, J. R. Stat. Soc. Ser. B
  84 (2022), 822–852 (e-BH, self-consistency).
* A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Testing exchangeability: fork-convexity,
  supermartingales and e-processes*, Int. J. Approx. Reason. 141 (2022), 83–109 (e-processes).
* P. Grünwald, R. de Heide and W. M. Koolen, *Safe testing*, J. R. Stat. Soc. Ser. B 86 (2024),
  1091–1128.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory Filter

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {m : ℕ}

/-! ### E-values -/

/-- `E` is an **e-value** under `μ`: a nonnegative measurable statistic with
`E_μ[E] ≤ 1` (expectation as a lower Lebesgue integral).

Source: Vovk and Wang (2021); Grünwald, de Heide and Koolen (2024). -/
structure IsEValue (μ : Measure Ω) (E : Ω → ℝ) : Prop where
  /-- An e-value is nonnegative. -/
  nonneg : ∀ ω, 0 ≤ E ω
  /-- An e-value is measurable. -/
  measurable : Measurable E
  /-- An e-value has expectation at most one under the null. -/
  lintegral_le_one : ∫⁻ ω, ENNReal.ofReal (E ω) ∂μ ≤ 1

namespace IsEValue

variable {E : Ω → ℝ}

/-- A nonnegative measurable integrable statistic with Bochner expectation at most one is an
e-value. -/
theorem of_integral_le_one (hnonneg : ∀ ω, 0 ≤ E ω) (hmeas : Measurable E)
    (hint : Integrable E μ) (hle : ∫ ω, E ω ∂μ ≤ 1) : IsEValue μ E where
  nonneg := hnonneg
  measurable := hmeas
  lintegral_le_one := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnonneg)]
    exact ENNReal.ofReal_le_one.2 hle

/-- **Markov's inequality for e-values.** For `c > 0`, `μ {c ≤ E} ≤ 1 / c`. With `c = 1 / α`
the test "reject when `E ≥ 1 / α`" has type-I error at most `α`. -/
theorem measure_ge_le (hE : IsEValue μ E) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ E ω} ≤ ENNReal.ofReal c⁻¹ := by
  calc μ {ω | c ≤ E ω} ≤ μ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (E ω)} :=
        measure_mono fun ω hω => ENNReal.ofReal_le_ofReal hω
    _ ≤ (∫⁻ ω, ENNReal.ofReal (E ω) ∂μ) / ENNReal.ofReal c :=
        meas_ge_le_lintegral_div hE.measurable.ennreal_ofReal.aemeasurable
          (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top
    _ ≤ 1 / ENNReal.ofReal c := by gcongr; exact hE.lintegral_le_one
    _ = ENNReal.ofReal c⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos hc]

end IsEValue

/-- **E-to-p calibration, tail form.** If `μ` is a probability measure and
`μ {c ≤ X} ≤ 1 / c` for every `c > 1`, then `(max X 1)⁻¹` is a valid p-value. -/
theorem isValidPValue_inv_max_one [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : ∀ c : ℝ, 1 < c → μ {ω | c ≤ X ω} ≤ ENNReal.ofReal c⁻¹) :
    IsValidPValue μ (fun ω => (max (X ω) 1)⁻¹) := by
  rintro t ⟨ht0, ht1⟩
  have hpos (ω : Ω) : 0 < max (X ω) 1 := one_pos.trans_le (le_max_right _ _)
  rcases ht1.lt_or_eq with ht1 | rfl
  · rcases ht0.lt_or_eq with ht0 | rfl
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht0).2 ht1
      have hsub : {ω | (max (X ω) 1)⁻¹ ≤ t} ⊆ {ω | t⁻¹ ≤ X ω} := by
        intro ω hω
        have h1 : t⁻¹ ≤ max (X ω) 1 := (inv_le_comm₀ (hpos ω) ht0).1 hω
        rcases le_max_iff.1 h1 with h | h
        · exact h
        · exact absurd h (not_le.2 hinv)
      calc μ {ω | (max (X ω) 1)⁻¹ ≤ t} ≤ μ {ω | t⁻¹ ≤ X ω} := measure_mono hsub
        _ ≤ ENNReal.ofReal t⁻¹⁻¹ := hX _ hinv
        _ = ENNReal.ofReal t := by rw [inv_inv]
    · have hempty : {ω | (max (X ω) 1)⁻¹ ≤ 0} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact inv_pos.2 (hpos ω)
      rw [hempty, measure_empty]
      exact bot_le
  · rw [ENNReal.ofReal_one]
    exact prob_le_one

/-- **E-to-p calibration.** For an e-value `E` under a probability measure, `(max E 1)⁻¹` is a
valid p-value.

Source: Vovk and Wang (2021) (the calibrator `e ↦ min (1, 1 / e)`). -/
theorem IsEValue.isValidPValue [IsProbabilityMeasure μ] {E : Ω → ℝ} (hE : IsEValue μ E) :
    IsValidPValue μ (fun ω => (max (E ω) 1)⁻¹) :=
  isValidPValue_inv_max_one fun _ hc => hE.measure_ge_le (one_pos.trans hc)

/-! ### Union bound and e-Bonferroni -/

/-- Union bound with a common per-event bound. -/
theorem measure_biUnion_le_card_mul {ι : Type*} (s : Finset ι) (A : ι → Set Ω) {c : ℝ}
    (h : ∀ i ∈ s, μ (A i) ≤ ENNReal.ofReal c) :
    μ (⋃ i ∈ s, A i) ≤ ENNReal.ofReal (s.card * c) := by
  calc μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i) := measure_biUnion_finset_le s A
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal c := Finset.sum_le_sum h
    _ = ENNReal.ofReal (s.card * c) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]

/-- The level `α |H0| / m` is at most `α`. -/
theorem mul_card_div_le_alpha {α : ℝ} (hα : 0 ≤ α) (H0 : Finset (Fin m)) :
    α * H0.card / m ≤ α := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hα
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm']
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_finset_fin_le H0) hα

/-- The **e-Bonferroni** rejections at level `α` among `m` e-values: those with
`E i ≥ m / α`, written division-free as `m ≤ α E i`. -/
noncomputable def eBonferroniRejections (α : ℝ) (e : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => (m : ℝ) ≤ α * e i

/-- **E-Bonferroni controls the FWER.** If every true-null statistic is an e-value, the
probability that e-Bonferroni rejects some true null is at most `α |H0| / m`. No dependence
assumption is made.

Source: Vovk and Wang (2021). -/
theorem measure_exists_mem_eBonferroniRejections_le {α : ℝ} (hα : 0 < α)
    (E : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) (hnull : ∀ i ∈ H0, IsEValue μ (E i)) :
    μ {ω | ∃ i ∈ H0, i ∈ eBonferroniRejections α (fun j => E j ω)} ≤
      ENNReal.ofReal (α * H0.card / m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Finset.eq_empty_of_isEmpty H0]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hset : {ω | ∃ i ∈ H0, i ∈ eBonferroniRejections α (fun j => E j ω)} =
      ⋃ i ∈ H0, {ω | (m : ℝ) / α ≤ E i ω} := by
    ext ω
    simp [eBonferroniRejections, div_le_iff₀' hα]
  rw [hset]
  refine (measure_biUnion_le_card_mul H0 _ (c := α / m)
    fun i hi => ?_).trans_eq ?_
  · simpa [inv_div] using (hnull i hi).measure_ge_le (div_pos hm' hα)
  · congr 1
    ring

/-! ### E-processes and test supermartingales -/

/-- `E` is an **e-process** for the filtration `𝒢` under `μ`: a nonnegative adapted process
whose value at every bounded stopping time is an e-value.

Source: Ramdas, Ruf, Larsson and Koolen (2022). -/
structure IsEProcess (μ : Measure Ω) (𝒢 : Filtration ℕ m0) (E : ℕ → Ω → ℝ) : Prop where
  /-- An e-process is nonnegative. -/
  nonneg : ∀ n ω, 0 ≤ E n ω
  /-- An e-process is adapted. -/
  stronglyAdapted : StronglyAdapted 𝒢 E
  /-- At every bounded stopping time the stopped value has expectation at most one. -/
  lintegral_stoppedValue_le_one : ∀ τ : Ω → WithTop ℕ, IsStoppingTime 𝒢 τ →
    ∀ N : ℕ, (∀ ω, τ ω ≤ N) → ∫⁻ ω, ENNReal.ofReal (stoppedValue E τ ω) ∂μ ≤ 1

/-- `M` is a **test supermartingale** for `𝒢` under `μ`: a nonnegative supermartingale with
`E[M 0] ≤ 1`. -/
structure IsTestSupermartingale (μ : Measure Ω) (𝒢 : Filtration ℕ m0) (M : ℕ → Ω → ℝ) :
    Prop where
  /-- A test supermartingale is a supermartingale. -/
  supermartingale : Supermartingale M 𝒢 μ
  /-- A test supermartingale is nonnegative. -/
  nonneg : ∀ n ω, 0 ≤ M n ω
  /-- A test supermartingale starts with expectation at most one. -/
  integral_zero_le_one : ∫ ω, M 0 ω ∂μ ≤ 1

/-- **A test supermartingale is an e-process**: by bounded optional stopping,
`E[M_τ] ≤ E[M_0] ≤ 1` for every bounded stopping time `τ`. -/
theorem IsTestSupermartingale.isEProcess [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0}
    {M : ℕ → Ω → ℝ} (hM : IsTestSupermartingale μ 𝒢 M) : IsEProcess μ 𝒢 M where
  nonneg := hM.nonneg
  stronglyAdapted := hM.supermartingale.stronglyAdapted
  lintegral_stoppedValue_le_one τ hτ N hbdd := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_stoppedValue ℕ hτ hM.supermartingale.integrable hbdd)
      (ae_of_all _ fun ω => hM.nonneg _ ω)]
    exact ENNReal.ofReal_le_one.2
      ((hM.supermartingale.expected_stoppedValue_le hτ hbdd).trans hM.integral_zero_le_one)

/-- An e-value measurable at time `0`, held constant in time, is an e-process. -/
theorem IsEValue.isEProcess_const {𝒢 : Filtration ℕ m0} {E : Ω → ℝ} (hE : IsEValue μ E)
    (hmeas : Measurable[𝒢 0] E) : IsEProcess μ 𝒢 (fun _ => E) where
  nonneg _ := hE.nonneg
  stronglyAdapted n := (hmeas.mono (𝒢.mono (Nat.zero_le n)) le_rfl).stronglyMeasurable
  lintegral_stoppedValue_le_one _ _ _ _ := hE.lintegral_le_one

namespace IsEProcess

variable {𝒢 : Filtration ℕ m0} {E : ℕ → Ω → ℝ}

/-- Each time slice of an e-process is measurable. -/
theorem measurable (hE : IsEProcess μ 𝒢 E) (n : ℕ) : Measurable (E n) :=
  ((hE.stronglyAdapted n).mono (𝒢.le n)).measurable

/-- The value of an e-process at a stopping time is measurable. -/
theorem measurable_stoppedValue (hE : IsEProcess μ 𝒢 E) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) : Measurable (stoppedValue E τ) :=
  (MeasureTheory.measurable_stoppedValue
    hE.stronglyAdapted.isStronglyProgressive_of_discrete hτ).mono hτ.measurableSpace_le le_rfl

/-- **Validity under optional stopping.** The value of an e-process at a bounded stopping time
is an e-value. -/
theorem isEValue_stoppedValue (hE : IsEProcess μ 𝒢 E) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    IsEValue μ (stoppedValue E τ) where
  nonneg ω := hE.nonneg _ ω
  measurable := hE.measurable_stoppedValue hτ
  lintegral_le_one := hE.lintegral_stoppedValue_le_one τ hτ N hbdd

/-- Each time slice of an e-process is an e-value. -/
theorem isEValue (hE : IsEProcess μ 𝒢 E) (n : ℕ) : IsEValue μ (E n) :=
  hE.isEValue_stoppedValue (isStoppingTime_const 𝒢 n) (N := n) fun _ => le_rfl

/-- **Ville's inequality for e-processes, finite horizon.** For `c > 0` and every horizon `N`,
`μ {∃ n ≤ N, c ≤ E n} ≤ 1 / c`. The proof stops the process at the first time it reaches
`c` (capped at `N`) and applies Markov's inequality to the stopped e-value. -/
theorem measure_exists_le_ge_le (hE : IsEProcess μ 𝒢 E) (N : ℕ) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n ≤ N, c ≤ E n ω} ≤ ENNReal.ofReal c⁻¹ := by
  set τ : Ω → WithTop ℕ := fun ω => (hittingBtwn E (Set.Ici c) 0 N ω : ℕ)
  have hτ : IsStoppingTime 𝒢 τ :=
    hE.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd (ω : Ω) : τ ω ≤ N := WithTop.coe_le_coe.2 (hittingBtwn_le ω)
  calc μ {ω | ∃ n ≤ N, c ≤ E n ω} ≤ μ {ω | c ≤ stoppedValue E τ ω} := by
        refine measure_mono ?_
        rintro ω ⟨n, hn, h⟩
        exact stoppedValue_hittingBtwn_mem ⟨n, ⟨Nat.zero_le n, hn⟩, h⟩
    _ ≤ ENNReal.ofReal c⁻¹ := (hE.isEValue_stoppedValue hτ hbdd).measure_ge_le hc

/-- **Ville's inequality for e-processes, time-uniform.** For `c > 0`, the probability that the
e-process *ever* reaches `c` is at most `1 / c`.

Source: Ville (1939); Ramdas, Ruf, Larsson and Koolen (2022). -/
theorem measure_exists_ge_le (hE : IsEProcess μ 𝒢 E) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c ≤ E n ω} ≤ ENNReal.ofReal c⁻¹ := by
  have hmono : Monotone fun N : ℕ => {ω | ∃ n ≤ N, c ≤ E n ω} := by
    rintro N N' hNN' ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hNN', h⟩
  have hunion : ⋃ N : ℕ, {ω | ∃ n ≤ N, c ≤ E n ω} = {ω | ∃ n, c ≤ E n ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, n, _, h⟩
      exact ⟨n, h⟩
    · rintro ⟨n, h⟩
      exact ⟨n, n, le_rfl, h⟩
  rw [← hunion]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
    fun N => hE.measure_exists_le_ge_le N hc

/-- **Anytime validity.** The e-process evaluated at an *arbitrary* random time `T` (not
necessarily a stopping time) reaches `c > 0` with probability at most `1 / c`. -/
theorem measure_ge_at_le (hE : IsEProcess μ 𝒢 E) (T : Ω → ℕ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ E (T ω) ω} ≤ ENNReal.ofReal c⁻¹ :=
  (measure_mono (s := {ω | c ≤ E (T ω) ω}) (t := {ω | ∃ n, c ≤ E n ω})
    fun ω hω => ⟨T ω, hω⟩).trans (hE.measure_exists_ge_le hc)

/-- **Anytime-valid p-value.** At any random time `T`, `(max (E T) 1)⁻¹` is a valid p-value. -/
theorem isValidPValue_at [IsProbabilityMeasure μ] (hE : IsEProcess μ 𝒢 E) (T : Ω → ℕ) :
    IsValidPValue μ (fun ω => (max (E (T ω) ω) 1)⁻¹) :=
  isValidPValue_inv_max_one fun _ hc => hE.measure_ge_at_le T (one_pos.trans hc)

end IsEProcess

/-- **FWER over all looks and all endpoints (e-Bonferroni for e-processes).** Endpoint `i` is
rejected at look `n` when `E i n ≥ m / α`. If every true-null endpoint carries an e-process,
the probability that some true null is *ever* rejected, at any look `n ∈ ℕ`, is at most
`α |H0| / m`. The looks need not be pre-planned, and the endpoints may be arbitrarily
dependent. -/
theorem measure_exists_mem_exists_eBonferroniRejections_le {α : ℝ} (hα : 0 < α)
    {𝒢 : Filtration ℕ m0} (E : Fin m → ℕ → Ω → ℝ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsEProcess μ 𝒢 (E i)) :
    μ {ω | ∃ i ∈ H0, ∃ n, i ∈ eBonferroniRejections α (fun j => E j n ω)} ≤
      ENNReal.ofReal (α * H0.card / m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Finset.eq_empty_of_isEmpty H0]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hset : {ω | ∃ i ∈ H0, ∃ n, i ∈ eBonferroniRejections α (fun j => E j n ω)} =
      ⋃ i ∈ H0, {ω | ∃ n, (m : ℝ) / α ≤ E i n ω} := by
    ext ω
    simp [eBonferroniRejections, div_le_iff₀' hα]
  rw [hset]
  refine (measure_biUnion_le_card_mul H0 _ (c := α / m)
    fun i hi => ?_).trans_eq ?_
  · simpa [inv_div] using (hnull i hi).measure_exists_ge_le (div_pos hm' hα)
  · congr 1
    ring

/-- **FWER at most `α` over all looks and endpoints.** -/
theorem measure_exists_mem_exists_eBonferroniRejections_le_alpha {α : ℝ} (hα : 0 < α)
    {𝒢 : Filtration ℕ m0} (E : Fin m → ℕ → Ω → ℝ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsEProcess μ 𝒢 (E i)) :
    μ {ω | ∃ i ∈ H0, ∃ n, i ∈ eBonferroniRejections α (fun j => E j n ω)} ≤
      ENNReal.ofReal α :=
  (measure_exists_mem_exists_eBonferroniRejections_le hα E H0 hnull).trans
    (ENNReal.ofReal_le_ofReal (mul_card_div_le_alpha hα.le H0))

/-! ### FDR: self-consistent rejection sets and e-BH -/

/-- A rejection set `R` is **self-consistent** for e-values `e` at level `α` if every rejected
hypothesis has `e i ≥ m / (α |R|)`, written division-free as `m ≤ α |R| e i`.

Source: Wang and Ramdas (2022). -/
def IsEBHSelfConsistent (α : ℝ) (e : Fin m → ℝ) (R : Finset (Fin m)) : Prop :=
  ∀ i ∈ R, (m : ℝ) ≤ α * R.card * e i

/-- The number of e-values clearing the e-BH threshold for `k` rejections, `e i ≥ m / (α k)`
(division-free: `m ≤ α k e i`). -/
noncomputable def eBHCount (α : ℝ) (e : Fin m → ℝ) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (m : ℝ) ≤ α * k * e i).card

/-- The **e-BH index**: the largest `k ∈ {0, …, m}` such that at least `k` e-values satisfy
`e i ≥ m / (α k)` (`k = 0` always qualifies). -/
noncomputable def eBHIndex (α : ℝ) (e : Fin m → ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ => k ≤ eBHCount α e k).max' ⟨0, by simp⟩

/-- The **e-BH rejections**: the e-values with `e i ≥ m / (α k̂)`, `k̂ = eBHIndex α e`.

Source: Wang and Ramdas (2022). -/
noncomputable def eBHRejections (α : ℝ) (e : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => (m : ℝ) ≤ α * eBHIndex α e * e i

/-- The e-BH index lies in the set of qualifying indices it maximizes over. -/
theorem eBHIndex_mem (α : ℝ) (e : Fin m → ℝ) :
    eBHIndex α e ∈ (Finset.range (m + 1)).filter fun k : ℕ => k ≤ eBHCount α e k :=
  Finset.max'_mem _ _

/-- The e-BH index is at most `m`. -/
theorem eBHIndex_le (α : ℝ) (e : Fin m → ℝ) : eBHIndex α e ≤ m := by
  have h := eBHIndex_mem α e
  simp only [Finset.mem_filter, Finset.mem_range] at h
  omega

/-- The e-BH procedure rejects at least `eBHIndex α e` hypotheses. -/
theorem eBHIndex_le_card_eBHRejections (α : ℝ) (e : Fin m → ℝ) :
    eBHIndex α e ≤ (eBHRejections α e).card := by
  have h := eBHIndex_mem α e
  simp only [Finset.mem_filter] at h
  exact h.2

/-- The e-BH index is the largest qualifying `k ≤ m`. -/
theorem le_eBHIndex {α : ℝ} {e : Fin m → ℝ} {k : ℕ} (hk : k ≤ m) (h : k ≤ eBHCount α e k) :
    k ≤ eBHIndex α e :=
  Finset.le_max' _ k (by simpa [Nat.lt_succ_iff] using ⟨hk, h⟩)

/-- **The e-BH rejection set is self-consistent.** -/
theorem eBHRejections_isEBHSelfConsistent (α : ℝ) (e : Fin m → ℝ) :
    IsEBHSelfConsistent α e (eBHRejections α e) := by
  intro i hi
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast i.pos
  simp only [eBHRejections, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hk : (eBHIndex α e : ℝ) ≤ (eBHRejections α e).card := by
    exact_mod_cast eBHIndex_le_card_eBHRejections α e
  have hk0 : (0 : ℝ) ≤ eBHIndex α e := Nat.cast_nonneg _
  have hae : 0 ≤ α * e i := by
    by_contra h
    push Not at h
    have : α * eBHIndex α e * e i ≤ 0 := by nlinarith
    linarith
  calc (m : ℝ) ≤ α * eBHIndex α e * e i := hi
    _ = eBHIndex α e * (α * e i) := by ring
    _ ≤ (eBHRejections α e).card * (α * e i) := mul_le_mul_of_nonneg_right hk hae
    _ = α * (eBHRejections α e).card * e i := by ring

/-- **Pointwise FDP bound for self-consistent sets.** If `R` is self-consistent and the
true-null e-values are nonnegative, `FDP ≤ (α / m) ∑_{i ∈ H0} e i`. -/
theorem falseDiscoveryProportion_le_of_isEBHSelfConsistent {α : ℝ} (hα : 0 ≤ α)
    {e : Fin m → ℝ} {R : Finset (Fin m)} (hR : IsEBHSelfConsistent α e R)
    (H0 : Finset (Fin m)) (he : ∀ i ∈ H0, 0 ≤ e i) :
    falseDiscoveryProportion H0 R ≤ α / m * ∑ i ∈ H0, e i := by
  rw [fdp_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  split_ifs with hiR
  · have hm' : (0 : ℝ) < m := by exact_mod_cast i.pos
    have hcard : (1 : ℝ) ≤ R.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hiR⟩
    rw [max_eq_left hcard, div_le_iff₀ (by linarith)]
    calc (1 : ℝ) = m / m := (div_self hm'.ne').symm
      _ ≤ (α * R.card * e i) / m := by gcongr; exact hR i hiR
      _ = α / m * e i * R.card := by ring
  · exact mul_nonneg (div_nonneg hα (Nat.cast_nonneg _)) (he i hi)

/-- **FDR control for self-consistent rejection sets under arbitrary dependence.** If every
true-null statistic is an e-value and `R ω` is self-consistent for every outcome, then
`E[FDP] ≤ α |H0| / m`. No assumption is made on the joint law of the e-values.

Source: Wang and Ramdas (2022). -/
theorem lintegral_falseDiscoveryProportion_le_of_isEBHSelfConsistent {α : ℝ} (hα : 0 ≤ α)
    (E : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) (hnull : ∀ i ∈ H0, IsEValue μ (E i))
    (R : Ω → Finset (Fin m)) (hR : ∀ ω, IsEBHSelfConsistent α (fun j => E j ω) (R ω)) :
    ∫⁻ ω, ENNReal.ofReal (falseDiscoveryProportion H0 (R ω)) ∂μ ≤
      ENNReal.ofReal (α * H0.card / m) := by
  have hαm : (0 : ℝ) ≤ α / m := div_nonneg hα (Nat.cast_nonneg _)
  calc ∫⁻ ω, ENNReal.ofReal (falseDiscoveryProportion H0 (R ω)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (α / m) * ∑ i ∈ H0, ENNReal.ofReal (E i ω) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun i hi => (hnull i hi).nonneg ω,
          ← ENNReal.ofReal_mul hαm]
        exact ENNReal.ofReal_le_ofReal (falseDiscoveryProportion_le_of_isEBHSelfConsistent hα
          (hR ω) H0 fun i hi => (hnull i hi).nonneg ω)
    _ = ENNReal.ofReal (α / m) * ∑ i ∈ H0, ∫⁻ ω, ENNReal.ofReal (E i ω) ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' H0 fun i hi => (hnull i hi).measurable.ennreal_ofReal.aemeasurable]
    _ ≤ ENNReal.ofReal (α / m) * ∑ _i ∈ H0, 1 := by
        gcongr with i hi
        exact (hnull i hi).lintegral_le_one
    _ = ENNReal.ofReal (α * H0.card / m) := by
        rw [Finset.sum_const, nsmul_one, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hαm]
        congr 1
        ring

/-- **e-BH controls the FDR under arbitrary dependence**: `E[FDP] ≤ α |H0| / m`.

Source: Wang and Ramdas (2022). -/
theorem lintegral_falseDiscoveryProportion_eBHRejections_le {α : ℝ} (hα : 0 ≤ α)
    (E : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) (hnull : ∀ i ∈ H0, IsEValue μ (E i)) :
    ∫⁻ ω, ENNReal.ofReal (falseDiscoveryProportion H0 (eBHRejections α fun j => E j ω)) ∂μ ≤
      ENNReal.ofReal (α * H0.card / m) :=
  lintegral_falseDiscoveryProportion_le_of_isEBHSelfConsistent hα E H0 hnull _
    fun _ => eBHRejections_isEBHSelfConsistent α _

/-- A nonnegative function whose lower integral is at most `ofReal b` has Bochner integral at
most `b` (non-integrable functions have Bochner integral `0`). -/
theorem integral_le_of_lintegral_ofReal_le {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {b : ℝ}
    (hb : 0 ≤ b) (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal b) :
    ∫ ω, f ω ∂μ ≤ b := by
  by_cases hi : Integrable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hi.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hb h
  · rw [integral_undef hi]
    exact hb

/-- **e-BH controls the FDR, Bochner form**: `∫ FDP ≤ α |H0| / m ≤ α`. -/
theorem integral_falseDiscoveryProportion_eBHRejections_le {α : ℝ} (hα : 0 ≤ α)
    (E : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) (hnull : ∀ i ∈ H0, IsEValue μ (E i)) :
    ∫ ω, falseDiscoveryProportion H0 (eBHRejections α fun j => E j ω) ∂μ ≤ α :=
  (integral_le_of_lintegral_ofReal_le (fun _ => falseDiscoveryProportion_nonneg _ _)
    (by positivity) (lintegral_falseDiscoveryProportion_eBHRejections_le hα E H0 hnull)).trans
    (mul_card_div_le_alpha hα H0)

/-- **e-BH at a stopping time.** If every true-null endpoint carries an e-process for a common
filtration and `τ` is a bounded stopping time, the e-BH procedure applied to the stopped
values `E i τ` has `E[FDP] ≤ α |H0| / m`: the analyst may choose when to stop, using all data
so far, and still control the FDR. -/
theorem lintegral_falseDiscoveryProportion_eBHRejections_stoppedValue_le {α : ℝ}
    (hα : 0 ≤ α) {𝒢 : Filtration ℕ m0} (E : Fin m → ℕ → Ω → ℝ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsEProcess μ 𝒢 (E i)) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫⁻ ω, ENNReal.ofReal
        (falseDiscoveryProportion H0 (eBHRejections α fun j => stoppedValue (E j) τ ω)) ∂μ ≤
      ENNReal.ofReal (α * H0.card / m) :=
  lintegral_falseDiscoveryProportion_eBHRejections_le hα (fun j => stoppedValue (E j) τ) H0
    fun i hi => (hnull i hi).isEValue_stoppedValue hτ hbdd

end MathlibExt.Probability.Statistics.MultipleTesting
