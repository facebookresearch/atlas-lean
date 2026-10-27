/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Wald's equation

If `X₁, X₂, …` are identically distributed integrable real random variables,
`T` is a stopping time with `E[T] < ∞`, and each `Xₖ` is independent of the
filtration at time `k`, then the expectation of the randomly stopped sum is
`E[S_T] = E[X₁] · E[T]`, where `S_T = ∑_{i < T} Xᵢ`.

## Source

This formalizes the target "Theorem (Wald's equation)" (Lecture 23, Stopping
times section) of `v1/Atlas/TheoryOfProbability/targets.yaml`: "Let `Xᵢ` be
i.i.d. with `E|Xᵢ| < ∞`. If `N` is a stopping time with `EN < ∞` then
`ES_N = EX₁ · EN`." Its v1 formalization is
`v1/Atlas/TheoryOfProbability/code/WaldEquation.lean` (`wald_equation`,
fully proved in v1).

The hypotheses here are slightly weaker than v1's: v1 also assumed
`iIndepFun X μ`, but that hypothesis is unused in its proof (its only use
was a `hind_norm` fact that is never referenced), so it is dropped. The
independence actually used is that each `Xₖ` is independent of the filtration
at time `k`, together with identical distribution.

## Main results

* `MeasureTheory.wald_equation`: `E[∑_{i < T} Xᵢ] = E[X₀] · E[T]`.

## Proof outline

Write the stopped sum as the series `∑'ₙ Xₙ · 1_{T > n}`. Each summand
factors, `E[Xₙ · 1_{T > n}] = E[Xₙ] · P(T > n)`, because `1_{T > n}` is
`ℱₙ`-measurable (as `T` is a stopping time) and `Xₙ` is independent of `ℱₙ`.
The series of `L¹` norms is summable since it equals
`E|X₀| · E[T] < ∞`, which justifies interchanging sum and integral. The
result then follows from the layer-cake identity `E[T] = ∑'ₙ P(T > n)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset ENNReal

namespace MeasureTheory

/-- If `T : Ω → ℕ`, viewed as a `WithTop ℕ`-valued process, is a stopping time with
respect to a filtration `f`, then `T` is measurable (with respect to the ambient
`σ`-algebra). -/
private theorem measurable_of_isStoppingTime {Ω : Type*} {m : MeasurableSpace Ω}
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ))) :
    Measurable T := by
  apply measurable_to_nat
  intro ω
  exact (f.le (T ω)) _ (by convert hT.measurableSet_eq (T ω) using 1; ext x; simp)

/-- For a measurable `T : Ω → ℕ`, the layer-cake identity in `ℝ≥0∞`:
`∑'_i μ {T > i} = ∫⁻ T dμ`. -/
private theorem tsum_measure_gt_eq_lintegral
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {T : Ω → ℕ} (hT_meas : Measurable T) :
    ∑' i, μ {ω | i < T ω} = ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by
  have hmeas : ∀ i, MeasurableSet {ω : Ω | i < T ω} := fun i => hT_meas measurableSet_Ioi
  have key : ∀ ω, (T ω : ℝ≥0∞) =
      ∑' i, Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [tsum_eq_sum (s := range (T ω))]
    · rw [Finset.sum_congr rfl (fun x hx => ite_eq_left (Finset.mem_range.mp hx)),
          Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]
    · intro i hi; exact ite_eq_right (Finset.mem_range.not.mp hi)
  calc ∑' i, μ {ω | i < T ω}
      = ∑' i, ∫⁻ a, Set.indicator {ω | i < T ω} (fun _ => 1) a ∂μ := by
        congr 1; ext i; rw [lintegral_indicator (hmeas i), setLIntegral_one]
      _ = ∫⁻ ω, ∑' i, Set.indicator {ω | i < T ω} (fun _ => 1) ω ∂μ := by
        rw [lintegral_tsum (fun i => (measurable_const.indicator (hmeas i)).aemeasurable)]
      _ = ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by congr 1; ext ω; exact (key ω).symm

/-- Express `k : ℕ` (cast to `ℝ`) as the tsum `∑' n, 1_{n < k}`. -/
private theorem nat_eq_tsum_indicator (k : ℕ) :
    (k : ℝ) = ∑' n, (if n < k then (1 : ℝ) else 0) := by
  rw [tsum_eq_sum (s := range k)]
  · rw [Finset.sum_congr rfl (fun x hx => ite_eq_left (Finset.mem_range.mp hx)),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · intro i hi; exact ite_eq_right (Finset.mem_range.not.mp hi)

/-- Real-valued layer-cake identity: if `T : Ω → ℕ` is measurable and integrable,
then `E T = ∑'_n P(T > n)`. -/
private theorem integral_nat_eq_tsum_prob
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → ℕ} (hT_meas : Measurable T)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (T ω : ℝ) ∂μ = ∑' n, (μ {ω | n < T ω}).toReal := by
  have heq : (fun ω => (T ω : ℝ)) = fun ω => ∑' n, (if n < T ω then (1 : ℝ) else 0) := by
    ext ω; exact nat_eq_tsum_indicator (T ω)
  rw [heq]
  have hind : ∀ n, (fun ω => if n < T ω then (1 : ℝ) else 0) =
      Set.indicator {ω | n < T ω} (fun _ => 1) := by
    intro n; ext ω; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hmeas : ∀ n, MeasurableSet {ω | n < T ω} := fun n => hT_meas measurableSet_Ioi
  rw [integral_tsum]
  · congr 1; ext n
    rw [hind n, integral_indicator_const _ (hmeas n), smul_eq_mul, mul_one, Measure.real]
  · intro n; rw [hind n]; exact aestronglyMeasurable_const.indicator (hmeas n)
  · have h1 : ∀ i a, ‖if i < T a then (1 : ℝ) else 0‖ₑ =
        Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ≥0∞)) a := by
      intro i a; simp only [Set.indicator_apply, Set.mem_ofPred_eq]; split_ifs with h <;> simp
    simp_rw [h1, lintegral_indicator (hmeas _), setLIntegral_one,
        tsum_measure_gt_eq_lintegral hT_meas]
    have hfi : ∫⁻ ω, ‖(T ω : ℝ)‖ₑ ∂μ < ⊤ := hT_int.2
    rw [show (fun ω => ‖(T ω : ℝ)‖ₑ) = (fun ω => (T ω : ℝ≥0∞)) from ?_] at hfi
    · exact hfi.ne
    · ext ω; simp [enorm]

/-- Rewrite a finite sum `∑_{i < n} f i` as an infinite tsum with indicator weights. -/
private theorem sum_range_eq_tsum_ite (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, f i = ∑' i, (if i < n then f i else 0) := by
  rw [tsum_eq_sum (s := range n)]
  · exact Finset.sum_congr rfl (fun x hx => by simp [Finset.mem_range.mp hx])
  · intro i hi; exact ite_eq_right (Finset.mem_range.not.mp hi)

/-- If the `σ`-algebra generated by `g : Ω → ℝ` is independent of a `σ`-algebra `m'`,
and `A` is `m'`-measurable, then `g` is independent of the indicator `1_A` (as
real-valued random variables). -/
private theorem indepFun_indicator_of_indep {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} {g : Ω → ℝ} {m' : MeasurableSpace Ω}
    (hindep : Indep (MeasurableSpace.comap g inferInstance) m' μ)
    {A : Set Ω} (hA : @MeasurableSet Ω m' A) :
    IndepFun g (Set.indicator A (fun _ => (1 : ℝ))) μ := by
  rw [IndepFun_iff_Indep]
  apply indep_of_indep_of_le_right hindep
  intro s hs
  obtain ⟨t, _, rfl⟩ := hs
  by_cases h1 : (1 : ℝ) ∈ t <;> by_cases h0 : (0 : ℝ) ∈ t
  · convert @MeasurableSet.univ Ω m'
    ext ω; simp [Set.indicator]; split_ifs <;> simp [*]
  · convert hA
    ext ω; simp [Set.indicator]; constructor
    · intro h; split_ifs at h with hmem <;> [exact hmem; exact absurd h h0]
    · intro hmem; simp [hmem, h1]
  · convert hA.compl
    ext ω; simp [Set.indicator]; constructor
    · intro h; split_ifs at h with hmem <;> [exact absurd h h1; exact hmem]
    · intro hmem; simp [show ¬(ω ∈ A) from hmem, h0]
  · convert @MeasurableSet.empty Ω m'
    ext ω; simp [Set.indicator]; split_ifs <;> simp [*]

/-- Factorisation lemma underlying Wald's equation: for a stopping time `T` and
identically distributed `X` with each `X k` independent of the filtration at time `k`,
`E[X_n · 1_{T > n}] = E[X_n] · P(T > n)`. -/
private theorem indep_factor
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_int : Integrable (X 0) μ)
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (n : ℕ) :
    ∫ ω, (if n < T ω then X n ω else 0) ∂μ =
      (∫ ω, X n ω ∂μ) * (μ {ω | n < T ω}).toReal := by
  have hS : MeasurableSet {ω : Ω | n < T ω} := by
    have hT_meas : Measurable T := measurable_of_isStoppingTime hT
    exact hT_meas measurableSet_Ioi
  have heq_ind : (fun ω => if n < T ω then X n ω else 0) =
      fun ω => X n ω * Set.indicator {ω | n < T ω} (fun _ => (1 : ℝ)) ω := by
    ext ω; simp only [Set.indicator_apply, Set.mem_ofPred_eq]; split_ifs with h <;> ring
  rw [heq_ind]
  have hindep : IndepFun (X n) (Set.indicator {ω | n < T ω} (fun _ => (1 : ℝ))) μ := by
    apply indepFun_indicator_of_indep (hXf n)
    have key : {ω : Ω | n < T ω} = {ω | (fun ω => (T ω : WithTop ℕ)) ω ≤ ↑n}ᶜ := by
      ext ω; simp [not_le]
    rw [key]
    exact (hT n).compl
  have hXn_aesm : AEStronglyMeasurable (X n) μ :=
    (hX_iid n 0).aestronglyMeasurable_iff.mpr hX_int.aestronglyMeasurable
  have hind_aesm : AEStronglyMeasurable (Set.indicator {ω | n < T ω} (fun _ => (1 : ℝ))) μ :=
    aestronglyMeasurable_const.indicator hS
  rw [hindep.integral_fun_mul_eq_mul_integral hXn_aesm hind_aesm]
  congr 1
  rw [integral_indicator_const _ hS, smul_eq_mul, mul_one]
  rfl

/-- Per-term bound for Wald's series: the truncated `L¹` norm of `X n` over `{T > n}`
is at most `E|X_0| · P(T > n)`. -/
private theorem lintegral_enorm_indicator_le
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_int : Integrable (X 0) μ)
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_meas : Measurable T) (n : ℕ) :
    ∫⁻ a in {ω | n < T ω}, ‖X n a‖ₑ ∂μ ≤
      (∫⁻ a, ‖X 0 a‖ₑ ∂μ) * μ {ω | n < T ω} := by
  simp_rw [show ∀ (g : ℕ → Ω → ℝ) (k : ℕ) (a : Ω), ‖g k a‖ₑ = .ofReal ‖g k a‖ from
    fun g k a => by rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]]
  have hint_norm : Integrable (fun ω => ‖X 0 ω‖) μ := hX_int.norm
  have hiid_norm : ∀ i j, IdentDistrib (fun ω => ‖X i ω‖) (fun ω => ‖X j ω‖) μ μ :=
    fun i j => (hX_iid i j).comp measurable_norm
  have hXf_norm : ∀ k, Indep (MeasurableSpace.comap (fun ω => ‖X k ω‖) inferInstance) (f k) μ := by
    intro k
    exact indep_of_indep_of_le_left (hXf k)
      (fun s ⟨t, ht, hts⟩ => ⟨(‖·‖) ⁻¹' t, measurable_norm ht, hts⟩)
  have hfactor := indep_factor hint_norm hiid_norm hT hXf_norm n
  have hmeas_set : MeasurableSet {ω : Ω | n < T ω} := hT_meas measurableSet_Ioi
  rw [show (fun ω => if n < T ω then ‖X n ω‖ else 0) =
    Set.indicator {ω | n < T ω} (fun ω => ‖X n ω‖) from by
      ext ω; simp only [Set.indicator_apply, Set.mem_ofPred_eq],
    integral_indicator hmeas_set] at hfactor
  rw [(hiid_norm n 0).integral_eq] at hfactor
  have hXn_int : Integrable (X n) μ := (hX_iid n 0).integrable_iff.mpr hX_int
  rw [← ofReal_integral_eq_lintegral_ofReal (hXn_int.norm.restrict)
      (ae_of_all _ (fun _ => norm_nonneg _))]
  rw [← ofReal_integral_eq_lintegral_ofReal hint_norm
      (ae_of_all _ (fun _ => norm_nonneg _))]
  rw [hfactor]
  rw [ENNReal.ofReal_mul (integral_nonneg (fun ω => norm_nonneg _))]
  gcongr
  exact ofReal_toReal_le

/-- Summability of the truncated `L¹` norms used to justify the interchange of sum
and integral in Wald's equation: under the i.i.d./independence hypotheses and
`E T < ∞`, the series `∑'_n ∫ |X_n · 1_{T > n}| dμ` is finite. -/
private theorem summability_condition
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_int : Integrable (X 0) μ)
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∑' (n : ℕ), ∫⁻ (a : Ω), ‖(if n < T a then X n a else 0)‖ₑ ∂μ ≠ ⊤ := by
  have hT_meas : Measurable T := measurable_of_isStoppingTime hT
  have h_rewrite : ∀ n a, ‖(if n < T a then X n a else 0)‖ₑ =
      Set.indicator {ω | n < T ω} (fun ω => ‖X n ω‖ₑ) a := by
    intro n a; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with h <;> simp [enorm]
  simp_rw [h_rewrite]
  have hmeas : ∀ n, MeasurableSet {ω : Ω | n < T ω} := fun n => hT_meas measurableSet_Ioi
  simp_rw [lintegral_indicator (hmeas _)]
  have key := fun n => lintegral_enorm_indicator_le hX_int hX_iid hT hXf hT_meas n
  have hbound_ne_top : ∑' n, (∫⁻ a, ‖X 0 a‖ₑ ∂μ) * μ {ω | n < T ω} ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left]
    apply ENNReal.mul_ne_top
    · exact hX_int.2.ne
    · rw [tsum_measure_gt_eq_lintegral hT_meas]
      have hfi : ∫⁻ ω, ‖(T ω : ℝ)‖ₑ ∂μ < ⊤ := hT_int.2
      rw [show (fun ω => ‖(T ω : ℝ)‖ₑ) = (fun ω => (T ω : ℝ≥0∞)) from by ext ω; simp [enorm]]
        at hfi
      exact hfi.ne
  exact ne_top_of_le_ne_top hbound_ne_top (ENNReal.tsum_le_tsum key)

/-- The truncated summand `ω ↦ X_n(ω) · 1_{T(ω) > n}` is `AEStronglyMeasurable`,
provided `X_n` is and `T` is measurable. -/
private theorem aesm_summand
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    {T : Ω → ℕ} (hT_meas : Measurable T) (n : ℕ) :
    AEStronglyMeasurable (fun ω => if n < T ω then X n ω else 0) μ := by
  have hXn_aesm : AEStronglyMeasurable (X n) μ :=
    (hX_iid n 0).aestronglyMeasurable_iff.mpr hX_int.aestronglyMeasurable
  have hset : MeasurableSet {ω : Ω | n < T ω} := hT_meas measurableSet_Ioi
  have heq : (fun ω => if n < T ω then X n ω else 0) = Set.indicator {ω | n < T ω} (X n) := by
    ext ω; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  exact hXn_aesm.indicator hset

/-- **Wald's equation.** Let `Xᵢ` be identically distributed integrable real
random variables and `T` a stopping time with `E T < ∞`, with each `Xₖ`
independent of the filtration at time `k`. Then `E[S_T] = E[X₁] · E[T]`,
where `S_T = ∑_{i < T} Xᵢ`. -/
theorem wald_equation
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), X i ω) ∂μ =
      (∫ ω, X 0 ω ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) := by
  have hT_meas : Measurable T := measurable_of_isStoppingTime hT
  simp_rw [sum_range_eq_tsum_ite (fun i => X i _) (T _)]
  rw [integral_tsum
    (fun n => aesm_summand hX_iid hX_int hT_meas n)
    (summability_condition hX_int hX_iid hT hXf hT_int)]
  simp_rw [indep_factor hX_int hX_iid hT hXf]
  simp_rw [(hX_iid _ 0).integral_eq]
  rw [tsum_mul_left]
  congr 1
  exact (integral_nat_eq_tsum_prob hT_meas hT_int).symm

end MeasureTheory
