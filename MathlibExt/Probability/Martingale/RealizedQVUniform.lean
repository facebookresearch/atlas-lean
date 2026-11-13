/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.RealizedQV

/-!
# Realized quadratic variation: uniform convergence and the converse direction

For a triangular array `ξ n i` (row `n` filtered by `𝓕 n`, `ξ n i` measurable for
`𝓕 n (i+1)`) write `U n t = ∑_{j < ⌊n t⌋} ξ n j²` for the realized and
`V n t = ∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j]` for the predictable quadratic variation.
`MathlibExt.Probability.Martingale.RealizedQV` (roadmap task T123) proves that `V n t → t` in
probability for every `t` implies `U n t → t` for every `t`. This file adds the two pieces that
file lists as not proved.

## Main results

* `tendstoInMeasure_iSup_abs_sub_of_monotoneOn`: processes `f n t` that are a.e. nondecreasing
  in `t ∈ [0,1]` and converge in probability to `t` for every fixed `t` converge uniformly:
  `sup_{t ∈ [0,1]} |f n t - t| → 0` in probability.
* `tendstoInMeasure_iSup_abs_sum_sq_floor_sub_of_qv` (**uniform in `t`**): under T82's
  hypotheses, `sup_{t ∈ [0,1]} |∑_{j < ⌊n t⌋} ξ n j² - t| → 0` in probability.
* `exists_eventually_measure_lt_sum_condExp_le` (**tightness transfer**): under Lindeberg,
  boundedness in probability of the realized variation `∑_{j < k n} ξ n j²` implies that of
  the predictable variation `∑_{j < k n} E[ξ n j² | 𝓕 n j]`.
* `tendstoInMeasure_sup_abs_sum_sq_sub_condExp_of_sq` (**Hall–Heyde, Theorem 2.23, converse
  hypothesis**): Lindeberg plus tightness of the *realized* variation imply
  `max_{i ≤ k n} |∑_{j < i} (ξ n j² - E[ξ n j² | 𝓕 n j])| → 0` in probability.
* `tendstoInMeasure_sum_condExp_floor_of_rqv` (**converse direction**): under Lindeberg,
  `U n t → t` in probability for every `t ∈ [0,1]` implies `V n t → t` for every `t`.
* `tendstoInMeasure_iSup_abs_sum_condExp_floor_sub_of_rqv`: the same conclusion uniformly in `t`.

## Proof

*Uniformity.* Both variations are nondecreasing step functions of `t` (squares and conditional
expectations of squares are nonnegative). For a grid `i / N`, `i ≤ N`, if
`|f(i/N) - i/N| < 1/N` at every grid point then monotonicity squeezes `f t` between neighboring
grid values, so `|f t - t| < 2/N` for every `t ∈ [0,1]` (`abs_sub_lt_of_grid`). The `N + 1`
grid events have probabilities tending to `0`.

*Converse.* Split `ξ² = a + b` at `|ξ| = 1`, so `0 ≤ a ≤ 1`. Stop predictably once the realized
truncated sum `∑_{i < j} a i` passes `C`: the indicator `𝟙{∑_{i < j} a i ≤ C}` is
`𝓕 n j`-measurable, so `E ∑_j 𝟙{…} E[a j | 𝓕 n j] = E ∑_j 𝟙{…} a j ≤ C + 1`, and Markov's
inequality bounds the stopped predictable sum. The large parts have
`E ∑_j E[b j | 𝓕 n j]` equal to the Lindeberg sum at level `1`. Off `{∑_{j<K} ξ j² > C}` the
stopping never triggers. This Lenglart-type bound gives the tightness transfer; T123's
Theorem 2.23 then gives the uniform closeness of `U` and `V`.

## Scope and what is not proved

* The Lindeberg condition is the unconditional `LindebergConditionTriangular` of T82 and T123,
  rows have length `n`, and index cutoffs satisfy `k n ≤ n`, as in T123.
* The limit is the identity `t`; general continuous nondecreasing limits are not treated.
* The supremum over `t ∈ [0,1]` is the real `iSup`. Each path `t ↦ U n t` takes only the
  `n + 1` values at `⌊n t⌋ ∈ {0, …, n}`, so the supremum is a finite maximum.

## Source

P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980),
Theorem 2.23: under the conditional Lindeberg condition, if either
`U²_{n k_n} = ∑_{i ≤ k_n} X_{ni}²` or `V²_{n k_n} = ∑_{i ≤ k_n} E[X_{ni}² | 𝓕_{n,i-1}]` is
tight, then `max_{i ≤ k_n} |U²_{ni} - V²_{ni}| → 0` in probability. T123 proves the `V`-tight
case; this file supplies the `U`-tight case by reducing it to the `V`-tight one.
(Statement paraphrased; theorem number matches a secondary citation (arXiv:2506.22354 §3);
book not consulted.)
The uniform-in-`t` step is the monotone-function argument behind Pólya's theorem (pointwise
convergence of monotone functions to a continuous limit is uniform).

Reused from `RealizedQV` (merged): `tendstoInMeasure_sup_abs_sum_sq_sub_condExp` (Theorem 2.23,
`V`-tight case) and `tendstoInMeasure_sum_sq_floor_of_qv`. Proved here: the grid lemma, the
tightness transfer, and the corollaries. Two private helpers are copied verbatim from
`RealizedQV`, where they are private: `measure_ge_le_ofReal_integral_div'` (copy of
`measure_ge_le_ofReal_integral_div`) and `exists_eventually_measure_lt_le'` (copy of
`exists_eventually_measure_lt_le`); delete both once the originals are made public.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

variable {Ω : Type*}

/-! ### Uniform convergence of monotone processes -/

/-- A function nondecreasing on `[0,1]` that is within `r` of the identity at every grid point
`i / N`, `i ≤ N`, is within `r + 1/N` of the identity on all of `[0,1]`. -/
lemma abs_sub_lt_of_grid {g : ℝ → ℝ} (hg : MonotoneOn g (Icc 0 1)) {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hgrid : ∀ i ≤ N, |g (i / N) - i / N| < r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |g t - t| < r + 1 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < r := (abs_nonneg _).trans_lt (hgrid 0 (Nat.zero_le N))
  set i := ⌊(N : ℝ) * t⌋₊ with hi_def
  have hiN : i ≤ N := Nat.floor_le_of_le (by nlinarith [ht.2])
  rcases hiN.lt_or_eq with hlt | heq
  · have hi_le : (i : ℝ) / N ≤ t := by
      rw [div_le_iff₀ hNpos, mul_comm]
      exact Nat.floor_le (mul_nonneg hNpos.le ht.1)
    have hi_lt : t < ((i + 1 : ℕ) : ℝ) / N := by
      rw [lt_div_iff₀ hNpos, mul_comm]
      push_cast
      exact Nat.lt_floor_add_one _
    have hmem0 : (i : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hNpos).2 (by exact_mod_cast hlt.le)⟩
    have hmem1 : ((i + 1 : ℕ) : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hNpos).2 (by exact_mod_cast hlt)⟩
    have hlo := hg hmem0 ht hi_le
    have hhi := hg ht hmem1 hi_lt.le
    have h0 := abs_lt.1 (hgrid i hlt.le)
    have h1 := abs_lt.1 (hgrid (i + 1) hlt)
    have hstep : ((i + 1 : ℕ) : ℝ) / N = i / N + 1 / N := by push_cast; ring
    rw [hstep] at h1 hhi hi_lt
    refine abs_lt.2 ⟨?_, ?_⟩ <;> linarith
  · have ht1 : t = 1 := by
      refine le_antisymm ht.2 ?_
      have := Nat.lt_floor_add_one ((N : ℝ) * t)
      rw [← hi_def, heq] at this
      by_contra h
      rw [not_le] at h
      have hfl : (N : ℝ) ≤ N * t := by
        have := Nat.floor_le (mul_nonneg hNpos.le ht.1)
        rw [← hi_def, heq] at this
        exact this
      nlinarith
    have := hgrid N le_rfl
    rw [div_self hNpos.ne'] at this
    rw [ht1]
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith

/-- **Uniform convergence from pointwise convergence for monotone processes.** If, for every
`n`, almost every path `t ↦ f n t ω` is nondecreasing on `[0,1]`, and `f n t → t` in probability
for every `t ∈ [0,1]`, then `sup_{t ∈ [0,1]} |f n t - t| → 0` in probability. -/
theorem tendstoInMeasure_iSup_abs_sub_of_monotoneOn {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → ℝ → Ω → ℝ} (hmono : ∀ n, ∀ᵐ ω ∂μ, MonotoneOn (fun t => f n t ω) (Icc 0 1))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, TendstoInMeasure μ (fun n => f n t) atTop fun _ => t) :
    TendstoInMeasure μ (fun n ω => ⨆ t : Icc (0 : ℝ) 1, |f n t ω - t|) atTop fun _ => 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hNε : 2 / (N : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at hN
    linarith
  have hgridmem : ∀ i ≤ N, (i : ℝ) / N ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨by positivity, (div_le_one hNpos).2 (by exact_mod_cast hi)⟩
  have hsum : Tendsto (fun n => ∑ i ∈ Finset.range (N + 1),
      μ {ω | 1 / (N : ℝ) ≤ ‖f n (i / N) ω - i / N‖}) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ _i ∈ Finset.range (N + 1), (0 : ℝ≥0∞) by simp]
    refine tendsto_finsetSum _ fun i hi => ?_
    exact tendstoInMeasure_iff_norm.1
      (hf _ (hgridmem i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))) _ (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (measure_mono_ae ?_).trans (measure_biUnion_finset_le (Finset.range (N + 1))
      fun i => {ω | 1 / (N : ℝ) ≤ ‖f n (i / N) ω - i / N‖})
  filter_upwards [hmono n] with ω hω hεω
  simp only [sub_zero, Real.norm_eq_abs] at hεω
  rw [abs_of_nonneg (Real.iSup_nonneg fun t => abs_nonneg _)] at hεω
  obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup (lt_of_lt_of_le (half_lt_self hε) hεω)
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Real.norm_eq_abs, not_exists, not_le] at hnot
  have hgrid : ∀ i ≤ N, |f n (i / N) ω - i / N| < 1 / N := fun i hi =>
    hnot i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have := abs_sub_lt_of_grid hω hN0 hgrid t.2
  have h2 : 1 / (N : ℝ) + 1 / N = 2 / N := by ring
  linarith

/-- A sum of nonnegative terms up to `⌊n t⌋` is nondecreasing in `t`. -/
lemma monotone_sum_range_floor_mul {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) (n : ℕ) :
    Monotone fun t : ℝ => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, g j := fun _ _ hst =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))))
    fun j _ _ => hg j

/-- **Uniform-in-`t` convergence of the realized quadratic variation.** Under the hypotheses of
T82's functional CLT `tendstoInDistribution_arrayStepProcess` (square integrability, `ξ n i`
measurable for `𝓕 n (i+1)`, predictable quadratic variation `→ t` for every `t ∈ [0,1]`,
Lindeberg),
`sup_{t ∈ [0,1]} |∑_{j < ⌊n t⌋} ξ n j² - t| → 0` in probability. -/
theorem tendstoInMeasure_iSup_abs_sum_sq_floor_sub_of_qv {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω => ⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, ξ n j ω ^ 2 - (t : ℝ)|) atTop (fun _ => 0) :=
  tendstoInMeasure_iSup_abs_sub_of_monotoneOn
    (f := fun n t ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, ξ n j ω ^ 2)
    (fun n => Eventually.of_forall fun ω =>
      (monotone_sum_range_floor_mul (fun j => sq_nonneg (ξ n j ω)) n).monotoneOn _)
    fun t ht => tendstoInMeasure_sum_sq_floor_of_qv hξ hL2 hQV hLind ⟨t, ht⟩

/-! ### Converse direction: tightness transfer from realized to predictable variation -/

/-- Markov's inequality: for an a.e. nonnegative integrable `f` and `δ > 0`,
`μ {δ ≤ f} ≤ ofReal (∫ f / δ)`.

Private copy of `RealizedQV`'s private `measure_ge_le_ofReal_integral_div`; delete once that
lemma is made public (T165 follow-up). -/
private lemma measure_ge_le_ofReal_integral_div' {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hf : Integrable f μ) {δ : ℝ}
    (hδ : 0 < δ) : μ {ω | δ ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂μ) / δ) := by
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hδ, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hf0 hf δ

/-- Stopping a sum of terms in `[0,1]` once the partial sum before the current term exceeds
`C` overshoots `C` by at most `1`: `∑_{j < K} 𝟙{∑_{i < j} a i ≤ C} a j ≤ C + 1`. -/
private lemma sum_ite_lt_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (K : ℕ) :
    ∑ j ∈ Finset.range K, (if ∑ i ∈ Finset.range j, a i ≤ C then a j else 0) ≤ C + 1 := by
  classical
  set J := (Finset.range K).filter fun j => ∑ i ∈ Finset.range j, a i ≤ C with hJ
  rw [← Finset.sum_filter]
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · rw [← hJ, hJe, Finset.sum_empty]; linarith
  · set j₀ := J.max' hJne
    have hj₀ : j₀ ∈ J := J.max'_mem hJne
    calc ∑ j ∈ J, a j ≤ ∑ i ∈ Finset.range (j₀ + 1), a i := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => (ha j).1
          exact Finset.mem_range.2 (Nat.lt_succ_of_le (J.le_max' j hj))
      _ = ∑ i ∈ Finset.range j₀, a i + a j₀ := Finset.sum_range_succ _ _
      _ ≤ C + 1 := add_le_add (Finset.mem_filter.1 hj₀).2 (ha j₀).2

/-- **One-row Lenglart-type bound.** Let `x 0, x 1, …` be square-integrable with `x i`
measurable for `F (i+1)` and write `c j = E[x j² | F j]`. For `C ≥ 0` and `M > 0`,
`P(∑_{j<K} c j > M + 1) ≤ P(∑_{j<K} x j² > C) + (C + 1) / M + L`, where
`L = ∑_{j<K} E[x j² 𝟙{|x j| > 1}]` is the Lindeberg sum at level `1`. -/
lemma measure_lt_sum_condExp_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ m} {x : ℕ → Ω → ℝ}
    (hx : ∀ i, StronglyMeasurable[F (i + 1)] (x i)) (hL2 : ∀ i, MemLp (x i) 2 μ)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 < M) (K : ℕ) :
    μ {ω | M + 1 < ∑ j ∈ Finset.range K, (μ[fun ω => x j ω ^ 2 | F j]) ω} ≤
      μ {ω | C < ∑ j ∈ Finset.range K, x j ω ^ 2} + ENNReal.ofReal ((C + 1) / M) +
        ENNReal.ofReal (∑ j ∈ Finset.range K,
          ∫ ω, x j ω ^ 2 * Set.indicator {ω' | 1 < |x j ω'|} 1 ω ∂μ) := by
  set c : ℕ → Ω → ℝ := fun j => μ[fun ω => x j ω ^ 2 | F j] with hc_def
  set S : ℕ → Set Ω := fun j => {ω | 1 < |x j ω|} with hS_def
  set b : ℕ → Ω → ℝ := fun j => (S j).indicator fun ω => x j ω ^ 2 with hb_def
  set a : ℕ → Ω → ℝ := fun j => (S j)ᶜ.indicator fun ω => x j ω ^ 2 with ha_def
  set A : ℕ → Set Ω := fun j => {ω | ∑ i ∈ Finset.range j, a i ω ≤ C} with hA_def
  set W : Ω → ℝ := fun ω => ∑ j ∈ Finset.range K, (A j).indicator (μ[a j | F j]) ω with hW_def
  -- measurability
  have hSm : ∀ j, MeasurableSet[F (j + 1)] (S j) := fun j =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hx j).measurable)
  have hSm' : ∀ j, MeasurableSet (S j) := fun j => F.le _ _ (hSm j)
  have hsq : ∀ j, StronglyMeasurable[F (j + 1)] (fun ω => x j ω ^ 2) := fun j => (hx j).pow 2
  have ha_sm : ∀ j, StronglyMeasurable[F (j + 1)] (a j) := fun j =>
    (hsq j).indicator (hSm j).compl
  have hAm : ∀ j, MeasurableSet[F j] (A j) := by
    intro j
    have : StronglyMeasurable[F j] (fun ω => ∑ i ∈ Finset.range j, a i ω) :=
      Finset.stronglyMeasurable_fun_sum _ fun i hi =>
        (ha_sm i).mono (F.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hi)))
    exact measurableSet_le this.measurable measurable_const
  have hAm' : ∀ j, MeasurableSet (A j) := fun j => F.le _ _ (hAm j)
  -- integrability and bounds
  have hsq_int : ∀ j, Integrable (fun ω => x j ω ^ 2) μ := fun j => (hL2 j).integrable_sq
  have hb_int : ∀ j, Integrable (b j) μ := fun j => (hsq_int j).indicator (hSm' j)
  have ha_int : ∀ j, Integrable (a j) μ := fun j => (hsq_int j).indicator (hSm' j).compl
  have hb_nn : ∀ j ω, 0 ≤ b j ω := fun j ω =>
    Set.indicator_nonneg (fun ω _ => sq_nonneg (x j ω)) ω
  have ha_bd : ∀ j ω, 0 ≤ a j ω ∧ a j ω ≤ 1 ∧ a j ω ≤ x j ω ^ 2 := by
    intro j ω
    by_cases h : ω ∈ S j
    · simp [ha_def, h, sq_nonneg]
    · have h' : |x j ω| ≤ 1 := not_lt.1 h
      have : x j ω ^ 2 ≤ 1 := by
        rw [← sq_abs, ← one_pow 2]; exact pow_le_pow_left₀ (abs_nonneg _) h' 2
      simp only [ha_def, Set.indicator_of_mem (Set.mem_compl h)]
      exact ⟨sq_nonneg _, this, le_rfl⟩
  have hW_int : Integrable W μ :=
    integrable_finsetSum _ fun j _ => integrable_condExp.indicator (hAm' j)
  -- the stopped predictable sum has mean at most `C + 1`
  have hEW : ∫ ω, W ω ∂μ ≤ C + 1 := by
    have hpt : ∫ ω, W ω ∂μ = ∫ ω, ∑ j ∈ Finset.range K, (A j).indicator (a j) ω ∂μ := by
      rw [hW_def, integral_finsetSum _ fun j _ => integrable_condExp.indicator (hAm' j),
        integral_finsetSum _ fun j _ => (ha_int j).indicator (hAm' j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_indicator (hAm' j), integral_indicator (hAm' j),
        setIntegral_condExp (F.le j) (ha_int j) (hAm j)]
    rw [hpt]
    calc ∫ ω, ∑ j ∈ Finset.range K, (A j).indicator (a j) ω ∂μ ≤ ∫ _ω, C + 1 ∂μ := by
          refine integral_mono
            (integrable_finsetSum _ fun j _ => (ha_int j).indicator (hAm' j))
            (integrable_const _) fun ω => ?_
          simpa only [hA_def, Set.indicator_apply, Set.mem_ofPred_eq] using
            sum_ite_lt_le (fun j => a j ω) (fun j => ⟨(ha_bd j ω).1, (ha_bd j ω).2.1⟩) hC K
      _ = C + 1 := by simp
  have hW_nn : 0 ≤ᵐ[μ] W := by
    have : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ (μ[a j | F j]) ω := ae_all_iff.2 fun j =>
      condExp_nonneg (Eventually.of_forall fun ω => (ha_bd j ω).1)
    filter_upwards [this] with ω hω
    exact Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun ω _ => hω j) ω
  have hPW : μ {ω | M ≤ W ω} ≤ ENNReal.ofReal ((C + 1) / M) :=
    (measure_ge_le_ofReal_integral_div' hW_nn hW_int hM).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hEW hM.le))
  -- the large parts: Markov
  set L := ∑ j ∈ Finset.range K, ∫ ω, x j ω ^ 2 * Set.indicator {ω' | 1 < |x j ω'|} 1 ω ∂μ
    with hL_def
  have hLb : L = ∑ j ∈ Finset.range K, ∫ ω, b j ω ∂μ := by
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae
      (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ S j
    · simp only [hb_def, Set.indicator_of_mem h]
      rw [Set.indicator_of_mem (show ω ∈ {ω' | 1 < |x j ω'|} from h), Pi.one_apply, mul_one]
    · simp only [hb_def, Set.indicator_of_notMem h]
      rw [Set.indicator_of_notMem (show ω ∉ {ω' | 1 < |x j ω'|} from h), mul_zero]
  have hPB : μ {ω | 1 ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω} ≤ ENNReal.ofReal L := by
    refine (measure_ge_le_ofReal_integral_div' ?_
      (integrable_finsetSum _ fun j _ => integrable_condExp) one_pos).trans (le_of_eq ?_)
    · have : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ (μ[b j | F j]) ω := ae_all_iff.2 fun j =>
        condExp_nonneg (Eventually.of_forall fun ω => hb_nn j ω)
      filter_upwards [this] with ω hω
      exact Finset.sum_nonneg fun j _ => hω j
    · rw [integral_finsetSum _ fun j _ => integrable_condExp, hLb, div_one]
      exact congrArg ENNReal.ofReal
        (Finset.sum_congr rfl fun j _ => integral_condExp (F.le j))
  -- pointwise decomposition off the bad events
  have hab : ∀ j, (fun ω => x j ω ^ 2) = a j + b j := fun j =>
    (Set.indicator_compl_add_self (S j) _).symm
  have hdec : ∀ᵐ ω ∂μ, ∀ j, c j ω = (μ[a j | F j]) ω + (μ[b j | F j]) ω := by
    refine ae_all_iff.2 fun j => ?_
    have : c j =ᵐ[μ] μ[a j | F j] + μ[b j | F j] := by
      simp only [hc_def]
      rw [hab j]
      exact condExp_add (ha_int j) (hb_int j) _
    filter_upwards [this] with ω hω
    exact hω
  have hsub : {ω | M + 1 < ∑ j ∈ Finset.range K, c j ω} ≤ᵐ[μ]
      ({ω | C < ∑ j ∈ Finset.range K, x j ω ^ 2} ∪ {ω | M ≤ W ω}) ∪
        {ω | 1 ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω} := by
    filter_upwards [hdec] with ω hω hT
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_le] at hnot hT
    obtain ⟨⟨hU, hWω⟩, hBω⟩ := hnot
    have hAj : ∀ j < K, ω ∈ A j := by
      intro j hj
      change ∑ i ∈ Finset.range j, a i ω ≤ C
      calc ∑ i ∈ Finset.range j, a i ω ≤ ∑ i ∈ Finset.range K, x i ω ^ 2 :=
            (Finset.sum_le_sum fun i _ => (ha_bd i ω).2.2).trans
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj.le)
                fun i _ _ => sq_nonneg _)
        _ ≤ C := hU
    have hWeq : W ω = ∑ j ∈ Finset.range K, (μ[a j | F j]) ω :=
      Finset.sum_congr rfl fun j hj =>
        Set.indicator_of_mem (hAj j (Finset.mem_range.1 hj)) _
    have : ∑ j ∈ Finset.range K, c j ω = W ω + ∑ j ∈ Finset.range K, (μ[b j | F j]) ω := by
      rw [hWeq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hω j
    linarith
  calc _ ≤ μ (({ω | C < ∑ j ∈ Finset.range K, x j ω ^ 2} ∪ {ω | M ≤ W ω}) ∪
        {ω | 1 ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω}) := measure_mono_ae hsub
    _ ≤ μ {ω | C < ∑ j ∈ Finset.range K, x j ω ^ 2} + μ {ω | M ≤ W ω} +
        μ {ω | 1 ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω} :=
      (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ _ := by gcongr

/-- **Tightness transfer (realized to predictable variation).** Let row `n` of `ξ` be
square-integrable with `ξ n i` measurable for `𝓕 n (i+1)`, satisfying the Lindeberg condition,
and let `k n ≤ n`. If the realized variations `∑_{j < k n} ξ n j²` are bounded in probability,
so are the predictable variations `∑_{j < k n} E[ξ n j² | 𝓕 n j]`. -/
theorem exists_eventually_measure_lt_sum_condExp_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hLind : LindebergConditionTriangular ξ μ) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n)
    (htightU : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ n in atTop,
      μ {ω | C < ∑ j ∈ Finset.range (k n), ξ n j ω ^ 2} ≤ ENNReal.ofReal η) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ n in atTop,
      μ {ω | C < ∑ j ∈ Finset.range (k n), (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω} ≤
        ENNReal.ofReal η := by
  intro η hη
  obtain ⟨C₀, hC₀⟩ := htightU (η / 3) (by positivity)
  set C := max C₀ 0 with hC_def
  have hC : 0 ≤ C := le_max_right _ _
  set M := 3 * (C + 1) / η with hM_def
  have hM : 0 < M := by positivity
  have hCM : (C + 1) / M = η / 3 := by rw [hM_def]; field_simp
  have hLnn : ∀ n j, 0 ≤ ∫ ω, ξ n j ω ^ 2 * Set.indicator {ω' | 1 < |ξ n j ω'|} 1 ω ∂μ :=
    fun n j => integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (Set.indicator_nonneg
      (fun _ _ => zero_le_one) ω)
  refine ⟨M + 1, ?_⟩
  filter_upwards [hC₀, (hLind 1 one_pos).eventually (gt_mem_nhds (show (0 : ℝ) < η / 3 by
    positivity))] with n hn hLn
  have hLle : ∑ j ∈ Finset.range (k n),
      ∫ ω, ξ n j ω ^ 2 * Set.indicator {ω' | 1 < |ξ n j ω'|} 1 ω ∂μ ≤ η / 3 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (hk n))
      fun j _ _ => hLnn n j).trans hLn.le
  calc _ ≤ _ := measure_lt_sum_condExp_le (μ := μ) (F := 𝓕 n) (x := ξ n) (hξ n) (hL2 n) hC hM
        (k n)
    _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) := by
        rw [hCM]
        gcongr
        exact (measure_mono fun ω (hω : C < _) => (show C₀ < _ from
          lt_of_le_of_lt (le_max_left _ _) hω)).trans hn
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **Hall–Heyde, Theorem 2.23, with the realized variation tight.** Under the hypotheses of
`tendstoInMeasure_sup_abs_sum_sq_sub_condExp` with tightness of the predictable variation
replaced by tightness of the realized variation `∑_{j < k n} ξ n j²`,
`max_{i ≤ k n} |∑_{j < i} ξ n j² - ∑_{j < i} E[ξ n j² | 𝓕 n j]| → 0` in probability. -/
theorem tendstoInMeasure_sup_abs_sum_sq_sub_condExp_of_sq {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hLind : LindebergConditionTriangular ξ μ) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n)
    (htightU : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ n in atTop,
      μ {ω | C < ∑ j ∈ Finset.range (k n), ξ n j ω ^ 2} ≤ ENNReal.ofReal η) :
    TendstoInMeasure μ
      (fun n ω => (Finset.range (k n + 1)).sup' Finset.nonempty_range_add_one fun i =>
        |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|)
      atTop (fun _ => 0) :=
  tendstoInMeasure_sup_abs_sum_sq_sub_condExp hξ hL2 hLind k hk
    (exists_eventually_measure_lt_sum_condExp_le hξ hL2 hLind k hk htightU)

/-- Convergence in probability to a constant gives boundedness in probability.

Private copy of `RealizedQV`'s private `exists_eventually_measure_lt_le`; delete once that
lemma is made public (T165 follow-up). -/
private lemma exists_eventually_measure_lt_le' {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {t : ℝ} (h : TendstoInMeasure μ f atTop fun _ => t) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ᶠ n in atTop, μ {ω | C < f n ω} ≤ ENNReal.ofReal η := by
  refine ⟨t + 1, ?_⟩
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (tendstoInMeasure_iff_norm.1 h 1 one_pos)
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)] with n hn
  refine (measure_mono fun ω (hω : t + 1 < f n ω) => ?_).trans hn
  change 1 ≤ ‖f n ω - t‖
  rw [Real.norm_eq_abs]
  exact le_trans (by linarith) (le_abs_self _)

/-- If `f n → t` in probability and `|g n - f n| ≤ D n` with `D n → 0` in probability, then
`g n → t` in probability. -/
private lemma tendstoInMeasure_of_abs_sub_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g D : ℕ → Ω → ℝ} {t : ℝ} (hf : TendstoInMeasure μ f atTop fun _ => t)
    (hD : TendstoInMeasure μ D atTop fun _ => 0) (hle : ∀ n ω, |g n ω - f n ω| ≤ D n ω) :
    TendstoInMeasure μ g atTop fun _ => t := by
  rw [tendstoInMeasure_iff_norm] at hf hD ⊢
  intro ε hε
  have hlim := (hD (ε / 2) (half_pos hε)).add (hf (ε / 2) (half_pos hε))
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, sub_zero] at hω ⊢
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
  obtain ⟨h1, h2⟩ := hnot
  have h3 := abs_sub_le (g n ω) (f n ω) t
  linarith [hle n ω, le_abs_self (D n ω)]

/-- **Predictable quadratic variation from realized quadratic variation** (converse of
`tendstoInMeasure_sum_sq_floor_of_qv`). Let row `n` of `ξ` be square-integrable with `ξ n i`
measurable for `𝓕 n (i+1)` and satisfying the Lindeberg condition. If the realized variation
`∑_{j < ⌊n t⌋} ξ n j²` tends to `t` in probability for every `t ∈ [0,1]` (the hypothesis `hRQV`
of T81's `tendstoInDistribution_fdd_martingaleDifference_floor`), then so does the predictable
variation: `∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j] → t` in probability for every `t ∈ [0,1]` (the
hypothesis `hQV` of T82's `tendstoInDistribution_arrayStepProcess`). -/
theorem tendstoInMeasure_sum_condExp_floor_of_rqv {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hRQV : ∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n j ω ^ 2) atTop
      (fun _ => t.1))
    (hLind : LindebergConditionTriangular ξ μ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t) := by
  intro t ht
  have hU := hRQV ⟨t, ht⟩
  have hk : ∀ n : ℕ, ⌊(n : ℝ) * t⌋₊ ≤ n := fun n =>
    Nat.floor_le_of_le (by nlinarith [ht.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hD := tendstoInMeasure_sup_abs_sum_sq_sub_condExp_of_sq hξ hL2 hLind
    (fun n => ⌊(n : ℝ) * t⌋₊) hk (exists_eventually_measure_lt_le' hU)
  refine tendstoInMeasure_of_abs_sub_le hU hD fun n ω => ?_
  set K := ⌊(n : ℝ) * t⌋₊
  have hle : |∑ j ∈ Finset.range K, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)| ≤
      (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun i =>
        |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)| :=
    Finset.le_sup' (fun i => |∑ j ∈ Finset.range i,
      (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|) (by simp)
  rw [Finset.sum_sub_distrib, abs_sub_comm] at hle
  exact hle

/-- **Uniform-in-`t` convergence of the predictable quadratic variation from the realized one.**
Under the hypotheses of `tendstoInMeasure_sum_condExp_floor_of_rqv`,
`sup_{t ∈ [0,1]} |∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j] - t| → 0` in probability. -/
theorem tendstoInMeasure_iSup_abs_sum_condExp_floor_sub_of_rqv {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hRQV : ∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n j ω ^ 2) atTop
      (fun _ => t.1))
    (hLind : LindebergConditionTriangular ξ μ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω => ⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω - (t : ℝ)|)
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_iSup_abs_sub_of_monotoneOn
    (f := fun n t ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
    (fun n => ?_) (tendstoInMeasure_sum_condExp_floor_of_rqv hξ hL2 hRQV hLind)
  have : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω := ae_all_iff.2 fun j =>
    condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (ξ n j ω))
  filter_upwards [this] with ω hω
  exact (monotone_sum_range_floor_mul hω n).monotoneOn _

end

end MathlibExt.Probability.Martingale
