/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.MartingaleTightness
public import MathlibExt.Probability.DoobLpInequality
public import Mathlib.Probability.CondVar

/-!
# Realized quadratic variation from predictable quadratic variation

For a triangular array `ξ n i` (row `n` filtered by `𝓕 n`, `ξ n i` measurable for
`𝓕 n (i+1)`), compare the *realized* quadratic variation `∑_{j < k} ξ n j²` with the
*predictable* one `∑_{j < k} E[ξ n j² | 𝓕 n j]`. Under the Lindeberg condition and
boundedness in probability of the predictable variation, the two are uniformly close along
the row. This is the array setting of `MathlibExt.Probability.Martingale.MartingaleTightness`
(roadmap task T82), and T82's hypotheses suffice.

## Main results

* `tendstoInMeasure_sup_abs_sum_sq_sub_condExp` (**Hall–Heyde, Theorem 2.23**): Lindeberg plus
  tightness of `∑_{j < k n} E[ξ n j² | 𝓕 n j]` (`k n ≤ n`) imply
  `max_{i ≤ k n} |∑_{j < i} (ξ n j² - E[ξ n j² | 𝓕 n j])| → 0` in probability.
* `tendstoInMeasure_sup_abs_sum_sq_sub_condExp_of_qv`: the same along the whole row
  (`k n = n`) under T82's hypotheses.
* `tendstoInMeasure_sum_sq_floor_of_qv`: under T82's hypotheses, `∑_{j < ⌊n t⌋} ξ n j² → t`
  in probability for every `t ∈ [0,1]`. This is verbatim the hypothesis `hRQV` of
  `tendstoInDistribution_fdd_martingaleDifference_floor` (`McLeishCLT`, roadmap task T81).

## Proof

Fix `ε > 0` and a level `C`. Split `ξ² = a + b` at `|ξ| = ε`. The large parts `b` and their
conditional expectations have total mean equal to the Lindeberg sum, so they vanish in
probability (Markov). The small parts give martingale differences `a - E[a | 𝓕]`, bounded by
`ε²`. Stopped predictably once the predictable variation passes `C`, their predictable
quadratic variation has mean at most `ε² C` (Mathlib's `condVar_ae_le_condExp_sq`). Doob's `L²`
maximal inequality (`Martingale.doob_sq_maximal_ineq_predictableQuadraticVariation`, from
`MathlibExt.Probability.DoobLpInequality`) bounds their running maximum. Off the event that the
predictable variation exceeds `C`, the stopping never triggers.

## Scope and what is not proved

* The Lindeberg condition is the unconditional `LindebergConditionTriangular` used by T82 and
  T81. Hall–Heyde assume only the conditional Lindeberg condition
  `∑_i E[ξ n i² 𝟙{|ξ n i| > ε} | 𝓕 n i] → 0` in probability, which the unconditional one
  implies. The conditional form is not treated.
* Rows have length `n` with index cutoffs `k n ≤ n`, as in T82. Hall–Heyde allow general row
  lengths `k_n`.
* The martingale property `E[ξ n i | 𝓕 n i] = 0` is not used, so it is not a hypothesis.
* The converse direction (predictable from realized variation) and uniform-in-`t`
  convergence of `∑_{j < ⌊n t⌋} ξ n j²` to `t` are not proved.

## Source

P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980),
Theorem 2.23: under the conditional Lindeberg condition and tightness of
`V²_{n k_n} = ∑_{i ≤ k_n} E[X_{ni}² | 𝓕_{n,i-1}]`,
`max_{i ≤ k_n} |U²_{ni} - V²_{ni}| → 0` in probability, where `U²_{ni} = ∑_{j ≤ i} X_{nj}²`.
(Statement paraphrased; theorem number from the task spec, not checked against the text.)
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

variable {Ω : Type*}

/-! ### Auxiliary bounds -/

/-- Markov's inequality in the form used below: for an a.e. nonnegative integrable `f` and
`δ > 0`, `μ {δ ≤ f} ≤ ofReal (∫ f / δ)`. -/
lemma measure_ge_le_ofReal_integral_div {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hf : Integrable f μ) {δ : ℝ}
    (hδ : 0 < δ) : μ {ω | δ ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂μ) / δ) := by
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hδ, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hf0 hf δ

/-- The predictably stopped conditional variances stay below the stopping level: if every
`c j` is nonnegative, then `∑_{j < K} 𝟙{∑_{i ≤ j} c i ≤ C} c j ≤ C`. -/
private lemma sum_ite_le (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) {C : ℝ} (hC : 0 ≤ C) (K : ℕ) :
    ∑ j ∈ Finset.range K, (if ∑ i ∈ Finset.range (j + 1), c i ≤ C then c j else 0) ≤ C := by
  classical
  set J := (Finset.range K).filter fun j => ∑ i ∈ Finset.range (j + 1), c i ≤ C with hJ
  rw [← Finset.sum_filter]
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · rw [← hJ, hJe, Finset.sum_empty]; exact hC
  · set j₀ := J.max' hJne
    have hj₀ : j₀ ∈ J := J.max'_mem hJne
    calc ∑ j ∈ J, c j ≤ ∑ i ∈ Finset.range (j₀ + 1), c i := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hc j
          exact Finset.mem_range.2 (Nat.lt_succ_of_le (J.le_max' j hj))
      _ ≤ C := (Finset.mem_filter.1 hj₀).2

/-- The square of a finite maximum of absolute values is bounded by the sum of the squares. -/
private lemma sup'_abs_sq_le (g : ℕ → ℝ) (K : ℕ) :
    ((Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => |g k|) ^ 2 ≤
      ∑ k ∈ Finset.range (K + 1), g k ^ 2 := by
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    fun k => |g k|
  rw [hkeq, sq_abs]
  exact Finset.single_le_sum (f := fun k => g k ^ 2) (fun k _ => sq_nonneg (g k)) hk

/-! ### One row: truncation, predictable stopping, and Doob's inequality -/

/-- **One-row estimate behind Hall–Heyde Theorem 2.23.** Let `x 0, x 1, …` be square-integrable
with `x i` measurable for `F (i+1)`, write `c j = E[x j² | F j]` and let
`D = max_{k ≤ K} |∑_{j < k} (x j² - c j)|`. For `ε, δ > 0` and `C ≥ 0`,
`P(D ≥ 3δ) ≤ P(∑_{j<K} c j > C) + 4 ε² C / δ² + 2 L / δ`, where
`L = ∑_{j<K} E[x j² 𝟙{|x j| > ε}]` is the Lindeberg sum.

Proof: split `x j² = a j + b j` at `|x j| = ε`. The centered truncated squares, stopped
predictably once `∑_{i ≤ j} c i` exceeds `C`, are bounded martingale differences whose
predictable quadratic variation has mean at most `ε² C`; Doob's `L²` maximal inequality
(`Martingale.doob_sq_maximal_ineq_predictableQuadraticVariation`) and Chebyshev bound their
running maximum. The large parts `b j` and their conditional expectations both have mean `L`
(Markov). Off `{∑_{j<K} c j > C}` the stopping never triggers before `K`. -/
private lemma measure_three_mul_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℕ m} {x : ℕ → Ω → ℝ}
    (hx : ∀ i, StronglyMeasurable[F (i + 1)] (x i)) (hL2 : ∀ i, MemLp (x i) 2 μ)
    {ε δ C : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hC : 0 ≤ C) (K : ℕ) :
    μ {ω | 3 * δ ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k =>
        |∑ j ∈ Finset.range k, (x j ω ^ 2 - (μ[fun ω => x j ω ^ 2 | F j]) ω)|} ≤
      μ {ω | C < ∑ j ∈ Finset.range K, (μ[fun ω => x j ω ^ 2 | F j]) ω} +
        ENNReal.ofReal (4 * (ε ^ 2 * C) / δ ^ 2) +
        2 * ENNReal.ofReal ((∑ j ∈ Finset.range K,
          ∫ ω, x j ω ^ 2 * Set.indicator {ω' | ε < |x j ω'|} 1 ω ∂μ) / δ) := by
  set c : ℕ → Ω → ℝ := fun j => μ[fun ω => x j ω ^ 2 | F j] with hc_def
  set S : ℕ → Set Ω := fun j => {ω | ε < |x j ω|} with hS_def
  set b : ℕ → Ω → ℝ := fun j => (S j).indicator fun ω => x j ω ^ 2 with hb_def
  set a : ℕ → Ω → ℝ := fun j => (S j)ᶜ.indicator fun ω => x j ω ^ 2 with ha_def
  set A : ℕ → Set Ω := fun j => {ω | ∑ i ∈ Finset.range (j + 1), c i ω ≤ C} with hA_def
  set Z : ℕ → Ω → ℝ := fun j => (A j).indicator (a j) with hZ_def
  set y : ℕ → Ω → ℝ := fun j => Z j - μ[Z j | F j] with hy_def
  set M : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, y j ω with hM_def
  -- measurability
  have hSm : ∀ j, MeasurableSet[F (j + 1)] (S j) := fun j =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hx j).measurable)
  have hSm' : ∀ j, MeasurableSet (S j) := fun j => F.le _ _ (hSm j)
  have hsq : ∀ j, StronglyMeasurable[F (j + 1)] (fun ω => x j ω ^ 2) := fun j => (hx j).pow 2
  have ha_sm : ∀ j, StronglyMeasurable[F (j + 1)] (a j) := fun j =>
    (hsq j).indicator (hSm j).compl
  have hAm : ∀ j, MeasurableSet[F j] (A j) := by
    intro j
    have : StronglyMeasurable[F j] (fun ω => ∑ i ∈ Finset.range (j + 1), c i ω) :=
      Finset.stronglyMeasurable_fun_sum _ fun i hi => stronglyMeasurable_condExp.mono
        (F.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
    exact measurableSet_le this.measurable measurable_const
  have hAm' : ∀ j, MeasurableSet (A j) := fun j => F.le _ _ (hAm j)
  have hZ_sm : ∀ j, StronglyMeasurable[F (j + 1)] (Z j) := fun j =>
    (ha_sm j).indicator (F.mono (Nat.le_succ j) _ (hAm j))
  have hy_sm : ∀ j, StronglyMeasurable[F (j + 1)] (y j) := fun j =>
    (hZ_sm j).sub (stronglyMeasurable_condExp.mono (F.mono (Nat.le_succ j)))
  -- integrability and bounds
  have hsq_int : ∀ j, Integrable (fun ω => x j ω ^ 2) μ := fun j => (hL2 j).integrable_sq
  have hb_int : ∀ j, Integrable (b j) μ := fun j => (hsq_int j).indicator (hSm' j)
  have ha_int : ∀ j, Integrable (a j) μ := fun j => (hsq_int j).indicator (hSm' j).compl
  have hb_nn : ∀ j ω, 0 ≤ b j ω := fun j ω =>
    Set.indicator_nonneg (fun ω _ => sq_nonneg (x j ω)) ω
  have ha_bd : ∀ j ω, 0 ≤ a j ω ∧ a j ω ≤ ε ^ 2 ∧ a j ω ≤ x j ω ^ 2 := by
    intro j ω
    by_cases h : ω ∈ S j
    · simp [ha_def, h, sq_nonneg]
    · have h' : |x j ω| ≤ ε := not_lt.1 h
      have : x j ω ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h' 2
      simp only [ha_def, Set.indicator_of_mem (Set.mem_compl h)]
      exact ⟨sq_nonneg _, this, le_rfl⟩
  have hZL2 : ∀ j, MemLp (Z j) 2 μ := by
    intro j
    refine MemLp.of_bound ((hZ_sm j).mono (F.le _)).aestronglyMeasurable (ε ^ 2)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ A j
    · simp only [hZ_def, Set.indicator_of_mem hω]
      rw [abs_of_nonneg (ha_bd j ω).1]; exact (ha_bd j ω).2.1
    · simp only [hZ_def, Set.indicator_of_notMem hω, abs_zero]; positivity
  have hyL2 : ∀ j, MemLp (y j) 2 μ := fun j => (hZL2 j).sub ((hZL2 j).condExp one_le_two)
  -- the stopped truncated sums form a square-integrable martingale started at `0`
  have hy_ce : ∀ j, μ[y j | F j] =ᵐ[μ] 0 := by
    intro j
    have hZint : Integrable (Z j) μ := (hZL2 j).integrable one_le_two
    filter_upwards [condExp_sub hZint (integrable_condExp (m := F j) (f := Z j)) (F j)]
      with ω hω
    rw [hω, Pi.sub_apply, condExp_of_stronglyMeasurable (F.le j) stronglyMeasurable_condExp
      integrable_condExp, sub_self, Pi.zero_apply]
  have hM_sm : ∀ k, StronglyMeasurable[F k] (M k) := fun k =>
    Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      (hy_sm j).mono (F.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))
  have hML2 : ∀ k, MemLp (M k) 2 μ := fun k => memLp_finsetSum _ fun j _ => hyL2 j
  have hMinc : ∀ k, M (k + 1) - M k = y k := fun k => by
    funext ω; simp [hM_def, Finset.sum_range_succ]
  have hmart : Martingale M F μ := by
    refine martingale_of_condExp_sub_eq_zero_nat hM_sm (fun k => (hML2 k).integrable one_le_two)
      fun k => ?_
    rw [hMinc]; exact hy_ce k
  have hdoob := hmart.doob_sq_maximal_ineq_predictableQuadraticVariation hML2
    (Eventually.of_forall fun ω => by simp [hM_def]) K
  have hPQV : ∫ ω, predictableQuadraticVariation μ F M K ω ∂μ =
      ∑ k ∈ Finset.range K, ∫ ω, y k ω ^ 2 ∂μ := by
    simp only [predictableQuadraticVariation]
    rw [integral_finsetSum _ fun k _ => integrable_condExp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_condExp (F.le k)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Pi.sub_apply (M (k + 1)) (M k), hMinc]
  -- variance bound for one stopped truncated increment
  have hy2 : ∀ j, ∫ ω, y j ω ^ 2 ∂μ ≤ ε ^ 2 * ∫ ω, (A j).indicator (c j) ω ∂μ := by
    intro j
    calc ∫ ω, y j ω ^ 2 ∂μ = ∫ ω, Var[Z j; μ | F j] ω ∂μ := by
          rw [condVar, integral_condExp (F.le j)]; rfl
      _ ≤ ∫ ω, (μ[Z j ^ 2 | F j]) ω ∂μ :=
          integral_mono_ae integrable_condVar integrable_condExp
            (condVar_ae_le_condExp_sq (F.le j) (hZL2 j))
      _ = ∫ ω, Z j ω ^ 2 ∂μ := by rw [integral_condExp (F.le j)]; rfl
      _ ≤ ∫ ω, ε ^ 2 * (A j).indicator (fun ω => x j ω ^ 2) ω ∂μ := by
          refine integral_mono (hZL2 j).integrable_sq
            (((hsq_int j).indicator (hAm' j)).const_mul _) fun ω => ?_
          by_cases hω : ω ∈ A j
          · simp only [hZ_def, Set.indicator_of_mem hω]
            obtain ⟨h0, h1, h2⟩ := ha_bd j ω
            nlinarith
          · simp [hZ_def, Set.indicator_of_notMem hω]
      _ = ε ^ 2 * ∫ ω, (A j).indicator (c j) ω ∂μ := by
          rw [integral_const_mul, integral_indicator (hAm' j), integral_indicator (hAm' j),
            hc_def, setIntegral_condExp (F.le j) (hsq_int j) (hAm j)]
  have hc_nn : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ c j ω := ae_all_iff.2 fun j =>
    condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg (x j ω))
  have hEsum : ∑ j ∈ Finset.range K, ∫ ω, (A j).indicator (c j) ω ∂μ ≤ C := by
    rw [← integral_finsetSum _ fun j _ => integrable_condExp.indicator (hAm' j)]
    calc ∫ ω, ∑ j ∈ Finset.range K, (A j).indicator (c j) ω ∂μ ≤ ∫ _ω, C ∂μ := by
          refine integral_mono_ae
            (integrable_finsetSum _ fun j _ => integrable_condExp.indicator (hAm' j))
            (integrable_const C) ?_
          filter_upwards [hc_nn] with ω hω
          simpa only [hA_def, Set.indicator_apply, Set.mem_ofPred_eq] using
            sum_ite_le (fun j => c j ω) hω hC K
      _ = C := by simp
  -- the running maximum of the martingale
  set maxM : Ω → ℝ := fun ω =>
    (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω| with hmaxM_def
  have hmaxM_nn : ∀ ω, 0 ≤ maxM ω := fun ω =>
    (abs_nonneg (M 0 ω)).trans (Finset.le_sup' (fun k => |M k ω|) (by simp))
  have hmaxM_int : Integrable (fun ω => maxM ω ^ 2) μ := by
    refine Integrable.mono' (g := fun ω => ∑ k ∈ Finset.range (K + 1), M k ω ^ 2)
      (integrable_finsetSum _ fun k _ => (hML2 k).integrable_sq) ?_
      (Eventually.of_forall fun ω => ?_)
    · exact ((Finset.measurable_range_sup'' fun k _ =>
        continuous_abs.measurable.comp ((hM_sm k).mono (F.le k)).measurable).pow_const
          2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sup'_abs_sq_le (fun k => M k ω) K
  have hmaxM_L2 : ∫ ω, maxM ω ^ 2 ∂μ ≤ 4 * (ε ^ 2 * C) := by
    refine hdoob.trans ?_
    rw [hPQV]
    gcongr
    calc ∑ k ∈ Finset.range K, ∫ ω, y k ω ^ 2 ∂μ
        ≤ ∑ k ∈ Finset.range K, ε ^ 2 * ∫ ω, (A k).indicator (c k) ω ∂μ :=
          Finset.sum_le_sum fun k _ => hy2 k
      _ ≤ ε ^ 2 * C := by rw [← Finset.mul_sum]; gcongr
  have hPM : μ {ω | δ ≤ maxM ω} ≤ ENNReal.ofReal (4 * (ε ^ 2 * C) / δ ^ 2) := by
    calc μ {ω | δ ≤ maxM ω} ≤ μ {ω | δ ^ 2 ≤ maxM ω ^ 2} :=
          measure_mono fun ω hω => pow_le_pow_left₀ hδ.le hω 2
      _ ≤ ENNReal.ofReal ((∫ ω, maxM ω ^ 2 ∂μ) / δ ^ 2) :=
          measure_ge_le_ofReal_integral_div (Eventually.of_forall fun ω => sq_nonneg _)
            hmaxM_int (by positivity)
      _ ≤ ENNReal.ofReal (4 * (ε ^ 2 * C) / δ ^ 2) := by gcongr
  -- the large parts: Markov
  set L := ∑ j ∈ Finset.range K, ∫ ω, x j ω ^ 2 * Set.indicator {ω' | ε < |x j ω'|} 1 ω ∂μ
    with hL_def
  have hLb : L = ∑ j ∈ Finset.range K, ∫ ω, b j ω ∂μ := by
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae
      (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ S j
    · simp only [hb_def, Set.indicator_of_mem h]
      rw [Set.indicator_of_mem (show ω ∈ {ω' | ε < |x j ω'|} from h), Pi.one_apply, mul_one]
    · simp only [hb_def, Set.indicator_of_notMem h]
      rw [Set.indicator_of_notMem (show ω ∉ {ω' | ε < |x j ω'|} from h), mul_zero]
  have hPB : μ {ω | δ ≤ ∑ j ∈ Finset.range K, b j ω} ≤ ENNReal.ofReal (L / δ) := by
    refine (measure_ge_le_ofReal_integral_div
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun j _ => hb_nn j ω)
      (integrable_finsetSum _ fun j _ => hb_int j) hδ).trans (le_of_eq ?_)
    rw [integral_finsetSum _ fun j _ => hb_int j, hLb]
  have hPB' : μ {ω | δ ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω} ≤
      ENNReal.ofReal (L / δ) := by
    refine (measure_ge_le_ofReal_integral_div ?_
      (integrable_finsetSum _ fun j _ => integrable_condExp) hδ).trans (le_of_eq ?_)
    · have : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ (μ[b j | F j]) ω := ae_all_iff.2 fun j =>
        condExp_nonneg (Eventually.of_forall fun ω => hb_nn j ω)
      filter_upwards [this] with ω hω
      exact Finset.sum_nonneg fun j _ => hω j
    · rw [integral_finsetSum _ fun j _ => integrable_condExp, hLb]
      congr 2
      exact Finset.sum_congr rfl fun j _ => integral_condExp (F.le j)
  -- pointwise decomposition off the stopping event
  have hab : ∀ j, (fun ω => x j ω ^ 2) = a j + b j := fun j =>
    (Set.indicator_compl_add_self (S j) _).symm
  have hgood : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ c j ω ∧ 0 ≤ (μ[b j | F j]) ω ∧
      c j ω = (μ[a j | F j]) ω + (μ[b j | F j]) ω ∧
      (μ[Z j | F j]) ω = (A j).indicator (μ[a j | F j]) ω := by
    refine ae_all_iff.2 fun j => ?_
    have hdec : c j =ᵐ[μ] μ[a j | F j] + μ[b j | F j] := by
      simp only [hc_def]
      rw [hab j]
      exact condExp_add (ha_int j) (hb_int j) _
    filter_upwards [condExp_nonneg (m := F j) (μ := μ)
        (Eventually.of_forall fun ω => sq_nonneg (x j ω)),
      condExp_nonneg (m := F j) (μ := μ) (Eventually.of_forall fun ω => hb_nn j ω), hdec,
      condExp_indicator (m := F j) (ha_int j) (hAm j)] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hsub : {ω | 3 * δ ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k =>
        |∑ j ∈ Finset.range k, (x j ω ^ 2 - c j ω)|} ≤ᵐ[μ]
      (({ω | C < ∑ j ∈ Finset.range K, c j ω} ∪ {ω | δ ≤ maxM ω}) ∪
        {ω | δ ≤ ∑ j ∈ Finset.range K, b j ω}) ∪
        {ω | δ ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω} := by
    filter_upwards [hgood] with ω hω hT
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_le] at hnot hT
    obtain ⟨⟨⟨hG, hMω⟩, hBω⟩, hB'ω⟩ := hnot
    have hterm : ∀ j < K, x j ω ^ 2 - c j ω = y j ω + b j ω - (μ[b j | F j]) ω := by
      intro j hj
      have hAj : ω ∈ A j := by
        change ∑ i ∈ Finset.range (j + 1), c i ω ≤ C
        refine le_trans ?_ hG
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hj)
          fun i _ _ => (hω i).1
      have hy : y j ω = a j ω - (μ[a j | F j]) ω := by
        change Z j ω - (μ[Z j | F j]) ω = _
        rw [(hω j).2.2.2, Set.indicator_of_mem hAj]
        simp only [hZ_def, Set.indicator_of_mem hAj]
      have hx2 : x j ω ^ 2 = a j ω + b j ω := congrFun (hab j) ω
      rw [hy, hx2, (hω j).2.2.1]
      ring
    have hD : ∀ k ∈ Finset.range (K + 1), |∑ j ∈ Finset.range k, (x j ω ^ 2 - c j ω)| ≤
        maxM ω + ∑ j ∈ Finset.range K, b j ω + ∑ j ∈ Finset.range K, (μ[b j | F j]) ω := by
      intro k hk
      have hkK : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      rw [Finset.sum_congr rfl fun j hj => hterm j
        (lt_of_lt_of_le (Finset.mem_range.1 hj) hkK), Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      have hMk : |M k ω| ≤ maxM ω := Finset.le_sup' (fun k => |M k ω|) hk
      have hb1 : 0 ≤ ∑ j ∈ Finset.range k, b j ω := Finset.sum_nonneg fun j _ => hb_nn j ω
      have hb2 : ∑ j ∈ Finset.range k, b j ω ≤ ∑ j ∈ Finset.range K, b j ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkK)
          fun j _ _ => hb_nn j ω
      have hb3 : 0 ≤ ∑ j ∈ Finset.range k, (μ[b j | F j]) ω :=
        Finset.sum_nonneg fun j _ => (hω j).2.1
      have hb4 : ∑ j ∈ Finset.range k, (μ[b j | F j]) ω ≤
          ∑ j ∈ Finset.range K, (μ[b j | F j]) ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkK)
          fun j _ _ => (hω j).2.1
      have hMk' : ∑ j ∈ Finset.range k, y j ω = M k ω := rfl
      rw [hMk']
      refine abs_le.2 ⟨?_, ?_⟩
      · linarith [neg_abs_le (M k ω)]
      · linarith [le_abs_self (M k ω)]
    have := Finset.sup'_le Finset.nonempty_range_add_one _ hD
    linarith
  calc _ ≤ μ ((({ω | C < ∑ j ∈ Finset.range K, c j ω} ∪ {ω | δ ≤ maxM ω}) ∪
        {ω | δ ≤ ∑ j ∈ Finset.range K, b j ω}) ∪
        {ω | δ ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω}) := measure_mono_ae hsub
    _ ≤ μ {ω | C < ∑ j ∈ Finset.range K, c j ω} + μ {ω | δ ≤ maxM ω} +
        μ {ω | δ ≤ ∑ j ∈ Finset.range K, b j ω} +
        μ {ω | δ ≤ ∑ j ∈ Finset.range K, (μ[b j | F j]) ω} :=
      (measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
        (add_le_add_left (measure_union_le _ _) _)) _)
    _ ≤ μ {ω | C < ∑ j ∈ Finset.range K, c j ω} +
        ENNReal.ofReal (4 * (ε ^ 2 * C) / δ ^ 2) + ENNReal.ofReal (L / δ) +
        ENNReal.ofReal (L / δ) := by gcongr
    _ = _ := by rw [two_mul]; ring

/-! ### Realized versus predictable quadratic variation -/

/-- **Hall–Heyde, Theorem 2.23 (realized and predictable quadratic variation agree).**
Let row `n` of `ξ` be square-integrable, with `ξ n i` measurable for `𝓕 n (i+1)`, satisfying
the Lindeberg condition `LindebergConditionTriangular ξ μ`, and let `k n ≤ n`. If the
predictable quadratic variations `V n = ∑_{j < k n} E[ξ n j² | 𝓕 n j]` are bounded in
probability, then
`max_{i ≤ k n} |∑_{j < i} ξ n j² - ∑_{j < i} E[ξ n j² | 𝓕 n j]| → 0` in probability.

The martingale property `E[ξ n i | 𝓕 n i] = 0` is not needed. Hall–Heyde assume the conditional
Lindeberg condition; the unconditional one used here (as in T82) implies it.

Source: P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press
(1980), Theorem 2.23 (statement paraphrased; theorem number from the task spec, not checked
against the text). -/
theorem tendstoInMeasure_sup_abs_sum_sq_sub_condExp {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hLind : LindebergConditionTriangular ξ μ) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n)
    (htight : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ n in atTop,
      μ {ω | C < ∑ j ∈ Finset.range (k n), (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω} ≤
        ENNReal.ofReal η) :
    TendstoInMeasure μ
      (fun n ω => (Finset.range (k n + 1)).sup' Finset.nonempty_range_add_one fun i =>
        |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro δ₀ hδ₀
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨η, hη, hηe⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ e := by
    by_cases htop : e = ⊤
    · exact ⟨1, one_pos, by simp [htop]⟩
    · exact ⟨e.toReal, ENNReal.toReal_pos he.ne' htop, (ENNReal.ofReal_toReal htop).le⟩
  set δ := δ₀ / 3 with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨C₀, hC₀⟩ := htight (η / 4) (by positivity)
  set C := max C₀ 0 with hC_def
  have hC : 0 ≤ C := le_max_right _ _
  set ε := δ * Real.sqrt (η / (16 * (C + 1))) with hε_def
  have hε : 0 < ε := mul_pos hδ (Real.sqrt_pos.2 (by positivity))
  have hεC : 4 * (ε ^ 2 * C) / δ ^ 2 ≤ η / 4 := by
    have hsq : ε ^ 2 = δ ^ 2 * (η / (16 * (C + 1))) := by
      rw [hε_def, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsq, div_le_iff₀ (by positivity)]
    have hC1 : C / (C + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have : 4 * (δ ^ 2 * (η / (16 * (C + 1))) * C) = δ ^ 2 * (η / 4) * (C / (C + 1)) := by
      field_simp; ring
    rw [this]
    have := mul_le_of_le_one_right (show 0 ≤ δ ^ 2 * (η / 4) by positivity) hC1
    linarith
  have hLnn : ∀ n j, 0 ≤ ∫ ω, ξ n j ω ^ 2 * Set.indicator {ω' | ε < |ξ n j ω'|} 1 ω ∂μ :=
    fun n j => integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (Set.indicator_nonneg
      (fun _ _ => zero_le_one) ω)
  filter_upwards [hC₀, (hLind ε hε).eventually (gt_mem_nhds (show (0 : ℝ) < δ * η / 8 by
    positivity))] with n hn hLn
  set D : Ω → ℝ := fun ω => (Finset.range (k n + 1)).sup' Finset.nonempty_range_add_one
    fun i => |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|
    with hD_def
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω => (abs_nonneg _).trans
    (Finset.le_sup' (fun i => |∑ j ∈ Finset.range i,
      (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|) (b := 0) (by simp))
  have hrow := measure_three_mul_le (μ := μ) (F := 𝓕 n) (x := ξ n) (hξ n) (hL2 n) hε hδ hC
    (k n)
  set L := ∑ j ∈ Finset.range (k n),
    ∫ ω, ξ n j ω ^ 2 * Set.indicator {ω' | ε < |ξ n j ω'|} 1 ω ∂μ with hL_def
  have hLle : L / δ ≤ η / 8 := by
    rw [div_le_iff₀ hδ]
    have : L ≤ ∑ j ∈ Finset.range n,
        ∫ ω, ξ n j ω ^ 2 * Set.indicator {ω' | ε < |ξ n j ω'|} 1 ω ∂μ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (hk n))
        fun j _ _ => hLnn n j
    linarith
  calc μ {ω | δ₀ ≤ ‖D ω - 0‖} ≤ μ {ω | 3 * δ ≤ D ω} := measure_mono fun ω hω => by
        simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hD0 ω)] at hω
        change 3 * δ ≤ D ω
        rw [hδ_def]; linarith
    _ ≤ _ := hrow
    _ ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + 2 * ENNReal.ofReal (η / 8) := by
        gcongr
        exact (measure_mono fun ω (hω : C < _) => (show C₀ < _ from
          lt_of_le_of_lt (le_max_left _ _) hω)).trans hn
    _ = ENNReal.ofReal (3 * η / 4) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ e := hηe

/-- Convergence in probability to a constant gives boundedness in probability, in the form of
the hypothesis `htight` of `tendstoInMeasure_sup_abs_sum_sq_sub_condExp`. -/
lemma exists_eventually_measure_lt_le {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {t : ℝ} (h : TendstoInMeasure μ f atTop fun _ => t) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ᶠ n in atTop, μ {ω | C < f n ω} ≤ ENNReal.ofReal η := by
  refine ⟨t + 1, ?_⟩
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (tendstoInMeasure_iff_norm.1 h 1 one_pos)
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)] with n hn
  refine (measure_mono fun ω (hω : t + 1 < f n ω) => ?_).trans hn
  change 1 ≤ ‖f n ω - t‖
  rw [Real.norm_eq_abs]
  exact le_trans (by linarith) (le_abs_self _)

/-- `⌊n t⌋ ≤ n` for `t ≤ 1`. -/
private lemma floor_mul_le_self (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ⌊(n : ℝ) * t⌋₊ ≤ n :=
  Nat.floor_le_of_le (by nlinarith [ht.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- **Hall–Heyde Theorem 2.23 under T82's hypotheses.** For the martingale-difference arrays of
`tendstoInDistribution_arrayStepProcess` (`MartingaleTightness`, roadmap task T82): if row `n`
of `ξ` is square-integrable with `ξ n i` measurable for `𝓕 n (i+1)`, the predictable quadratic
variation `∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j]` tends to `t` in probability for every
`t ∈ [0,1]`, and the Lindeberg condition holds, then the realized and predictable quadratic
variations are uniformly close along the whole row:
`max_{i ≤ n} |∑_{j < i} ξ n j² - ∑_{j < i} E[ξ n j² | 𝓕 n j]| → 0` in probability.

Only `hQV` at `t = 1` is used. T82's martingale hypothesis `hmds` is not needed. -/
theorem tendstoInMeasure_sup_abs_sum_sq_sub_condExp_of_qv {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ) :
    TendstoInMeasure μ
      (fun n ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun i =>
        |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|)
      atTop (fun _ => 0) := by
  have h1 := hQV 1 ⟨zero_le_one, le_rfl⟩
  simp only [mul_one, Nat.floor_natCast] at h1
  exact tendstoInMeasure_sup_abs_sum_sq_sub_condExp hξ hL2 hLind id (fun _ => le_rfl)
    (exists_eventually_measure_lt_le h1)

/-- **Realized quadratic variation from predictable quadratic variation** (Hall–Heyde,
Theorem 2.23, for T82's arrays). Under the hypotheses of T82's functional CLT
`tendstoInDistribution_arrayStepProcess` (square integrability, `ξ n i` measurable for
`𝓕 n (i+1)`, predictable quadratic variation `→ t`, Lindeberg), the realized quadratic
variation converges to the same limit: for every `t ∈ [0,1]`,
`∑_{j < ⌊n t⌋} ξ n j² → t` in probability.

The conclusion is verbatim the hypothesis `hRQV` of
`tendstoInDistribution_fdd_martingaleDifference_floor` (`McLeishCLT`, roadmap task T81), so
T82's predictable-variation hypothesis discharges T81's realized-variation one. -/
theorem tendstoInMeasure_sum_sq_floor_of_qv {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ) :
    ∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n j ω ^ 2) atTop
      (fun _ => t.1) := by
  intro t
  have hV := hQV t.1 t.2
  have hD := tendstoInMeasure_sup_abs_sum_sq_sub_condExp hξ hL2 hLind
    (fun n => ⌊(n : ℝ) * t.1⌋₊) (fun n => floor_mul_le_self n t.2)
    (exists_eventually_measure_lt_le hV)
  rw [tendstoInMeasure_iff_norm] at hD hV ⊢
  intro ε hε
  have hlim := (hD (ε / 2) (half_pos hε)).add (hV (ε / 2) (half_pos hε))
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, sub_zero] at hω ⊢
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
  obtain ⟨h1, h2⟩ := hnot
  set K := ⌊(n : ℝ) * t.1⌋₊
  have hle : |∑ j ∈ Finset.range K, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)| ≤
      (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun i =>
        |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)| :=
    Finset.le_sup' (fun i => |∑ j ∈ Finset.range i,
      (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|) (by simp)
  rw [Finset.sum_sub_distrib] at hle
  have := abs_sub_le (∑ j ∈ Finset.range K, ξ n j ω ^ 2)
    (∑ j ∈ Finset.range K, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω) t.1
  linarith [le_abs_self ((Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun i =>
    |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)|)]

end

end MathlibExt.Probability.Martingale
