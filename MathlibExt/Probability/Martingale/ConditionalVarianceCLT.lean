/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.McLeishCLT
public import MathlibExt.Probability.DoobLpInequality

import MathlibExt.MeasureTheory.Function.ConditionalExpectation.BestPredictor

/-!
# Martingale CLT under the conditional-variance normalization

For a martingale difference array, convergence in probability of the **predictable** quadratic
variation `∑_k E[X n k² | F n k] → v` together with the conditional Lindeberg condition gives a
Gaussian limit `N(0, v)` for the row sums, and finite-dimensional convergence of the partial-sum
process. This is the conditional-variance form of the martingale CLT (Brown 1971; Hall–Heyde
Corollary 3.1), in contrast with McLeish's realized-quadratic-variation form proved in
`MathlibExt.Probability.Martingale.McLeishCLT`, which this file reduces to.

## Setting

Row `n` is a sequence `X n k` whose partial sums `∑_{j<k} X n j` form a martingale for a
filtration `F n`, with every `X n k` square integrable (a finite row of martingale differences
is extended by zeros); the row sum runs over `k < r n`. The predictable quadratic variation is
Mathlib-Ext's canonical `predictableQuadraticVariation` of the partial sums, which equals
`∑_{k<r n} E[X n k² | F n k]`. The conditional Lindeberg condition asks, for every `ε > 0`,
`∑_{k<r n} E[X n k² 1{ε < |X n k|} | F n k] → 0` in probability.

## Main results

* `tendstoInDistribution_martingale_condVar`: predictable quadratic variation `→ v` and the
  conditional Lindeberg condition imply `∑_{k<r n} X n k → N(0, v)` in distribution.
* `tendstoInDistribution_martingale_condVar_lindeberg`: the same under the unconditional
  Lindeberg condition `LindebergConditionTriangular` (rows of length `n`).
* `tendstoInDistribution_fdd_martingale_condVar`: finite-dimensional convergence of
  `S n s = ∑_{k < N n s} X n k` along a linearly ordered time axis, given predictable
  quadratic-variation convergence `→ A s` at every time and at the end of the row, to any process
  with centered Gaussian finite-dimensional laws of covariance `A (min s u)`.
* `tendstoInDistribution_fdd_martingaleDifference_floor_condVar`: the step-sum form
  `∑_{i < ⌊n t⌋} ξ n i` on `[0,1]`, under exactly the array hypotheses of the martingale
  functional CLT `tendstoInDistribution_arrayStepProcess` (roadmap task T82); its conclusion is
  T82's hypothesis `hT81`. It drops the realized-quadratic-variation hypothesis `hRQV` of
  `tendstoInDistribution_fdd_martingaleDifference_floor`.

## Proof

Cut each row predictably: keep increment `k` while `∑_{j ≤ k} E[X n j² | F n j] ≤ K`
(`K = v + 1`). The indicator of this event is `F n k`-measurable, so the cut increments are
still martingale differences, and the kept conditional variances add up to at most `K`, whence
`E[∑ X'²] ≤ K` (McLeish's maximal-moment condition (a)). Split `X'²` at level `ε` into big and
small jumps. The big jumps and their conditional means have expectation at most
`θ + K P(L n > θ)`, where `L n` is the conditional Lindeberg sum; this gives McLeish's (b)
and kills the big-jump part of realized minus predictable quadratic variation. The centred cut
small jumps `W - E[W | F n k]` form a martingale whose `L²` norm is at most `ε² K`
(`Martingale.integral_predictableQuadraticVariation` and `integral_sq_sub_condExp_le`), so
realized and kept predictable quadratic variation differ by `o_P(1)` (McLeish's (c)). On
`{∑_{k<r n} E[X n k² | F n k] ≤ K}`, whose probability tends to `1`, the cut changes nothing;
McLeish's theorem for the cut array and `tendstoInDistribution_of_tendstoInMeasure_sub`
conclude. The finite-dimensional statements run the same cut through
`tendstoInDistribution_fdd_martingale_mcLeish`.

## Scope and what is not proved

* The limit variance `v` (and `A s`) is a constant. Hall–Heyde's Corollary 3.1 also allows a
  random limit `η²` (with nested σ-fields), giving a variance mixture of normals; that is not
  proved here.
* Brown states the theorem for a single martingale normalized by `s_n² = E[∑ σ_k²]`; the
  triangular-array form here contains it by taking `X n k = Y k / s_n`.
* All increments are assumed square integrable (`∀ n k, MemLp (X n k) 2 μ`), including those
  past `r n`; finite rows are extended by zeros.
* `tendstoInDistribution_fdd_martingale_condVar` assumes the predictable quadratic variation of
  the whole row converges (`hpqvEnd`); this is automatic when the row ends at a time of the axis,
  as on `[0,1]` with `N n t = ⌊n t⌋` and `r n = n`. The hypothesis is a proof convenience, not
  part of the mathematics: the cut is built from the whole row because
  `tendstoInDistribution_fdd_martingale_mcLeish` asks for `N n s ≤ r n` and quadratic-variation
  convergence at every time `s`, not only at `s ∈ I`. Re-indexing the time axis to `I` and
  cutting at `N n (max I)` would remove it; that is not done here.
* The finite-dimensional theorems take the limit process `Z` as a hypothesis, specified by its
  Gaussian finite-dimensional laws; tightness and the functional CLT are T82's.

## Sources

B. M. Brown, *Martingale central limit theorems*, Ann. Math. Statist. 42 (1971), no. 1, 59–66
(the CLT and invariance principle under the conditional-variance normalization
`V_n² / s_n² → 1` and a Lindeberg condition).
P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980),
§3.2, Corollary 3.1 (the array form with `∑ E[X² 1{|X|>ε} | F] →_P 0` and
`∑ E[X² | F] →_P η²`).
D. L. McLeish, *Dependent central limit theorems and invariance principles*, Ann. Probab. 2
(1974), 620–628, Theorem (2.3), the realized form this file reduces to, and Corollary (3.8),
the conditional-variance form (as named in `MathlibExt.Probability.Martingale.McLeishCLT`).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### The predictable cut of one row -/

section Cut

variable (μ) in
/-- Conditional variance `E[X k² | F k]` of the `k`-th increment. -/
private def condSq (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  μ[fun ω => X k ω ^ 2 | F k]

variable (μ) in
/-- The predictable cut: keep increment `k` while `∑_{j ≤ k} E[X j² | F j] ≤ K`. -/
private def cutSet (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (K : ℝ) (k : ℕ) : Set Ω :=
  {ω | ∑ j ∈ range (k + 1), condSq μ F X j ω ≤ K}

variable (μ) in
/-- The cut increments `X' k = 1_{cutSet k} X k`. -/
private def cutX (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (K : ℝ) (k : ℕ) : Ω → ℝ :=
  (cutSet μ F X K k).indicator (X k)

variable {F : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

private lemma stronglyMeasurable_condSq (k : ℕ) : StronglyMeasurable[F k] (condSq μ F X k) :=
  stronglyMeasurable_condExp

private lemma measurableSet_cutSet (K : ℝ) (k : ℕ) : MeasurableSet[F k] (cutSet μ F X K k) := by
  have h : StronglyMeasurable[F k] fun ω => ∑ j ∈ range (k + 1), condSq μ F X j ω :=
    Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      (stronglyMeasurable_condSq j).mono (F.mono (Nat.lt_succ_iff.1 (mem_range.1 hj)))
  exact measurableSet_le h.measurable measurable_const

private lemma condSq_nonneg [IsFiniteMeasure μ] :
    ∀ᵐ ω ∂μ, ∀ k, 0 ≤ condSq μ F X k ω := by
  rw [ae_all_iff]
  intro k
  exact condExp_nonneg (ae_of_all _ fun ω => sq_nonneg _)

/-- The conditional variances kept by the cut add up to at most `K`. -/
private lemma sum_indicator_condSq_le {K : ℝ} (hK : 0 ≤ K) (m : ℕ) (ω : Ω) :
    ∑ k ∈ range m, (cutSet μ F X K k).indicator (condSq μ F X k) ω ≤ K := by
  have := sum_range_cut_le (fun k => condSq μ F X k ω) hK m
  convert this using 2 with k
  simp only [cutSet, Set.indicator_apply, Set.mem_ofPred_eq]

end Cut

/-! ### The cut row is a square-integrable martingale difference sequence -/

section CutMartingale

variable {F : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

private lemma cutX_sq (K : ℝ) (k : ℕ) (ω : Ω) :
    cutX μ F X K k ω ^ 2 = (cutSet μ F X K k).indicator (fun ω => X k ω ^ 2) ω := by
  by_cases h : ω ∈ cutSet μ F X K k <;> simp [cutX, h]

private lemma stronglyMeasurable_cutX (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (K : ℝ)
    (k : ℕ) : StronglyMeasurable[F (k + 1)] (cutX μ F X K k) :=
  (hX k).indicator (F.mono k.le_succ _ (measurableSet_cutSet K k))

private lemma memLp_cutX (hL2 : ∀ k, MemLp (X k) 2 μ) (K : ℝ) (k : ℕ) :
    MemLp (cutX μ F X K k) 2 μ :=
  (hL2 k).indicator
    (F.le k _ (measurableSet_cutSet K k)).nullMeasurableSet

private lemma condExp_cutX [IsFiniteMeasure μ] (hL2 : ∀ k, MemLp (X k) 2 μ)
    (hmds : ∀ k, μ[X k | F k] =ᵐ[μ] 0) (K : ℝ) (k : ℕ) : μ[cutX μ F X K k | F k] =ᵐ[μ] 0 := by
  have h := condExp_indicator (μ := μ) ((hL2 k).integrable one_le_two)
    (measurableSet_cutSet (μ := μ) (F := F) (X := X) K k)
  filter_upwards [h, hmds k] with ω hω h0
  rw [cutX, hω]
  by_cases hs : ω ∈ cutSet μ F X K k <;> simp [hs, h0]

private lemma martingale_cutX [IsFiniteMeasure μ] (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (hL2 : ∀ k, MemLp (X k) 2 μ) (hmds : ∀ k, μ[X k | F k] =ᵐ[μ] 0) (K : ℝ) :
    Martingale (fun j ω => ∑ k ∈ range j, cutX μ F X K k ω) F μ := by
  refine martingale_of_condExp_sub_eq_zero_nat (fun j => ?_) (fun j => ?_) fun j => ?_
  · exact Finset.stronglyMeasurable_fun_sum _ fun k hk =>
      (stronglyMeasurable_cutX hX K k).mono (F.mono (Nat.succ_le_of_lt (mem_range.1 hk)))
  · exact integrable_finsetSum _ fun k _ => (memLp_cutX hL2 K k).integrable one_le_two
  · have hd : ((fun ω => ∑ k ∈ range (j + 1), cutX μ F X K k ω) -
        fun ω => ∑ k ∈ range j, cutX μ F X K k ω) = cutX μ F X K j := by
      funext ω; simp [sum_range_succ]
    rw [hd]; exact condExp_cutX hL2 hmds K j

/-- On a set `A ∈ F k`, an integrable `h` and its conditional expectation have the same
integral. -/
private lemma integral_indicator_condExp [IsFiniteMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ)
    {k : ℕ} {A : Set Ω} (hA : MeasurableSet[F k] A) :
    ∫ ω, A.indicator (μ[h | F k]) ω ∂μ = ∫ ω, A.indicator h ω ∂μ := by
  rw [integral_indicator (F.le k _ hA), integral_indicator (F.le k _ hA),
    setIntegral_condExp (F.le k) hh hA]

/-- The cut row has `E[∑_{k<m} X' k²] ≤ K`. -/
private lemma integral_sum_sq_cutX_le [IsProbabilityMeasure μ] (hL2 : ∀ k, MemLp (X k) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    ∫ ω, ∑ k ∈ range m, cutX μ F X K k ω ^ 2 ∂μ ≤ K := by
  have hA := fun k => measurableSet_cutSet (μ := μ) (F := F) (X := X) K k
  have h1 : ∫ ω, ∑ k ∈ range m, cutX μ F X K k ω ^ 2 ∂μ =
      ∫ ω, ∑ k ∈ range m, (cutSet μ F X K k).indicator (condSq μ F X k) ω ∂μ := by
    have hi : ∀ k, Integrable ((cutSet μ F X K k).indicator (condSq μ F X k)) μ := fun k =>
      integrable_condExp.indicator (F.le k _ (hA k))
    simp_rw [cutX_sq]
    rw [integral_finsetSum _ fun k _ => (hL2 k).integrable_sq.indicator (F.le k _ (hA k)),
      integral_finsetSum _ fun k _ => hi k]
    exact sum_congr rfl fun k _ => (integral_indicator_condExp (hL2 k).integrable_sq (hA k)).symm
  rw [h1]
  calc _ ≤ ∫ _ω, K ∂μ := integral_mono_of_nonneg ?_ (integrable_const K)
          (ae_of_all _ fun ω => sum_indicator_condSq_le hK m ω)
    _ = K := by simp
  filter_upwards [condSq_nonneg (μ := μ) (F := F) (X := X)] with ω hω
  exact sum_nonneg fun k _ => Set.indicator_apply_nonneg fun _ => hω k

end CutMartingale

/-! ### Realized against predictable quadratic variation on the cut row -/

section Realized

variable {F : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The squared big jumps `X k² 1{ε < |X k|}`. -/
private def bigSq (X : ℕ → Ω → ℝ) (ε : ℝ) (k : ℕ) : Ω → ℝ :=
  {ω | ε < |X k ω|}.indicator fun ω => X k ω ^ 2

/-- The squared small jumps `X k² 1{|X k| ≤ ε}`. -/
private def smallSq (X : ℕ → Ω → ℝ) (ε : ℝ) (k : ℕ) : Ω → ℝ :=
  {ω | ε < |X k ω|}ᶜ.indicator fun ω => X k ω ^ 2

private lemma bigSq_add_smallSq (ε : ℝ) (k : ℕ) :
    bigSq X ε k + smallSq X ε k = fun ω => X k ω ^ 2 :=
  Set.indicator_self_add_compl _ _

private lemma measurableSet_bigSet (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (ε : ℝ)
    (k : ℕ) : MeasurableSet[F (k + 1)] {ω | ε < |X k ω|} :=
  measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX k).measurable)

private lemma integrable_bigSq (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (hL2 : ∀ k, MemLp (X k) 2 μ) (ε : ℝ) (k : ℕ) : Integrable (bigSq X ε k) μ :=
  (hL2 k).integrable_sq.indicator (F.le _ _ (measurableSet_bigSet hX ε k))

private lemma integrable_smallSq (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (hL2 : ∀ k, MemLp (X k) 2 μ) (ε : ℝ) (k : ℕ) : Integrable (smallSq X ε k) μ :=
  (hL2 k).integrable_sq.indicator (F.le _ _ (measurableSet_bigSet hX ε k)).compl

/-- The cut small-jump square `W k = 1_{cutSet k} X k² 1{|X k| ≤ ε}`. -/
private def cutSmall (μ : Measure Ω) (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (K ε : ℝ) (k : ℕ) :
    Ω → ℝ :=
  (cutSet μ F X K k).indicator (smallSq X ε k)

/-- Its centring `e k = W k - E[W k | F k]`, a martingale difference. -/
private def cutSmallCentred (μ : Measure Ω) (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (K ε : ℝ)
    (k : ℕ) : Ω → ℝ :=
  cutSmall μ F X K ε k - μ[cutSmall μ F X K ε k | F k]

private lemma stronglyMeasurable_cutSmall (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (K ε : ℝ) (k : ℕ) : StronglyMeasurable[F (k + 1)] (cutSmall μ F X K ε k) :=
  (((hX k).pow 2).indicator (measurableSet_bigSet hX ε k).compl).indicator
    (F.mono k.le_succ _ (measurableSet_cutSet K k))

private lemma abs_cutSmall_le (ε K : ℝ) (k : ℕ) (ω : Ω) :
    |cutSmall μ F X K ε k ω| ≤ ε ^ 2 := by
  simp only [cutSmall, smallSq]
  by_cases h1 : ω ∈ cutSet μ F X K k
  · by_cases h2 : ω ∈ {ω | ε < |X k ω|}ᶜ
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, abs_of_nonneg (sq_nonneg _),
        ← sq_abs]
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at h2
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, abs_zero]; positivity
  · rw [Set.indicator_of_notMem h1, abs_zero]; positivity

private lemma memLp_cutSmall [IsFiniteMeasure μ] (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (ε K : ℝ) (k : ℕ) : MemLp (cutSmall μ F X K ε k) 2 μ :=
  MemLp.of_bound ((stronglyMeasurable_cutSmall hX K ε k).mono (F.le _)).aestronglyMeasurable
    (ε ^ 2) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_cutSmall_le ε K k ω)

private lemma sq_cutSmall_le (ε K : ℝ) (k : ℕ) (ω : Ω) :
    cutSmall μ F X K ε k ω ^ 2 ≤ ε ^ 2 * cutX μ F X K k ω ^ 2 := by
  rw [cutX_sq]
  simp only [cutSmall, smallSq]
  by_cases h1 : ω ∈ cutSet μ F X K k
  · by_cases h2 : ω ∈ {ω | ε < |X k ω|}ᶜ
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem h1]
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at h2
      have : X k ω ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      nlinarith [sq_nonneg (X k ω)]
    · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_mem h1]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  · simp [Set.indicator_of_notMem h1]

/-- **The `L²` estimate.** The centred cut small jumps form a martingale with
`E[(∑_{k<m} e k)²] ≤ ε² K`. -/
private lemma integral_sq_sum_cutSmallCentred_le [IsProbabilityMeasure μ]
    (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (hL2 : ∀ k, MemLp (X k) 2 μ)
    (ε : ℝ) {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    ∫ ω, (∑ k ∈ range m, cutSmallCentred μ F X K ε k ω) ^ 2 ∂μ ≤ ε ^ 2 * K := by
  set f : ℕ → Ω → ℝ := fun j ω => ∑ k ∈ range j, cutSmallCentred μ F X K ε k ω with hf
  have hW := fun k => memLp_cutSmall (μ := μ) (F := F) (X := X) hX ε K k
  have he2 : ∀ k, MemLp (cutSmallCentred μ F X K ε k) 2 μ := fun k =>
    (hW k).sub ((hW k).condExp (by norm_num))
  have hesm : ∀ k, StronglyMeasurable[F (k + 1)] (cutSmallCentred μ F X K ε k) := fun k =>
    (stronglyMeasurable_cutSmall hX K ε k).sub (stronglyMeasurable_condExp.mono (F.mono k.le_succ))
  have hece : ∀ k, μ[cutSmallCentred μ F X K ε k | F k] =ᵐ[μ] 0 := by
    intro k
    have hWi := (hW k).integrable one_le_two
    refine (condExp_sub hWi integrable_condExp _).trans ?_
    rw [condExp_of_stronglyMeasurable (F.le k) stronglyMeasurable_condExp integrable_condExp]
    exact ae_of_all _ fun ω => by simp
  have hmart : Martingale f F μ := by
    refine martingale_of_condExp_sub_eq_zero_nat (fun j => ?_) (fun j => ?_) fun j => ?_
    · exact Finset.stronglyMeasurable_fun_sum _ fun k hk =>
        (hesm k).mono (F.mono (Nat.succ_le_of_lt (mem_range.1 hk)))
    · exact integrable_finsetSum _ fun k _ => (he2 k).integrable one_le_two
    · have hd : f (j + 1) - f j = cutSmallCentred μ F X K ε j := by
        funext ω; simp [hf, sum_range_succ]
      rw [hd]; exact hece j
  have hfL2 : ∀ j, MemLp (f j) 2 μ := fun j => memLp_finsetSum _ fun k _ => he2 k
  have hpqv := hmart.integral_predictableQuadraticVariation hfL2 m
  have hf0 : f 0 = 0 := by funext ω; simp [hf]
  simp only [hf0, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integral_zero, sub_zero] at hpqv
  change ∫ ω, f m ω ^ 2 ∂μ ≤ _
  rw [← hpqv]
  have hsum : ∫ ω, predictableQuadraticVariation μ F f m ω ∂μ =
      ∑ k ∈ range m, ∫ ω, cutSmallCentred μ F X K ε k ω ^ 2 ∂μ := by
    simp only [predictableQuadraticVariation]
    rw [integral_finsetSum _ fun k _ => integrable_condExp]
    refine sum_congr rfl fun k _ => ?_
    rw [integral_condExp (F.le k)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp [hf, sum_range_succ]
  rw [hsum]
  have hstep : ∀ k, ∫ ω, cutSmallCentred μ F X K ε k ω ^ 2 ∂μ ≤
      ∫ ω, ε ^ 2 * cutX μ F X K k ω ^ 2 ∂μ := by
    intro k
    have h := integral_sq_sub_condExp_le (F.le k) (hW k) (MemLp.zero (p := 2))
      (stronglyMeasurable_zero : StronglyMeasurable[F k] (0 : Ω → ℝ))
    simp only [Pi.zero_apply, sub_zero] at h
    refine h.trans (integral_mono (hW k).integrable_sq
      (((memLp_cutX hL2 K k).integrable_sq).const_mul _) fun ω => sq_cutSmall_le ε K k ω)
  calc _ ≤ ∑ k ∈ range m, ∫ ω, ε ^ 2 * cutX μ F X K k ω ^ 2 ∂μ := sum_le_sum fun k _ => hstep k
    _ = ε ^ 2 * ∫ ω, ∑ k ∈ range m, cutX μ F X K k ω ^ 2 ∂μ := by
        rw [integral_finsetSum _ fun k _ => (memLp_cutX hL2 K k).integrable_sq, mul_sum]
        exact sum_congr rfl fun k _ => integral_const_mul _ _
    _ ≤ ε ^ 2 * K := mul_le_mul_of_nonneg_left (integral_sum_sq_cutX_le hL2 hK m) (by positivity)

/-- The cut big-jump square `1_{cutSet k} X k² 1{ε < |X k|}`. -/
private def cutBig (μ : Measure Ω) (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ) (K ε : ℝ) (k : ℕ) :
    Ω → ℝ :=
  (cutSet μ F X K k).indicator (bigSq X ε k)

private lemma integrable_cutBig (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (hL2 : ∀ k, MemLp (X k) 2 μ) (K ε : ℝ) (k : ℕ) : Integrable (cutBig μ F X K ε k) μ :=
  (integrable_bigSq hX hL2 ε k).indicator (F.le k _ (measurableSet_cutSet K k))

private lemma cutBig_nonneg (K ε : ℝ) (k : ℕ) (ω : Ω) : 0 ≤ cutBig μ F X K ε k ω :=
  Set.indicator_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _) _

/-- **Decomposition.** Realized minus kept predictable quadratic variation of the cut row is
(big jumps) − (their conditional means) + (centred small jumps). -/
private lemma decomp_ae [IsFiniteMeasure μ] (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (hL2 : ∀ k, MemLp (X k) 2 μ) (K ε : ℝ) :
    ∀ᵐ ω ∂μ, ∀ m, ∑ k ∈ range m, cutX μ F X K k ω ^ 2 -
        ∑ k ∈ range m, (cutSet μ F X K k).indicator (condSq μ F X k) ω =
      ∑ k ∈ range m, cutBig μ F X K ε k ω -
        ∑ k ∈ range m, (cutSet μ F X K k).indicator (μ[bigSq X ε k | F k]) ω +
        ∑ k ∈ range m, cutSmallCentred μ F X K ε k ω := by
  have hk : ∀ k, ∀ᵐ ω ∂μ, cutX μ F X K k ω ^ 2 -
      (cutSet μ F X K k).indicator (condSq μ F X k) ω =
      cutBig μ F X K ε k ω - (cutSet μ F X K k).indicator (μ[bigSq X ε k | F k]) ω +
        cutSmallCentred μ F X K ε k ω := by
    intro k
    have hA := measurableSet_cutSet (μ := μ) (F := F) (X := X) K k
    have hadd : condSq μ F X k =ᵐ[μ] μ[bigSq X ε k | F k] + μ[smallSq X ε k | F k] := by
      rw [condSq, ← bigSq_add_smallSq ε k]
      exact condExp_add (integrable_bigSq hX hL2 ε k) (integrable_smallSq hX hL2 ε k) _
    have hind := condExp_indicator (μ := μ) (integrable_smallSq hX hL2 ε k) hA
    filter_upwards [hadd, hind] with ω h1 h2
    simp only [cutSmallCentred, cutSmall, Pi.sub_apply, cutBig]
    rw [h2, cutX_sq, ← bigSq_add_smallSq ε k]
    by_cases hω : ω ∈ cutSet μ F X K k
    · simp only [Set.indicator_of_mem hω, Pi.add_apply]
      rw [show condSq μ F X k ω = _ from h1, Pi.add_apply]; ring
    · simp [Set.indicator_of_notMem hω]
  rw [← ae_all_iff] at hk
  filter_upwards [hk] with ω hω m
  rw [← sum_sub_distrib, sum_congr rfl fun k _ => hω k, sum_add_distrib, sum_sub_distrib]

private lemma measureReal_mono_ae' [IsFiniteMeasure μ] {s t : Set Ω}
    (h : ∀ᵐ ω ∂μ, ω ∈ s → ω ∈ t) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (measure_ne_top μ t) (measure_mono_ae h)

/-- **The big-jump estimate.** For `m ≤ r` and `θ ≥ 0`,
`E[∑_{k<m} 1_{cutSet k} X k² 1{ε<|X k|}] ≤ θ + K P(θ < L)`, where
`L = ∑_{k<r} E[X k² 1{ε<|X k|} | F k]` is the conditional Lindeberg sum. -/
private lemma integral_sum_cutBig_le [IsProbabilityMeasure μ]
    (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (hL2 : ∀ k, MemLp (X k) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (ε : ℝ) {m r : ℕ} (hmr : m ≤ r) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ ω, ∑ k ∈ range m, cutBig μ F X K ε k ω ∂μ ≤
      θ + K * μ.real {ω | θ < ∑ k ∈ range r, μ[bigSq X ε k | F k] ω} := by
  have hA := fun k => measurableSet_cutSet (μ := μ) (F := F) (X := X) K k
  set L : Ω → ℝ := fun ω => ∑ k ∈ range r, μ[bigSq X ε k | F k] ω with hL
  have hLm : Measurable L := Finset.measurable_fun_sum _ fun k _ =>
    (stronglyMeasurable_condExp.mono (F.le k)).measurable
  have hS : MeasurableSet {ω | θ < L ω} := measurableSet_lt measurable_const hLm
  have hI : Integrable ({ω | θ < L ω}.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hS
  have hi : ∀ k, Integrable ((cutSet μ F X K k).indicator (μ[bigSq X ε k | F k])) μ := fun k =>
    integrable_condExp.indicator (F.le k _ (hA k))
  have h1 : ∫ ω, ∑ k ∈ range m, cutBig μ F X K ε k ω ∂μ =
      ∫ ω, ∑ k ∈ range m, (cutSet μ F X K k).indicator (μ[bigSq X ε k | F k]) ω ∂μ := by
    rw [integral_finsetSum _ fun k _ => integrable_cutBig hX hL2 K ε k,
      integral_finsetSum _ fun k _ => hi k]
    exact sum_congr rfl fun k _ =>
      (integral_indicator_condExp (integrable_bigSq hX hL2 ε k) (hA k)).symm
  rw [h1]
  have hnn : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ μ[bigSq X ε k | F k] ω := by
    rw [ae_all_iff]; intro k
    exact condExp_nonneg (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
  have hle : ∀ᵐ ω ∂μ, ∀ k, μ[bigSq X ε k | F k] ω ≤ condSq μ F X k ω := by
    rw [ae_all_iff]; intro k
    exact condExp_mono (integrable_bigSq hX hL2 ε k) (hL2 k).integrable_sq
      (ae_of_all _ fun ω => Set.indicator_le_self' (fun _ _ => sq_nonneg _) ω)
  calc _ ≤ ∫ ω, (θ + K * {ω | θ < L ω}.indicator 1 ω) ∂μ := by
        refine integral_mono_ae (integrable_finsetSum _ fun k _ => hi k)
          ((integrable_const θ).add (hI.const_mul K)) ?_
        filter_upwards [hnn, hle] with ω hω hω'
        have hT2K : ∑ k ∈ range m, (cutSet μ F X K k).indicator (μ[bigSq X ε k | F k]) ω ≤ K :=
          (sum_le_sum fun k _ => Set.indicator_le_indicator (hω' k)).trans
            (sum_indicator_condSq_le hK m ω)
        have hT2L : ∑ k ∈ range m, (cutSet μ F X K k).indicator (μ[bigSq X ε k | F k]) ω ≤ L ω :=
          (sum_le_sum fun k _ => Set.indicator_le_self' (fun _ _ => hω k) ω).trans
            (sum_le_sum_of_subset_of_nonneg (range_mono hmr) fun k _ _ => hω k)
        by_cases hθL : θ < L ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | θ < L ω} from hθL)]
          simp only [Pi.one_apply, mul_one]; linarith
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | θ < L ω} from hθL)]
          push Not at hθL; simp only [mul_zero, add_zero]; linarith
    _ = θ + K * μ.real {ω | θ < L ω} := by
        rw [integral_add (integrable_const θ) (hI.const_mul K), integral_const_mul,
          integral_indicator_one hS]
        simp

/-- **Probability bound for realized against kept predictable quadratic variation.** -/
private lemma measureReal_realized_sub_le [IsProbabilityMeasure μ]
    (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (hL2 : ∀ k, MemLp (X k) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (ε : ℝ) {m r : ℕ} (hmr : m ≤ r) {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 < η) :
    μ.real {ω | 3 * η ≤ |∑ k ∈ range m, cutX μ F X K k ω ^ 2 -
        ∑ k ∈ range m, (cutSet μ F X K k).indicator (condSq μ F X k) ω|} ≤
      2 * ((θ + K * μ.real {ω | θ < ∑ k ∈ range r, μ[bigSq X ε k | F k] ω}) / η) +
        ε ^ 2 * K / η ^ 2 := by
  set B := θ + K * μ.real {ω | θ < ∑ k ∈ range r, μ[bigSq X ε k | F k] ω} with hB
  set T1 : Ω → ℝ := fun ω => ∑ k ∈ range m, cutBig μ F X K ε k ω with hT1
  set T2 : Ω → ℝ := fun ω =>
    ∑ k ∈ range m, (cutSet μ F X K k).indicator (μ[bigSq X ε k | F k]) ω with hT2
  set T3 : Ω → ℝ := fun ω => ∑ k ∈ range m, cutSmallCentred μ F X K ε k ω with hT3
  have hA := fun k => measurableSet_cutSet (μ := μ) (F := F) (X := X) K k
  have hT1i : Integrable T1 μ := integrable_finsetSum _ fun k _ =>
    (integrable_bigSq hX hL2 ε k).indicator (F.le k _ (hA k))
  have hT2i : Integrable T2 μ := integrable_finsetSum _ fun k _ =>
    integrable_condExp.indicator (F.le k _ (hA k))
  have hT2nn : ∀ᵐ ω ∂μ, 0 ≤ T2 ω := by
    have hnn : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ μ[bigSq X ε k | F k] ω := by
      rw [ae_all_iff]; intro k
      exact condExp_nonneg (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
    filter_upwards [hnn] with ω hω
    exact sum_nonneg fun k _ => Set.indicator_apply_nonneg fun _ => hω k
  have hT1T2 : ∫ ω, T1 ω ∂μ = ∫ ω, T2 ω ∂μ := by
    simp only [hT1, hT2]
    rw [integral_finsetSum _ fun k _ => integrable_cutBig hX hL2 K ε k,
      integral_finsetSum _ fun k _ => integrable_condExp.indicator (F.le k _ (hA k))]
    exact sum_congr rfl fun k _ =>
      (integral_indicator_condExp (integrable_bigSq hX hL2 ε k) (hA k)).symm
  have hT1B : ∫ ω, T1 ω ∂μ ≤ B := integral_sum_cutBig_le hX hL2 hK ε hmr hθ
  have hT3L2 : MemLp T3 2 μ := memLp_finsetSum _ fun k _ =>
    (memLp_cutSmall hX ε K k).sub ((memLp_cutSmall hX ε K k).condExp (by norm_num))
  have hT3B : ∫ ω, T3 ω ^ 2 ∂μ ≤ ε ^ 2 * K := integral_sq_sum_cutSmallCentred_le hX hL2 ε hK m
  -- Markov for each piece
  have hM1 : μ.real {ω | η ≤ T1 ω} ≤ B / η := by
    rw [le_div_iff₀ hη, mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω =>
      sum_nonneg fun k _ => cutBig_nonneg K ε k ω) hT1i η).trans hT1B
  have hM2 : μ.real {ω | η ≤ T2 ω} ≤ B / η := by
    rw [le_div_iff₀ hη, mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg hT2nn hT2i η).trans (hT1T2 ▸ hT1B)
  have hM3 : μ.real {ω | η ≤ |T3 ω|} ≤ ε ^ 2 * K / η ^ 2 := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    have hsub : {ω | η ≤ |T3 ω|} ⊆ {ω | η ^ 2 ≤ T3 ω ^ 2} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [← sq_abs (T3 ω)]; exact pow_le_pow_left₀ hη.le hω 2
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
      ((mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
        hT3L2.integrable_sq _).trans hT3B)
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | 3 * η ≤ |∑ k ∈ range m, cutX μ F X K k ω ^ 2 -
      ∑ k ∈ range m, (cutSet μ F X K k).indicator (condSq μ F X k) ω|} →
      ω ∈ ({ω | η ≤ T1 ω} ∪ {ω | η ≤ T2 ω}) ∪ {ω | η ≤ |T3 ω|} := by
    filter_upwards [decomp_ae (μ := μ) (F := F) (X := X) hX hL2 K ε, hT2nn] with ω hω h2 hmem
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hmem ⊢
    rw [hω m] at hmem
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h1, h2'⟩, h3⟩ := hcon
    have h1' : 0 ≤ T1 ω := sum_nonneg fun k _ => cutBig_nonneg K ε k ω
    have := abs_add_le (T1 ω - T2 ω) (T3 ω)
    have := abs_sub (T1 ω) (T2 ω)
    rw [abs_of_nonneg h1', abs_of_nonneg h2] at this
    linarith
  calc _ ≤ μ.real (({ω | η ≤ T1 ω} ∪ {ω | η ≤ T2 ω}) ∪ {ω | η ≤ |T3 ω|}) :=
        measureReal_mono_ae' hsub
    _ ≤ μ.real {ω | η ≤ T1 ω} + μ.real {ω | η ≤ T2 ω} + μ.real {ω | η ≤ |T3 ω|} :=
        (measureReal_union_le _ _).trans (by gcongr; exact measureReal_union_le _ _)
    _ ≤ B / η + B / η + ε ^ 2 * K / η ^ 2 := by gcongr
    _ = _ := by ring

/-- **Probability bound for the maximal cut increment.** -/
private lemma measureReal_exists_cutX_gt_le [IsProbabilityMeasure μ]
    (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (hL2 : ∀ k, MemLp (X k) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) {m r : ℕ} (hmr : m ≤ r) {θ : ℝ} (hθ : 0 ≤ θ) :
    μ.real {ω | ∃ k ∈ range m, ε < |cutX μ F X K k ω|} ≤
      (θ + K * μ.real {ω | θ < ∑ k ∈ range r, μ[bigSq X ε k | F k] ω}) / ε ^ 2 := by
  have hA := fun k => measurableSet_cutSet (μ := μ) (F := F) (X := X) K k
  have hsub : {ω | ∃ k ∈ range m, ε < |cutX μ F X K k ω|} ⊆
      {ω | ε ^ 2 ≤ ∑ k ∈ range m, cutBig μ F X K ε k ω} := by
    intro ω hω
    obtain ⟨k, hk, hgt⟩ := hω
    simp only [Set.mem_ofPred_eq]
    have hin : ω ∈ cutSet μ F X K k := by
      by_contra h
      simp [cutX, Set.indicator_of_notMem h] at hgt; linarith
    rw [cutX, Set.indicator_of_mem hin] at hgt
    have hterm : cutBig μ F X K ε k ω = X k ω ^ 2 := by
      simp [cutBig, bigSq, Set.indicator_of_mem hin,
        Set.indicator_of_mem (show ω ∈ {ω | ε < |X k ω|} from hgt)]
    refine le_trans ?_ (single_le_sum (fun j _ => cutBig_nonneg K ε j ω) hk)
    rw [hterm, ← sq_abs (X k ω)]; exact pow_le_pow_left₀ hε.le hgt.le 2
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
    ((mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω =>
      sum_nonneg fun k _ => cutBig_nonneg K ε k ω) (integrable_finsetSum _ fun k _ =>
        (integrable_bigSq hX hL2 ε k).indicator (F.le k _ (hA k))) _).trans
      (integral_sum_cutBig_le hX hL2 hK ε hmr hθ))

end Realized

/-! ### Convergence in probability helpers -/

section InMeasure

private lemma tendsto_zero_of_forall_le {a : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, a n ≤ δ) : Tendsto a atTop (𝓝 0) :=
  tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun n => lt_of_lt_of_le hb (h0 n),
    fun b hb => (h (b / 2) (by linarith)).mono fun n hn => by linarith⟩

variable [IsFiniteMeasure μ]

/-- If `f n = g n` almost surely outside sets `B n` of vanishing probability, `f` inherits the
limit in probability of `g`. -/
private lemma tendstoInMeasure_of_ae_eq_off {E : Type*} [PseudoMetricSpace E]
    {f g : ℕ → Ω → E} {h : Ω → E} {B : ℕ → Set Ω}
    (hB : Tendsto (fun n => μ.real (B n)) atTop (𝓝 0))
    (heq : ∀ n, ∀ᵐ ω ∂μ, ω ∉ B n → f n ω = g n ω) (hg : TendstoInMeasure μ g atTop h) :
    TendstoInMeasure μ f atTop h := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hg ⊢
  intro ε hε
  have hsum := (hg ε hε).add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => measureReal_nonneg) fun n => (measureReal_mono_ae' ?_).trans
      (measureReal_union_le _ _)
  filter_upwards [heq n] with ω hω hmem
  by_cases hb : ω ∈ B n
  · exact Or.inr hb
  · left; simp only [Set.mem_ofPred_eq] at hmem ⊢; rwa [← hω hb]

private lemma tendstoInMeasure_zero_self {E : Type*} [PseudoMetricSpace E] [Zero E] :
    TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => (0 : E)) atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  have : {x : Ω | ε ≤ (0 : ℝ)} = ∅ := by ext; simp [hε]
  simp [this]

/-- From convergence in probability to `0`: `P(θ < L n) → 0` for `θ > 0`. -/
private lemma tendsto_measureReal_lt_of_tendstoInMeasure_zero {L : ℕ → Ω → ℝ}
    (hL : TendstoInMeasure μ L atTop fun _ => 0) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun n => μ.real {ω | θ < L n ω}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hL θ hθ)
    (fun _ => measureReal_nonneg) fun n => measureReal_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  exact hω.le.trans (le_abs_self _)

/-- From convergence in probability to `v`: `P(K < S n) → 0` for `K > v`. -/
private lemma tendsto_measureReal_gt_of_tendstoInMeasure {S : ℕ → Ω → ℝ} {v K : ℝ}
    (hS : TendstoInMeasure μ S atTop fun _ => v) (hK : v < K) :
    Tendsto (fun n => μ.real {ω | K < S n ω}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hS (K - v) (by linarith))
    (fun _ => measureReal_nonneg) fun n => measureReal_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
  exact (by linarith : K - v ≤ S n ω - v).trans (le_abs_self _)

end InMeasure

/-! ### The cut array satisfies McLeish's conditions -/

section Array

variable [IsProbabilityMeasure μ] {X : ℕ → ℕ → Ω → ℝ} {F : ℕ → Filtration ℕ m0} {r : ℕ → ℕ}

/-- McLeish's (a) for the cut array: `E[max_k X' n k²] ≤ K`. -/
private lemma lintegral_iSup_cutX_le (hL2 : ∀ n k, MemLp (X n k) 2 μ) {K : ℝ} (hK : 0 ≤ K)
    (n : ℕ) :
    ∫⁻ ω, ⨆ k ∈ range (r n), ‖cutX μ (F n) (X n) K k ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal K := by
  have hpt : ∀ ω, (⨆ k ∈ range (r n), ‖cutX μ (F n) (X n) K k ω‖ₑ ^ 2) ≤
      ENNReal.ofReal (∑ k ∈ range (r n), cutX μ (F n) (X n) K k ω ^ 2) := by
    intro ω
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    refine iSup₂_le fun k hk => ?_
    refine le_trans (le_of_eq ?_) (single_le_sum (f := fun k =>
      ENNReal.ofReal (cutX μ (F n) (X n) K k ω ^ 2)) (fun _ _ => zero_le) hk)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hint : Integrable (fun ω => ∑ k ∈ range (r n), cutX μ (F n) (X n) K k ω ^ 2) μ :=
    integrable_finsetSum _ fun k _ => (memLp_cutX (hL2 n) K k).integrable_sq
  refine (lintegral_mono hpt).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun ω => sum_nonneg fun k _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (integral_sum_sq_cutX_le (hL2 n) hK (r n))

/-- McLeish's (b) for the cut array, from the conditional Lindeberg condition. -/
private lemma tendsto_measure_exists_cutX_gt (hX : ∀ n k, StronglyMeasurable[F n (k + 1)] (X n k))
    (hL2 : ∀ n k, MemLp (X n k) 2 μ) {K : ℝ} (hK : 0 ≤ K)
    (hcondL : ∀ ε : ℝ, 0 < ε → TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n),
      (μ[bigSq (X n) ε k | F n k]) ω) atTop (fun _ => 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ∃ k ∈ range (r n), ε < |cutX μ (F n) (X n) K k ω|}) atTop
      (𝓝 0) := by
  rw [← ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]
  refine tendsto_zero_of_forall_le (fun _ => ENNReal.toReal_nonneg) fun δ hδ => ?_
  set θ := δ * ε ^ 2 / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hP := tendsto_measureReal_lt_of_tendstoInMeasure_zero (hcondL ε hε) hθ0
  have hKP : Tendsto (fun n => K * μ.real {ω | θ < ∑ k ∈ range (r n),
      (μ[bigSq (X n) ε k | F n k]) ω}) atTop (𝓝 0) := by
    simpa using hP.const_mul K
  filter_upwards [(hKP.eventually (Iic_mem_nhds (show (0 : ℝ) < δ * ε ^ 2 / 2 by positivity)))]
    with n hn
  have hb := measureReal_exists_cutX_gt_le (μ := μ) (F := F n) (X := X n) (hX n) (hL2 n) hK hε
    (le_refl (r n)) hθ0.le
  rw [← measureReal_def]
  refine hb.trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Realized minus kept predictable quadratic variation of the cut array tends to `0` in
probability, at any times `m n ≤ r n`. -/
private lemma tendstoInMeasure_realized_sub (hX : ∀ n k, StronglyMeasurable[F n (k + 1)] (X n k))
    (hL2 : ∀ n k, MemLp (X n k) 2 μ) {K : ℝ} (hK : 0 ≤ K)
    (hcondL : ∀ ε : ℝ, 0 < ε → TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n),
      (μ[bigSq (X n) ε k | F n k]) ω) atTop (fun _ => 0))
    {m : ℕ → ℕ} (hmr : ∀ n, m n ≤ r n) :
    TendstoInMeasure μ (fun n ω => ∑ k ∈ range (m n), cutX μ (F n) (X n) K k ω ^ 2 -
      ∑ k ∈ range (m n), (cutSet μ (F n) (X n) K k).indicator (condSq μ (F n) (X n) k) ω)
      atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro η' hη'
  set η := η' / 3 with hη
  have hη0 : 0 < η := by positivity
  refine tendsto_zero_of_forall_le (fun _ => measureReal_nonneg) fun δ hδ => ?_
  set ε := min 1 (δ * η ^ 2 / (3 * (K + 1))) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ δ * η ^ 2 / (3 * (K + 1)) := min_le_right _ _
  set θ := δ * η / 6 with hθ
  have hθ0 : 0 < θ := by positivity
  have hP := tendsto_measureReal_lt_of_tendstoInMeasure_zero (hcondL ε hε0) hθ0
  have hKP : Tendsto (fun n => K * μ.real {ω | θ < ∑ k ∈ range (r n),
      (μ[bigSq (X n) ε k | F n k]) ω}) atTop (𝓝 0) := by
    simpa using hP.const_mul K
  filter_upwards [(hKP.eventually (Iic_mem_nhds (show (0 : ℝ) < δ * η / 6 by positivity)))]
    with n hn
  have hb := measureReal_realized_sub_le (μ := μ) (F := F n) (X := X n) (hX n) (hL2 n) hK ε
    (hmr n) hθ0.le hη0
  have hset : {ω | η' ≤ dist (∑ k ∈ range (m n), cutX μ (F n) (X n) K k ω ^ 2 -
      ∑ k ∈ range (m n), (cutSet μ (F n) (X n) K k).indicator (condSq μ (F n) (X n) k) ω)
      ((0 : Ω → ℝ) ω)} = {ω | 3 * η ≤ |∑ k ∈ range (m n), cutX μ (F n) (X n) K k ω ^ 2 -
      ∑ k ∈ range (m n), (cutSet μ (F n) (X n) K k).indicator (condSq μ (F n) (X n) k) ω|} := by
    ext ω; simp [hη, mul_div_cancel₀ η' (three_ne_zero (α := ℝ))]
  rw [hset]
  refine hb.trans ?_
  have hε2' : ε ^ 2 * K / η ^ 2 ≤ δ / 3 := by
    have h1 : ε ^ 2 ≤ ε := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have h2 : ε * (3 * (K + 1)) ≤ δ * η ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hε2
    nlinarith [sq_nonneg η, mul_nonneg hK (sq_nonneg ε)]
  have h3 : 2 * ((θ + K * μ.real {ω | θ < ∑ k ∈ range (r n), (μ[bigSq (X n) ε k | F n k]) ω})
      / η) ≤ 2 * δ / 3 := by
    rw [mul_div_assoc', div_le_iff₀ hη0]
    rw [hθ] at hn ⊢
    nlinarith
  linarith

/-- Off the event `{K < ∑_{k < r n} E[X n k² | F n k]}`, the cut changes nothing up to
time `r n`. -/
private lemma cut_eq_off (n : ℕ) {K : ℝ} :
    ∀ᵐ ω ∂μ, ω ∉ {ω | K < ∑ k ∈ range (r n), condSq μ (F n) (X n) k ω} →
      ∀ m ≤ r n, ∀ k < m, ω ∈ cutSet μ (F n) (X n) K k := by
  filter_upwards [condSq_nonneg (μ := μ) (F := F n) (X := X n)] with ω hω hgood m hm k hk
  simp only [not_lt] at hgood
  simp only [cutSet, Set.mem_ofPred_eq]
  exact le_trans (sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    fun j _ _ => hω j) hgood

/-- McLeish's (c) for the cut array: realized quadratic variation converges wherever the
predictable one does, at any times `m n ≤ r n`, once the terminal predictable quadratic
variation exceeds `K` with vanishing probability. -/
private lemma tendstoInMeasure_sum_sq_cutX (hX : ∀ n k, StronglyMeasurable[F n (k + 1)] (X n k))
    (hL2 : ∀ n k, MemLp (X n k) 2 μ) {K : ℝ} (hK : 0 ≤ K)
    (hcondL : ∀ ε : ℝ, 0 < ε → TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n),
      (μ[bigSq (X n) ε k | F n k]) ω) atTop (fun _ => 0))
    (hB : Tendsto (fun n => μ.real {ω | K < ∑ k ∈ range (r n), condSq μ (F n) (X n) k ω})
      atTop (𝓝 0))
    {m : ℕ → ℕ} (hmr : ∀ n, m n ≤ r n) {a : ℝ}
    (hpqv : TendstoInMeasure μ (fun n ω => ∑ k ∈ range (m n), condSq μ (F n) (X n) k ω) atTop
      (fun _ => a)) :
    TendstoInMeasure μ (fun n ω => ∑ k ∈ range (m n), cutX μ (F n) (X n) K k ω ^ 2) atTop
      (fun _ => a) := by
  have hkept : TendstoInMeasure μ (fun n ω => ∑ k ∈ range (m n),
      (cutSet μ (F n) (X n) K k).indicator (condSq μ (F n) (X n) k) ω) atTop (fun _ => a) := by
    refine tendstoInMeasure_of_ae_eq_off hB (fun n => ?_) hpqv
    filter_upwards [cut_eq_off (μ := μ) (F := F) (X := X) (r := r) n (K := K)] with ω hω hgood
    exact sum_congr rfl fun k hk =>
      Set.indicator_of_mem (hω hgood (m n) (hmr n) k (mem_range.1 hk)) _
  have h := tendstoInMeasure_add (tendstoInMeasure_realized_sub hX hL2 hK hcondL hmr) hkept
  refine h.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
  · simp
  · simp

end Array

/-! ### Main results -/

section Main

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The predictable quadratic variation of the partial sums `∑_{j<k} X j` is
`∑_{k<m} E[X k² | F k]`. -/
private lemma predictableQuadraticVariation_partialSum (F : Filtration ℕ m0) (X : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) :
    predictableQuadraticVariation μ F (fun k ω => ∑ j ∈ range k, X j ω) m ω =
      ∑ k ∈ range m, condSq μ F X k ω := by
  simp only [predictableQuadraticVariation, condSq]
  refine sum_congr rfl fun k _ => ?_
  congr 2
  funext ω'
  simp [sum_range_succ]

/-- The (unconditional) Lindeberg condition implies the conditional Lindeberg condition in
probability. -/
private lemma condLindeberg_of_lindeberg {X : ℕ → ℕ → Ω → ℝ} {F : ℕ → Filtration ℕ m0}
    (hL : LindebergConditionTriangular X μ) (ε : ℝ) (hε : 0 < ε) :
    TendstoInMeasure μ (fun n ω => ∑ k ∈ range n, (μ[bigSq (X n) ε k | F n k]) ω) atTop
      (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro θ hθ
  have hint : ∀ n, Integrable (fun ω => ∑ k ∈ range n, (μ[bigSq (X n) ε k | F n k]) ω) μ :=
    fun n => integrable_finsetSum _ fun k _ => integrable_condExp
  have hnn : ∀ n, 0 ≤ᵐ[μ] fun ω => ∑ k ∈ range n, (μ[bigSq (X n) ε k | F n k]) ω := by
    intro n
    have : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ μ[bigSq (X n) ε k | F n k] ω := by
      rw [ae_all_iff]; intro k
      exact condExp_nonneg (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
    filter_upwards [this] with ω hω
    exact sum_nonneg fun k _ => hω k
  have hE : ∀ n, ∫ ω, ∑ k ∈ range n, (μ[bigSq (X n) ε k | F n k]) ω ∂μ =
      ∑ k ∈ range n, ∫ ω, X n k ω ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ := by
    intro n
    rw [integral_finsetSum _ fun k _ => integrable_condExp]
    refine sum_congr rfl fun k _ => ?_
    rw [integral_condExp ((F n).le k)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases h : ε < |X n k ω| <;> simp [bigSq, h]
  have hlim : Tendsto (fun n => θ⁻¹ * ∫ ω, ∑ k ∈ range n, (μ[bigSq (X n) ε k | F n k]) ω ∂μ)
      atTop (𝓝 0) := by
    simp_rw [hE]; simpa using (hL ε hε).const_mul θ⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => measureReal_nonneg) fun n => ?_
  rw [le_inv_mul_iff₀ hθ]
  refine le_trans ?_ (mul_meas_ge_le_integral_of_nonneg (hnn n) (hint n) θ)
  refine mul_le_mul_of_nonneg_left (measureReal_mono_ae' ?_) hθ.le
  filter_upwards [hnn n] with ω hω hmem
  simp only [Real.dist_eq, sub_zero] at hmem ⊢
  rwa [abs_of_nonneg hω] at hmem

/-- **Martingale CLT under the conditional-variance normalization** (Brown 1971; Hall–Heyde
Corollary 3.1 with a constant limit). Let row `n` of `X` be a square-integrable martingale
difference sequence for the filtration `F n` (the partial sums `∑_{j<k} X n j` form a
martingale; a finite row is extended by zeros). If the **predictable** quadratic variation
`∑_{k<r n} E[X n k² | F n k]` of row `n` (Mathlib-Ext's `predictableQuadraticVariation` of the
partial sums) tends to `v` in probability and the **conditional Lindeberg condition**
`∑_{k<r n} E[X n k² 1{ε < |X n k|} | F n k] → 0` in probability holds for every `ε > 0`, then
`∑_{k<r n} X n k → N(0, v)` in distribution.

Compared with `tendstoInDistribution_martingale_mcLeish`, the realized quadratic variation
`∑ X n k²` is replaced by the predictable one, and McLeish's maximal-moment condition is not
assumed.

Proof: cut each row predictably, keeping increment `k` while `∑_{j ≤ k} E[X n j² | F n j]`
stays `≤ v + 1`. The cut row is still a martingale difference sequence, has
`E[∑ X'²] ≤ v + 1` (so McLeish's (a)), its maximal increment tends to `0` (McLeish's (b),
from the conditional Lindeberg condition), and its realized quadratic variation tends to `v`
(McLeish's (c)): the big jumps are controlled by the conditional Lindeberg condition and the
centred small jumps form a martingale with `L²` norm at most `ε² (v + 1)`. McLeish's theorem
applies to the cut row, which agrees with the original one outside an event of vanishing
probability. -/
theorem tendstoInDistribution_martingale_condVar
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0) (r : ℕ → ℕ)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hL2 : ∀ n k, MemLp (X n k) 2 μ) (v : ℝ≥0)
    (hpqv : TendstoInMeasure μ (fun n => predictableQuadraticVariation μ (F n)
      (fun k ω => ∑ j ∈ range k, X n j ω) (r n)) atTop (fun _ => (v : ℝ)))
    (hcondL : ∀ ε : ℝ, 0 < ε → TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n),
      (μ[{ω' | ε < |X n k ω'|}.indicator (fun ω' => X n k ω' ^ 2) | F n k]) ω) atTop
      (fun _ => 0)) :
    TendstoInDistribution (fun n ω => ∑ k ∈ range (r n), X n k ω) atTop id (fun _ => μ)
      (gaussianReal 0 v) := by
  have hX : ∀ n k, StronglyMeasurable[F n (k + 1)] (X n k) := fun n k =>
    (martingale_increment (hmart n) k).1
  have hmds : ∀ n k, μ[X n k | F n k] =ᵐ[μ] 0 := fun n k => (martingale_increment (hmart n) k).2.2
  have hpqv' : TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n), condSq μ (F n) (X n) k ω)
      atTop (fun _ => (v : ℝ)) :=
    hpqv.congr (fun n => ae_of_all _ fun ω => predictableQuadraticVariation_partialSum _ _ _ ω)
      (ae_of_all _ fun _ => rfl)
  set K : ℝ := v + 1 with hKdef
  have hK : 0 ≤ K := by positivity
  have hB := tendsto_measureReal_gt_of_tendstoInMeasure hpqv' (show (v : ℝ) < K by linarith)
  have hCLT := tendstoInDistribution_martingale_mcLeish (fun n => cutX μ (F n) (X n) K) F r
    (fun n => martingale_cutX (hX n) (hL2 n) (hmds n) K)
    ⟨ENNReal.ofReal K, ENNReal.ofReal_ne_top,
      Eventually.of_forall fun n => lintegral_iSup_cutX_le hL2 hK n⟩
    (tendsto_measure_exists_cutX_gt hX hL2 hK hcondL) v
    (tendstoInMeasure_sum_sq_cutX hX hL2 hK hcondL hB (fun n => le_rfl) hpqv')
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hCLT ?_ fun n =>
    (Finset.measurable_fun_sum _ fun k _ => ((hX n k).mono ((F n).le _)).measurable).aemeasurable
  refine tendstoInMeasure_of_ae_eq_off hB (fun n => ?_) tendstoInMeasure_zero_self
  filter_upwards [cut_eq_off (μ := μ) (F := F) (X := X) (r := r) n (K := K)] with ω hω hgood
  simp only [Pi.sub_apply]
  rw [sub_eq_zero]
  exact sum_congr rfl fun k hk =>
    (Set.indicator_of_mem (hω hgood (r n) le_rfl k (mem_range.1 hk)) _).symm

/-- **Lindeberg form.** Rows of length `n`, square-integrable martingale differences, the
(unconditional) Lindeberg condition `LindebergConditionTriangular`, and the predictable
quadratic variation `∑_{k<n} E[X n k² | F n k] → v` in probability give
`∑_{k<n} X n k → N(0, v)`. The Lindeberg condition implies the conditional one (take
expectations and use Markov's inequality), so this is a corollary of
`tendstoInDistribution_martingale_condVar`.

Source: Hall–Heyde (1980), Corollary 3.1 together with the remark that the Lindeberg condition
implies the conditional Lindeberg condition; Brown (1971). -/
theorem tendstoInDistribution_martingale_condVar_lindeberg
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hL2 : ∀ n k, MemLp (X n k) 2 μ) (hL : LindebergConditionTriangular X μ) (v : ℝ≥0)
    (hpqv : TendstoInMeasure μ (fun n => predictableQuadraticVariation μ (F n)
      (fun k ω => ∑ j ∈ range k, X n j ω) n) atTop (fun _ => (v : ℝ))) :
    TendstoInDistribution (fun n ω => ∑ k ∈ range n, X n k ω) atTop id (fun _ => μ)
      (gaussianReal 0 v) :=
  tendstoInDistribution_martingale_condVar X F id hmart hL2 v hpqv
    (condLindeberg_of_lindeberg hL)

/-- **Finite-dimensional convergence under the conditional-variance normalization.** Let
`S n s = ∑_{k < N n s} X n k` along a linearly ordered time axis, with `N n` monotone and
`N n s ≤ r n`. If the predictable quadratic variation up to `N n s` tends to `A s` in probability
for every `s`, the predictable quadratic variation of the whole row (up to `r n`) converges in
probability to some `V`, and the conditional Lindeberg condition holds on the whole row, then
the finite-dimensional distributions of `S n` converge to those of any process `Z` with centered
Gaussian finite-dimensional laws of covariance `A (min s u)`.

The terminal hypothesis `hpqvEnd` is automatic when the row ends at a time of the axis
(`r n = N n s₁`), as in `tendstoInDistribution_fdd_martingaleDifference_floor_condVar`. It is a
proof convenience, not a sharp condition: the cut is built from the predictable quadratic
variation of the whole row because the fdd interface of McLeish's theorem wants `N n s ≤ r n`
and the quadratic-variation limit at every `s`; cutting at `N n (max I)` after re-indexing the
time axis to `I` would remove it.

The proof is the cut of `tendstoInDistribution_martingale_condVar` (at level `|V| + 1`)
followed by `tendstoInDistribution_fdd_martingale_mcLeish`. -/
theorem tendstoInDistribution_fdd_martingale_condVar
    {ι : Type*} [LinearOrder ι]
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0) (r : ℕ → ℕ)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hL2 : ∀ n k, MemLp (X n k) 2 μ)
    (hcondL : ∀ ε : ℝ, 0 < ε → TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n),
      (μ[{ω' | ε < |X n k ω'|}.indicator (fun ω' => X n k ω' ^ 2) | F n k]) ω) atTop
      (fun _ => 0))
    (V : ℝ) (hpqvEnd : TendstoInMeasure μ (fun n => predictableQuadraticVariation μ (F n)
      (fun k ω => ∑ j ∈ range k, X n j ω) (r n)) atTop (fun _ => V))
    (N : ℕ → ι → ℕ) (hN : ∀ n, Monotone (N n)) (hNr : ∀ n s, N n s ≤ r n) (A : ι → ℝ)
    (hpqv : ∀ s, TendstoInMeasure μ (fun n => predictableQuadraticVariation μ (F n)
      (fun k ω => ∑ j ∈ range k, X n j ω) (N n s)) atTop (fun _ => A s))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : ι → Ω' → ℝ) (hZm : ∀ s, Measurable (Z s))
    (hZ : ∀ (I : Finset ι) (c : I → ℝ), P'.map (fun ω => ∑ s : I, c s * Z s ω) =
      gaussianReal 0 (∑ s : I, ∑ u : I, c s * c u * A (min (s : ι) u)).toNNReal)
    (I : Finset ι) :
    TendstoInDistribution (fun n ω => I.restrict fun s => ∑ k ∈ range (N n s), X n k ω) atTop
      (fun ω => I.restrict fun s => Z s ω) (fun _ => μ) P' := by
  have hX : ∀ n k, StronglyMeasurable[F n (k + 1)] (X n k) := fun n k =>
    (martingale_increment (hmart n) k).1
  have hmds : ∀ n k, μ[X n k | F n k] =ᵐ[μ] 0 := fun n k => (martingale_increment (hmart n) k).2.2
  have hcond : ∀ (m : ℕ → ℕ) (a : ℝ), TendstoInMeasure μ (fun n =>
      predictableQuadraticVariation μ (F n) (fun k ω => ∑ j ∈ range k, X n j ω) (m n)) atTop
      (fun _ => a) → TendstoInMeasure μ
        (fun n ω => ∑ k ∈ range (m n), condSq μ (F n) (X n) k ω) atTop (fun _ => a) :=
    fun m a h => h.congr
      (fun n => ae_of_all _ fun ω => predictableQuadraticVariation_partialSum _ _ _ ω)
      (ae_of_all _ fun _ => rfl)
  set K : ℝ := |V| + 1 with hKdef
  have hK : 0 ≤ K := by positivity
  have hB := tendsto_measureReal_gt_of_tendstoInMeasure (hcond r V hpqvEnd)
    (show V < K by linarith [le_abs_self V])
  have hfdd := tendstoInDistribution_fdd_martingale_mcLeish (fun n => cutX μ (F n) (X n) K) F r
    (fun n => martingale_cutX (hX n) (hL2 n) (hmds n) K)
    ⟨ENNReal.ofReal K, ENNReal.ofReal_ne_top,
      Eventually.of_forall fun n => lintegral_iSup_cutX_le hL2 hK n⟩
    (tendsto_measure_exists_cutX_gt hX hL2 hK hcondL) N hN hNr A
    (fun s => tendstoInMeasure_sum_sq_cutX hX hL2 hK hcondL hB (fun n => hNr n s)
      (hcond (fun n => N n s) (A s) (hpqv s))) Z hZm hZ I
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hfdd ?_ fun n => ?_
  · refine tendstoInMeasure_of_ae_eq_off hB (fun n => ?_) tendstoInMeasure_zero_self
    filter_upwards [cut_eq_off (μ := μ) (F := F) (X := X) (r := r) n (K := K)] with ω hω hgood
    funext s
    simp only [Pi.sub_apply, Pi.zero_apply, Finset.restrict]
    rw [sub_eq_zero]
    exact sum_congr rfl fun k hk =>
      (Set.indicator_of_mem (hω hgood (N n s) (hNr n s) k (mem_range.1 hk)) _).symm
  · exact (Measurable.of_eval fun s : I => Finset.measurable_fun_sum _ fun k _ =>
      ((hX n k).mono ((F n).le _)).measurable).aemeasurable

/-- **Finite-dimensional convergence of the step sums on `[0,1]` from the predictable
quadratic variation**, in the form of the hypothesis `hT81` of the martingale functional CLT
`tendstoInDistribution_arrayStepProcess` (`MathlibExt.Probability.Martingale.MartingaleTightness`,
roadmap task T82), under T82's own array hypotheses.

Row `n` of `ξ` is a square-integrable martingale difference sequence for `𝓕 n` satisfying
`LindebergConditionTriangular`, and the predictable quadratic variation
`∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j]` tends to `t` in probability for every `t ∈ [0,1]`; these are
exactly T82's hypotheses `hξ`, `hmds`, `hL2`, `hQV`, `hLind`. If `Z` is measurable with the
centered Gaussian finite-dimensional laws of Brownian motion (covariance `min s u`), then for
every finite `I ⊆ [0,1]`, `(∑_{i < ⌊n t⌋} ξ n i)_{t ∈ I} → (Z t)_{t ∈ I}` in distribution.

Compared with `tendstoInDistribution_fdd_martingaleDifference_floor`, the realized
quadratic-variation hypothesis `hRQV` is gone. -/
theorem tendstoInDistribution_fdd_martingaleDifference_floor_condVar
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {𝓕 : ℕ → Filtration ℕ m0} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ)
    (Z : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hZm : Measurable Z)
    (hZ : ∀ (I : Finset (Set.Icc (0 : ℝ) 1)) (c : I → ℝ),
      P'.map (fun ω => ∑ s : I, c s * Z ω s) = gaussianReal 0
        (∑ s : I, ∑ u : I, c s * c u * (min (s : Set.Icc (0 : ℝ) 1) u).1).toNNReal) :
    ∀ I : Finset (Set.Icc (0 : ℝ) 1), TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict (fun t => ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n i ω))
      atTop (fun ω => I.restrict (fun t => Z ω t)) (fun _ => μ) P' := by
  intro I
  have hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, ξ n j ω) (𝓕 n) μ := by
    intro n
    refine martingale_of_condExp_sub_eq_zero_nat (fun k => ?_) (fun k => ?_) fun k => ?_
    · exact Finset.stronglyMeasurable_fun_sum _ fun j hj =>
        (hξ n j).mono ((𝓕 n).mono (Nat.succ_le_of_lt (mem_range.1 hj)))
    · exact integrable_finsetSum _ fun j _ => (hL2 n j).integrable one_le_two
    · have hd : ((fun ω => ∑ j ∈ range (k + 1), ξ n j ω) - fun ω => ∑ j ∈ range k, ξ n j ω)
          = ξ n k := by funext ω; simp [sum_range_succ]
      rw [hd]; exact hmds n k
  have hN : ∀ n : ℕ, Monotone (fun t : Set.Icc (0 : ℝ) 1 => ⌊(n : ℝ) * t.1⌋₊) := fun n s u hsu =>
    Nat.floor_mono (mul_le_mul_of_nonneg_left (Subtype.mono_coe _ hsu) (Nat.cast_nonneg (α := ℝ) n))
  have hNn : ∀ (n : ℕ) (t : Set.Icc (0 : ℝ) 1), ⌊(n : ℝ) * t.1⌋₊ ≤ n := fun n t =>
    Nat.floor_le_of_le (by nlinarith [t.2.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hpqv : ∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ (fun n =>
      predictableQuadraticVariation μ (𝓕 n) (fun k ω => ∑ j ∈ range k, ξ n j ω)
        ⌊(n : ℝ) * t.1⌋₊) atTop (fun _ => t.1) := fun t =>
    (hQV t.1 t.2).congr
      (fun n => ae_of_all _ fun ω => (predictableQuadraticVariation_partialSum _ _ _ ω).symm)
      (ae_of_all _ fun _ => rfl)
  have hEnd : TendstoInMeasure μ (fun n => predictableQuadraticVariation μ (𝓕 n)
      (fun k ω => ∑ j ∈ range k, ξ n j ω) (id n)) atTop (fun _ => (1 : ℝ)) := by
    have h := hpqv ⟨1, by norm_num, le_rfl⟩
    refine h.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
    simp
  exact tendstoInDistribution_fdd_martingale_condVar (ι := Set.Icc (0 : ℝ) 1) ξ 𝓕 id hmart hL2
    (condLindeberg_of_lindeberg hLind) 1 hEnd (fun n t => ⌊(n : ℝ) * t.1⌋₊) hN hNn
    (fun t => t.1) hpqv (fun s ω => Z ω s)
    (fun s => (continuous_eval_const s).measurable.comp hZm) hZ I

end Main

end

end MathlibExt.Probability.Martingale
