/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.VaradhanIntegralLemma
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Superexponential tightness and the product large deviation principle

Let `μₙ` satisfy a large deviation principle (LDP) with a good rate function `I` on a Polish
space.

* **Superexponential tightness.** For every `ℓ` there is a compact `K` with
  `μₙ(Kᶜ) ≤ exp (-n ℓ)` for every `n`.
* **Product LDP.** If also `νₙ` satisfies an LDP with a good rate function `J` on a Polish space
  and all measures are probability measures, then `μₙ × νₙ` satisfies an LDP with the good rate
  function `(x, y) ↦ I x + J y`.

## Proof idea

Tightness: the level set `{I ≤ ℓ + k + 2}` is compact, so for each `k` it is covered by an open
set `Uₖ`, a finite union of balls of radius `1/(k+1)`. The LDP upper bound on the closed set
`Uₖᶜ` gives `μₙ(Uₖᶜ) ≤ 2^{-(k+1)} exp (-n ℓ)` for large `n`; the finitely many remaining
measures are tight (inner regularity of finite measures on Polish spaces), which provides a
compact `Cₖ`. The set `⋂ₖ (Uₖ ∪ Cₖ)` is totally bounded, so its closure is compact, and its
complement has mass at most `∑ₖ 2^{-(k+1)} exp (-n ℓ) = exp (-n ℓ)`.

Product LDP: the lower bound uses product neighbourhoods `U × V`. For the upper bound, a local
estimate around each point, a finite-subcover argument on compact sets, and the
superexponential tightness of both factors handle an arbitrary closed set.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 2, Theorems 2.4 and 2.6 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf).

## Main results

* `exists_isCompact_measure_compl_le`: superexponential tightness (Theorem 2.4), for every `n`.
* `isGoodRateFunction_prod`: `(x, y) ↦ I x + J y` is a good rate function.
* `satisfiesLDP_prod`: the product LDP (Theorem 2.6).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MathlibExt.Probability.LDPProduct

open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.VaradhanIntegralLemma (coe_le_inv_mul_log_iff inv_mul_log_le_coe_iff)

/-- **Geometric weights sum to one.** `∑ₖ 2⁻¹ ^ (k + 1) = 1` in `ℝ≥0∞`. -/
theorem tsum_inv_two_pow_succ : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- **A numerical bound for the tail weights.** For `n ≥ 1`, `k : ℕ` and `ℓ : ℝ`,
`exp (n · (-(ℓ + k + 1))) ≤ 2⁻¹ ^ (k + 1) · exp (-(n ℓ))`. -/
theorem ofReal_exp_le_inv_two_pow_mul {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (ℓ : ℝ) :
    ENNReal.ofReal (Real.exp (n * (-(ℓ + (k + 1))))) ≤
      (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num
    exact h2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hreal : Real.exp (n * (-(ℓ + (k + 1)))) ≤ (1 / 2) ^ (k + 1) * Real.exp (-(n * ℓ)) := by
    have e1 : Real.exp (n * (-(ℓ + (k + 1)))) =
        Real.exp (-(n * ℓ)) * Real.exp (((k + 1 : ℕ) : ℝ) * (-1) - (n - 1) * (k + 1)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e1, mul_comm]
    gcongr
    calc Real.exp (((k + 1 : ℕ) : ℝ) * (-1) - (n - 1) * (k + 1))
        ≤ Real.exp (((k + 1 : ℕ) : ℝ) * (-1)) := by
          gcongr
          have : (0 : ℝ) ≤ (n - 1) * (k + 1) := mul_nonneg (by linarith) (by positivity)
          linarith
      _ = Real.exp (-1) ^ (k + 1) := Real.exp_nat_mul _ _
      _ ≤ (1 / 2) ^ (k + 1) := by gcongr
  calc ENNReal.ofReal (Real.exp (n * (-(ℓ + (k + 1)))))
      ≤ ENNReal.ofReal ((1 / 2) ^ (k + 1) * Real.exp (-(n * ℓ))) := ENNReal.ofReal_le_ofReal hreal
    _ = (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), one_div,
        ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

section Tightness

/-- **One step of the superexponential tightness construction.** In a complete separable
metric space, for `ℓ ≥ 0` and `k : ℕ` there are a finite set `t` and a compact set `C` such
that, for every `n`, the complement of `(⋃ y ∈ t, ball y (1/(k+1))) ∪ C` has `μₙ`-mass at
most `2⁻¹ ^ (k + 1) · exp (-n ℓ)`. -/
theorem exists_finite_isCompact_measure_compl_le {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} [∀ n, IsFiniteMeasure (μ n)] {I : X → ℝ≥0∞} (hμ : SatisfiesLDP μ I)
    (hI : IsGoodRateFunction I) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : ℕ) :
    ∃ t C : Set X, t.Finite ∧ IsCompact C ∧ ∀ n : ℕ,
      μ n ((⋃ y ∈ t, Metric.ball y (1 / (k + 1 : ℝ))) ∪ C)ᶜ ≤
        (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
  set L : ℝ := ℓ + (k + 1) + 1 with hL_def
  have hL : 0 ≤ L := by rw [hL_def]; positivity
  set A := {x | I x ≤ ENNReal.ofReal L} with hA_def
  have hA : IsCompact A := hI.isCompact_levelSet L
  obtain ⟨t, ht, hAt⟩ := Metric.totallyBounded_iff.1 hA.totallyBounded (1 / (k + 1 : ℝ))
    (by positivity)
  set U := ⋃ y ∈ t, Metric.ball y (1 / (k + 1 : ℝ)) with hU_def
  have hU : IsOpen U := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  -- the LDP upper bound on `Uᶜ`
  have hinf : -(⨅ x ∈ Uᶜ, (I x : EReal)) ≤ ((-L : ℝ) : EReal) := by
    rw [EReal.neg_le, EReal.coe_neg, neg_neg]
    refine le_iInf₂ fun x hx => ?_
    have hxA : x ∉ A := fun h => hx (hAt h)
    have hlt : ENNReal.ofReal L < I x := lt_of_not_ge hxA
    have hcoe : ((ENNReal.ofReal L : ℝ≥0∞) : EReal) = (L : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hL]
    rw [← hcoe]
    exact (EReal.coe_ennreal_lt_coe_ennreal_iff.2 hlt).le
  have hlim : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Uᶜ)) atTop <
      ((-(ℓ + (k + 1)) : ℝ) : EReal) :=
    (hμ.upper_bound _ hU.isClosed_compl).trans_lt (hinf.trans_lt (by
      exact_mod_cast (show -L < -(ℓ + (k + 1)) by rw [hL_def]; linarith)))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 ((eventually_lt_of_limsup_lt hlim).and
    (eventually_ge_atTop 1)))
  -- tightness of the finitely many measures `μ n`, `n < N`
  have htight : ∀ n : ℕ, ∃ B : Set X, IsCompact B ∧
      μ n Bᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
    intro n
    have hpos : 0 < (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.exp (-(n * ℓ))) :=
      ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
        (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    obtain ⟨K, hK, hKμ⟩ := exists_isCompact_closure_measure_compl_lt (μ n) _ hpos
    exact ⟨closure K, hK, (measure_mono (compl_subset_compl.2 subset_closure)).trans hKμ.le⟩
  choose B hB using htight
  refine ⟨t, ⋃ n ∈ Finset.range N, B n, ht, (Finset.range N).isCompact_biUnion
    fun n _ => (hB n).1, fun n => ?_⟩
  by_cases hnN : N ≤ n
  · obtain ⟨h1, h2⟩ := hN n hnN
    have hn0 : 0 < n := h2
    refine (measure_mono (compl_subset_compl.2 subset_union_left)).trans ?_
    refine ((inv_mul_log_le_coe_iff hn0 _ _).1 h1.le).trans ?_
    exact ofReal_exp_le_inv_two_pow_mul h2 k ℓ
  · refine (measure_mono (compl_subset_compl.2 ?_)).trans (hB n).2
    exact (subset_biUnion_of_mem (u := B) (Finset.mem_range.2 (lt_of_not_ge hnN))).trans
      subset_union_right

/-- **Superexponential tightness, metric form.** Let `μₙ` be finite measures on a complete
separable pseudometric space satisfying an LDP with a good rate function. Then for every `ℓ`
there is a compact set `K` with `μₙ(Kᶜ) ≤ exp (-n ℓ)` for every `n`. -/
theorem exists_isCompact_measure_compl_le_of_metric {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} [∀ n, IsFiniteMeasure (μ n)] {I : X → ℝ≥0∞} (hμ : SatisfiesLDP μ I)
    (hI : IsGoodRateFunction I) (ℓ : ℝ) :
    ∃ K : Set X, IsCompact K ∧ ∀ n : ℕ, μ n Kᶜ ≤ ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
  -- reduce to `ℓ ≥ 0`
  suffices h : ∀ ℓ : ℝ, 0 ≤ ℓ → ∃ K : Set X, IsCompact K ∧
      ∀ n : ℕ, μ n Kᶜ ≤ ENNReal.ofReal (Real.exp (-(n * ℓ))) by
    obtain ⟨K, hK, hKμ⟩ := h (max ℓ 0) (le_max_right _ _)
    refine ⟨K, hK, fun n => (hKμ n).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    gcongr
    exact le_max_left _ _
  intro ℓ hℓ
  choose t C ht hC hbd using fun k => exists_finite_isCompact_measure_compl_le hμ hI hℓ k
  set E := ⋂ k, ((⋃ y ∈ t k, Metric.ball y (1 / (k + 1 : ℝ))) ∪ C k) with hE_def
  have hE : TotallyBounded E := by
    refine Metric.totallyBounded_iff.2 fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨t', ht', hCt'⟩ := Metric.totallyBounded_iff.1 (hC k).totallyBounded ε hε
    refine ⟨t k ∪ t', (ht k).union ht', fun x hx => ?_⟩
    rcases mem_iInter.1 hx k with h | h
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 h
      exact mem_iUnion₂.2 ⟨y, Or.inl hy, Metric.ball_subset_ball hk.le hxy⟩
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hCt' h)
      exact mem_iUnion₂.2 ⟨y, Or.inr hy, hxy⟩
  refine ⟨closure E, isCompact_iff_totallyBounded_isComplete.2
    ⟨hE.closure, isClosed_closure.isComplete⟩, fun n => ?_⟩
  calc μ n (closure E)ᶜ ≤ μ n Eᶜ := measure_mono (compl_subset_compl.2 subset_closure)
    _ = μ n (⋃ k, ((⋃ y ∈ t k, Metric.ball y (1 / (k + 1 : ℝ))) ∪ C k)ᶜ) := by
        rw [hE_def, compl_iInter]
    _ ≤ ∑' k, μ n (((⋃ y ∈ t k, Metric.ball y (1 / (k + 1 : ℝ))) ∪ C k)ᶜ) :=
        measure_iUnion_le _
    _ ≤ ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (Real.exp (-(n * ℓ))) :=
        ENNReal.tsum_le_tsum fun k => hbd k n
    _ = ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
        rw [ENNReal.tsum_mul_right, tsum_inv_two_pow_succ, one_mul]

/-- **Superexponential tightness.** Let `μₙ` be finite measures on a Polish space satisfying a
large deviation principle with a good rate function. Then for every `ℓ : ℝ` there is a compact
set `K` with `μₙ(Kᶜ) ≤ exp (-n ℓ)` for every `n`.

Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University,
Spring 2010, Section 2, Theorem 2.4 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf). -/
theorem exists_isCompact_measure_compl_le {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : ℕ → Measure X}
    [∀ n, IsFiniteMeasure (μ n)] {I : X → ℝ≥0∞} (hμ : SatisfiesLDP μ I)
    (hI : IsGoodRateFunction I) (ℓ : ℝ) :
    ∃ K : Set X, IsCompact K ∧ ∀ n : ℕ, μ n Kᶜ ≤ ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact exists_isCompact_measure_compl_le_of_metric hμ hI ℓ

end Tightness

section Product

/-- **Eventual comparison of exponential rates.** If `M < ∞` and `q' < q`, then eventually
`M · exp (-n q) ≤ exp (-n q')`. -/
theorem eventually_mul_ofReal_exp_le {M : ℝ≥0∞} (hM : M ≠ ⊤) {q q' : ℝ} (hq : q' < q) :
    ∀ᶠ n : ℕ in atTop, M * ENNReal.ofReal (Real.exp (-(n * q))) ≤
      ENNReal.ofReal (Real.exp (-(n * q'))) := by
  have : Tendsto (fun n : ℕ => (n : ℝ) * (q - q')) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)
  filter_upwards [this.eventually_ge_atTop M.toReal] with n hn
  calc M * ENNReal.ofReal (Real.exp (-(n * q)))
      = ENNReal.ofReal (M.toReal * Real.exp (-(n * q))) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM]
    _ ≤ ENNReal.ofReal (Real.exp (-(n * q'))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc M.toReal * Real.exp (-(n * q))
            ≤ Real.exp (n * (q - q')) * Real.exp (-(n * q)) := by
              gcongr
              linarith [Real.add_one_le_exp (n * (q - q'))]
          _ = Real.exp (-(n * q')) := by
              rw [← Real.exp_add]
              ring_nf

/-- **Local LDP upper bound near a point.** If probability measures `μₙ` on a regular space
satisfy an LDP with rate function `I` and `q < I x`, then some open neighbourhood `U` of `x`
has `μₙ(U) ≤ exp (-n q)` eventually. -/
theorem exists_isOpen_eventually_measure_le {X : Type*} [TopologicalSpace X] [RegularSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : ℕ → Measure X}
    [∀ n, IsProbabilityMeasure (μ n)] {I : X → ℝ≥0∞} (hμ : SatisfiesLDP μ I) {x : X} {q : ℝ}
    (hq : (q : EReal) < I x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ n : ℕ in atTop, μ n U ≤ ENNReal.ofReal (Real.exp (-(n * q))) := by
  by_cases hq0 : q < 0
  · refine ⟨univ, isOpen_univ, mem_univ _, Eventually.of_forall fun n => ?_⟩
    rw [measure_univ]
    refine ENNReal.one_le_ofReal.2 (Real.one_le_exp ?_)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  push Not at hq0
  obtain ⟨q', hqq', hq'I⟩ := EReal.lt_iff_exists_real_btwn.1 hq
  rw [EReal.coe_lt_coe_iff] at hqq'
  have hq'0 : 0 ≤ q' := by linarith
  have hcoe : ((ENNReal.ofReal q' : ℝ≥0∞) : EReal) = q' := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hq'0]
  have hxU1 : ENNReal.ofReal q' < I x := by
    rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, hcoe]
    exact hq'I
  have hU1 : I ⁻¹' Ioi (ENNReal.ofReal q') ∈ 𝓝 x :=
    (hμ.isRateFunction.lowerSemicontinuous.isOpen_preimage _).mem_nhds hxU1
  obtain ⟨t, ht, htc, htU⟩ := exists_mem_nhds_isClosed_subset hU1
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  have hinf : -(⨅ y ∈ t, (I y : EReal)) ≤ ((-q' : ℝ) : EReal) := by
    rw [EReal.neg_le, EReal.coe_neg, neg_neg]
    refine le_iInf₂ fun y hy => ?_
    rw [← hcoe]
    exact (EReal.coe_ennreal_lt_coe_ennreal_iff.2 (htU hy)).le
  have hlim : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n t)) atTop <
      ((-q : ℝ) : EReal) :=
    (hμ.upper_bound t htc).trans_lt
      (hinf.trans_lt (by exact_mod_cast (show -q' < -q by linarith)))
  filter_upwards [eventually_lt_of_limsup_lt hlim, eventually_gt_atTop 0] with n hn hn0
  refine (measure_mono interior_subset).trans ?_
  have := (inv_mul_log_le_coe_iff hn0 _ _).1 hn.le
  rwa [mul_neg] at this

/-- **Local LDP lower bound near a point.** If `μₙ` satisfies an LDP with rate function `I`,
`U` is an open neighbourhood of `x`, `I x < ∞` and `ε > 0`, then eventually
`exp (n (-I x - ε)) ≤ μₙ(U)`. -/
theorem eventually_ofReal_exp_le_measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : ℕ → Measure X} {I : X → ℝ≥0∞} (hμ : SatisfiesLDP μ I)
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) (hIx : I x ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (n * (-(I x).toReal - ε))) ≤ μ n U := by
  have hr : ((I x : ℝ≥0∞) : EReal) = ((I x).toReal : EReal) :=
    (EReal.coe_ennreal_toReal hIx).symm
  have hinf : (⨅ y ∈ U, (I y : EReal)) ≤ (I x).toReal := hr ▸ iInf₂_le x hx
  have hs : ((-(I x).toReal - ε : ℝ) : EReal) <
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n U)) atTop := by
    refine lt_of_lt_of_le ?_ (hμ.lower_bound U hU)
    calc ((-(I x).toReal - ε : ℝ) : EReal) < ((-(I x).toReal : ℝ) : EReal) := by
          exact_mod_cast (show -(I x).toReal - ε < -(I x).toReal by linarith)
      _ = -((I x).toReal : EReal) := by rw [EReal.coe_neg]
      _ ≤ -(⨅ y ∈ U, (I y : EReal)) := EReal.neg_le_neg_iff.2 hinf
  filter_upwards [eventually_lt_of_lt_liminf hs, eventually_gt_atTop 0] with n hn hn0
  exact (coe_le_inv_mul_log_iff hn0 _ _).1 hn.le

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The product rate function is good.** If `I` and `J` are good rate functions on `X` and
`Y`, then `(x, y) ↦ I x + J y` is a good rate function on `X × Y`. -/
theorem isGoodRateFunction_prod {I : X → ℝ≥0∞} {J : Y → ℝ≥0∞} (hI : IsGoodRateFunction I)
    (hJ : IsGoodRateFunction J) : IsGoodRateFunction (fun z : X × Y => I z.1 + J z.2) := by
  have hlsc : LowerSemicontinuous (fun z : X × Y => I z.1 + J z.2) :=
    (hI.lowerSemicontinuous.comp continuous_fst).add (hJ.lowerSemicontinuous.comp continuous_snd)
  refine ⟨⟨hlsc⟩, fun a => ?_⟩
  refine ((hI.isCompact_levelSet a).prod (hJ.isCompact_levelSet a)).of_isClosed_subset
    (hlsc.isClosed_preimage _) fun z hz => ?_
  have hz' : I z.1 + J z.2 ≤ ENNReal.ofReal a := hz
  exact ⟨le_trans le_self_add hz', le_trans le_add_self hz'⟩

variable [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopologyEither X Y] {μ : ℕ → Measure X} {ν : ℕ → Measure Y}
  [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
  {I : X → ℝ≥0∞} {J : Y → ℝ≥0∞}

omit [SecondCountableTopologyEither X Y] in
/-- **Local product upper bound.** If `μₙ`, `νₙ` satisfy LDPs with rate functions `I`, `J` on
regular spaces and `q < I x + J y`, then some open neighbourhood `N` of `(x, y)` has
`(μₙ × νₙ)(N) ≤ exp (-n q)` eventually. -/
theorem exists_isOpen_eventually_prod_le [RegularSpace X] [RegularSpace Y]
    (hμ : SatisfiesLDP μ I) (hν : SatisfiesLDP ν J) (z : X × Y) {q : ℝ}
    (hq : (q : EReal) < ((I z.1 + J z.2 : ℝ≥0∞) : EReal)) :
    ∃ N : Set (X × Y), IsOpen N ∧ z ∈ N ∧
      ∀ᶠ n : ℕ in atTop, (μ n).prod (ν n) N ≤ ENNReal.ofReal (Real.exp (-(n * q))) := by
  obtain ⟨q₁, q₂, h₁, h₂, hsum⟩ : ∃ q₁ q₂ : ℝ, (q₁ : EReal) < I z.1 ∧ (q₂ : EReal) < J z.2 ∧
      q₁ + q₂ = q := by
    have hneg : ((-1 : ℝ) : EReal) < 0 := by exact_mod_cast (show (-1 : ℝ) < 0 by norm_num)
    by_cases hI : I z.1 = ⊤
    · exact ⟨q + 1, -1, by rw [hI, EReal.coe_ennreal_top]; exact EReal.coe_lt_top _,
        hneg.trans_le (EReal.coe_ennreal_nonneg _), by ring⟩
    by_cases hJ : J z.2 = ⊤
    · exact ⟨-1, q + 1, hneg.trans_le (EReal.coe_ennreal_nonneg _),
        by rw [hJ, EReal.coe_ennreal_top]; exact EReal.coe_lt_top _, by ring⟩
    rw [EReal.coe_ennreal_add, ← EReal.coe_ennreal_toReal hI, ← EReal.coe_ennreal_toReal hJ,
      ← EReal.coe_add, EReal.coe_lt_coe_iff] at hq
    refine ⟨(I z.1).toReal - ((I z.1).toReal + (J z.2).toReal - q) / 2,
      (J z.2).toReal - ((I z.1).toReal + (J z.2).toReal - q) / 2, ?_, ?_, by ring⟩
    · rw [← EReal.coe_ennreal_toReal hI, EReal.coe_lt_coe_iff]
      linarith
    · rw [← EReal.coe_ennreal_toReal hJ, EReal.coe_lt_coe_iff]
      linarith
  obtain ⟨U, hU, hxU, hUev⟩ := exists_isOpen_eventually_measure_le hμ h₁
  obtain ⟨V, hV, hyV, hVev⟩ := exists_isOpen_eventually_measure_le hν h₂
  refine ⟨U ×ˢ V, hU.prod hV, ⟨hxU, hyV⟩, ?_⟩
  filter_upwards [hUev, hVev] with n h1 h2
  rw [Measure.prod_prod]
  calc μ n U * ν n V
      ≤ ENNReal.ofReal (Real.exp (-(n * q₁))) * ENNReal.ofReal (Real.exp (-(n * q₂))) :=
        mul_le_mul' h1 h2
    _ = ENNReal.ofReal (Real.exp (-(n * q))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← hsum]
        ring_nf

omit [SecondCountableTopologyEither X Y] in
/-- **Product upper bound on a compact set.** If `D ⊆ X × Y` is compact and `q < I x + J y`
on `D`, then `(μₙ × νₙ)(D) ≤ M · exp (-n q)` eventually, for some finite constant `M`. -/
theorem exists_eventually_prod_le_of_isCompact [RegularSpace X] [RegularSpace Y]
    (hμ : SatisfiesLDP μ I) (hν : SatisfiesLDP ν J) {D : Set (X × Y)} (hD : IsCompact D)
    {q : ℝ} (hq : ∀ z ∈ D, (q : EReal) < ((I z.1 + J z.2 : ℝ≥0∞) : EReal)) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ᶠ n : ℕ in atTop, (μ n).prod (ν n) D ≤ M * ENNReal.ofReal (Real.exp (-(n * q))) := by
  refine hD.induction_on (p := fun s => ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).prod (ν n) s ≤ M * ENNReal.ofReal (Real.exp (-(n * q)))) ?_ ?_ ?_ ?_
  · exact ⟨0, ENNReal.zero_ne_top, Eventually.of_forall fun n => by simp⟩
  · rintro s t hst ⟨M, hM, h⟩
    exact ⟨M, hM, h.mono fun n hn => (measure_mono hst).trans hn⟩
  · rintro s t ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
    refine ⟨M₁ + M₂, ENNReal.add_ne_top.2 ⟨hM₁, hM₂⟩, (h₁.and h₂).mono fun n hn => ?_⟩
    exact (measure_union_le _ _).trans ((add_le_add hn.1 hn.2).trans_eq (add_mul _ _ _).symm)
  · intro z hz
    obtain ⟨N, hN, hzN, hev⟩ := exists_isOpen_eventually_prod_le hμ hν z (hq z hz)
    exact ⟨N, mem_nhdsWithin_of_mem_nhds (hN.mem_nhds hzN), 1, ENNReal.one_ne_top,
      hev.mono fun n hn => by rwa [one_mul]⟩

/-- **Product large deviation principle.** Let probability measures `μₙ` on a Polish space `X`
and `νₙ` on a Polish space `Y` satisfy large deviation principles with good rate functions `I`
and `J`. Then the product measures `μₙ × νₙ` satisfy a large deviation principle on `X × Y`
with rate function `(x, y) ↦ I x + J y`, which is good by `isGoodRateFunction_prod`.

Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University,
Spring 2010, Section 2, Theorem 2.6 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf). -/
theorem satisfiesLDP_prod [PolishSpace X] [PolishSpace Y] (hμ : SatisfiesLDP μ I)
    (hI : IsGoodRateFunction I) (hν : SatisfiesLDP ν J) (hJ : IsGoodRateFunction J) :
    SatisfiesLDP (fun n => (μ n).prod (ν n)) (fun z : X × Y => I z.1 + J z.2) := by
  refine ⟨(isGoodRateFunction_prod hI hJ).isRateFunction, fun W hW => ?_, fun W hW => ?_⟩
  · -- lower bound
    refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    rw [EReal.lt_neg_comm] at hb
    obtain ⟨z, hzW, hz⟩ : ∃ z ∈ W, ((I z.1 + J z.2 : ℝ≥0∞) : EReal) < -b := by
      rw [iInf_lt_iff] at hb
      obtain ⟨z, hz⟩ := hb
      rw [iInf_lt_iff] at hz
      obtain ⟨hzW, h⟩ := hz
      exact ⟨z, hzW, h⟩
    have hI' : I z.1 ≠ ⊤ := by
      intro h
      rw [h, top_add, EReal.coe_ennreal_top] at hz
      exact not_top_lt hz
    have hJ' : J z.2 ≠ ⊤ := by
      intro h
      rw [h, add_top, EReal.coe_ennreal_top] at hz
      exact not_top_lt hz
    rw [EReal.coe_ennreal_add, ← EReal.coe_ennreal_toReal hI', ← EReal.coe_ennreal_toReal hJ',
      ← EReal.coe_add, EReal.lt_neg_comm, ← EReal.coe_neg] at hz
    obtain ⟨t, hbt, htz⟩ := EReal.lt_iff_exists_real_btwn.1 hz
    rw [EReal.coe_lt_coe_iff] at htz
    refine hbt.le.trans ?_
    set ε := (-((I z.1).toReal + (J z.2).toReal) - t) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := isOpen_prod_iff.1 hW z.1 z.2 hzW
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ofReal_exp_le_measure hμ hU hxU hI' hε,
      eventually_ofReal_exp_le_measure hν hV hyV hJ' hε, eventually_gt_atTop 0]
      with n h1 h2 hn0
    rw [coe_le_inv_mul_log_iff hn0]
    calc ENNReal.ofReal (Real.exp (n * t))
        = ENNReal.ofReal (Real.exp (n * (-(I z.1).toReal - ε))) *
            ENNReal.ofReal (Real.exp (n * (-(J z.2).toReal - ε))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          rw [hε_def]
          ring
      _ ≤ μ n U * ν n V := mul_le_mul' h1 h2
      _ = (μ n).prod (ν n) (U ×ˢ V) := (Measure.prod_prod U V).symm
      _ ≤ (μ n).prod (ν n) W := measure_mono hUV
  · -- upper bound
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    rw [EReal.neg_lt_comm] at hc
    obtain ⟨q, hcq, hqm⟩ := EReal.lt_iff_exists_real_btwn.1 hc
    obtain ⟨q', hcq', hq'q⟩ := EReal.lt_iff_exists_real_btwn.1 hcq
    rw [EReal.coe_lt_coe_iff] at hq'q
    have hq'c : ((-q' : ℝ) : EReal) ≤ c := by
      rw [EReal.coe_neg]
      exact (EReal.neg_lt_comm.1 hcq').le
    refine le_trans ?_ hq'c
    obtain ⟨A, hA, hAμ⟩ := exists_isCompact_measure_compl_le hμ hI q
    obtain ⟨B, hB, hBν⟩ := exists_isCompact_measure_compl_le hν hJ q
    obtain ⟨M, hM, hMev⟩ := exists_eventually_prod_le_of_isCompact hμ hν
      ((hA.prod hB).inter_left hW) (q := q) fun z hz =>
        hqm.trans_le (iInf₂_le (f := fun z (_ : z ∈ W) =>
          ((I z.1 + J z.2 : ℝ≥0∞) : EReal)) z hz.1)
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hMev, eventually_mul_ofReal_exp_le (ENNReal.add_ne_top.2 ⟨hM,
      (by simp : (2 : ℝ≥0∞) ≠ ⊤)⟩) hq'q, eventually_gt_atTop 0] with n hn hfin hn0
    rw [inv_mul_log_le_coe_iff hn0, mul_neg]
    calc (μ n).prod (ν n) W
        ≤ (μ n).prod (ν n) (W ∩ A ×ˢ B) + (μ n).prod (ν n) (A ×ˢ B)ᶜ := by
          refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
          by_cases hzC : z ∈ A ×ˢ B
          · exact Or.inl ⟨hz, hzC⟩
          · exact Or.inr hzC
      _ ≤ M * ENNReal.ofReal (Real.exp (-(n * q))) +
            2 * ENNReal.ofReal (Real.exp (-(n * q))) := by
          refine add_le_add hn ?_
          rw [compl_prod_eq_union]
          refine (measure_union_le _ _).trans ?_
          rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one,
            one_mul, two_mul]
          exact add_le_add (hAμ n) (hBν n)
      _ = (M + 2) * ENNReal.ofReal (Real.exp (-(n * q))) := (add_mul _ _ _).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(n * q'))) := hfin

end Product

end MathlibExt.Probability.LDPProduct
