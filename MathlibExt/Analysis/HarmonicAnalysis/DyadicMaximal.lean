/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Dyadic maximal function and Calderón–Zygmund decomposition on the real line

The standard dyadic intervals of level `k ∈ ℤ` are `[m 2^{-k}, (m + 1) 2^{-k})`, `m ∈ ℤ`
(the case `d = 1` of the dyadic cubes of T. Hytönen, *Dyadic analysis and weights*, lecture notes,
University of Helsinki, version of 2 May 2014, §1.A). The level-`k` interval containing `x` has
index `⌊x 2^k⌋`, so membership, nesting and the stopping-time argument reduce to integer floors.

* `dyadicAverage k f x` is the average of `‖f‖ₑ` over the level-`k` interval containing `x`,
  written with Mathlib's `laverage`, and `dyadicMaximalFunction f x` is its supremum over `k`.
* `mul_volume_lt_dyadicMaximalFunction_le`: `λ |{M_d f > λ}| ≤ ∫_{M_d f > λ} ‖f‖`, for every
  function `f` and every `λ`, with no integrability hypothesis.
* `ae_tendsto_setAverage_dyadicInterval`: the dyadic Lebesgue differentiation theorem for
  locally integrable Banach-valued `f`, from `IsUnifLocDoublingMeasure.ae_tendsto_average`.
* `ae_tendsto_dyadicAverage`: its extended-real form for `‖f‖ₑ`, `f` integrable, obtained from
  Mathlib's Vitali-family differentiation theorem for doubling measures
  (`VitaliFamily.ae_tendsto_lintegral_div` and
  `IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt`).
* `calderon_zygmund`: the dyadic Calderón–Zygmund decomposition at height `c`, in terms of
  stopping levels (`IsStoppingLevel`).
* `lintegral_rpow_dyadicMaximalFunction_le`: `‖M_d f‖_p ≤ p / (p - 1) ‖f‖_p` for `1 < p < ∞`,
  from the Doob-type inequality, Hölder's inequality, and a Marcinkiewicz bound with constant
  `2^p p / (p - 1)` that supplies the finiteness needed to divide.

Mathlib has no Hardy–Littlewood maximal function; the averages here are Mathlib's `laverage`
and the differentiation theorem is Mathlib's, so nothing is redefined.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-- **Dyadic interval.** The dyadic interval of level `k ∈ ℤ` and index `m ∈ ℤ` is
`[m 2^{-k}, (m + 1) 2^{-k})`; for fixed `k` these intervals partition `ℝ`, and each level-`k`
interval is the disjoint union of two level-`(k + 1)` intervals (T. Hytönen, *Dyadic analysis and
weights*, lecture notes, University of Helsinki, version of 2 May 2014, §1.A, the
collection `D_k` with `d = 1`). -/
noncomputable def dyadicInterval (k m : ℤ) : Set ℝ := Ico ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k)

/-- **Dyadic index.** The index `⌊x 2^k⌋` of the level-`k` dyadic interval that contains `x`
(`mem_dyadicInterval_iff`). -/
noncomputable def dyadicIndex (k : ℤ) (x : ℝ) : ℤ := ⌊x * 2 ^ k⌋

theorem mem_dyadicInterval_iff {k m : ℤ} {x : ℝ} :
    x ∈ dyadicInterval k m ↔ dyadicIndex k x = m := by
  have h2 : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  rw [dyadicIndex, Int.floor_eq_iff, dyadicInterval, mem_Ico, div_le_iff₀ h2, lt_div_iff₀ h2]

theorem dyadicInterval_eq_preimage (k m : ℤ) :
    dyadicInterval k m = dyadicIndex k ⁻¹' {m} := by
  ext x; simp [mem_dyadicInterval_iff]

theorem measurable_dyadicIndex (k : ℤ) : Measurable (dyadicIndex k) :=
  Int.measurable_floor.comp (measurable_id.mul_const _)

theorem measurableSet_dyadicInterval (k m : ℤ) : MeasurableSet (dyadicInterval k m) :=
  measurableSet_Ico

theorem volume_dyadicInterval (k m : ℤ) :
    volume (dyadicInterval k m) = ENNReal.ofReal ((2 : ℝ) ^ k)⁻¹ := by
  rw [dyadicInterval, Real.volume_Ico]
  congr 1
  field_simp
  ring

theorem volume_dyadicInterval_pos (k m : ℤ) : 0 < volume (dyadicInterval k m) := by
  rw [volume_dyadicInterval]; simp [zpow_pos (two_pos : (0 : ℝ) < 2) k]

theorem volume_dyadicInterval_ne_top (k m : ℤ) : volume (dyadicInterval k m) ≠ ∞ := by
  rw [volume_dyadicInterval]; exact ENNReal.ofReal_ne_top

/-- **Nesting of dyadic intervals.** For `j ≤ k`, the level-`j` index of `x` is the level-`k`
index divided (with floor) by `2^{k - j}`; in particular two points in the same level-`k`
interval lie in the same level-`j` interval. -/
theorem dyadicIndex_of_le {j k : ℤ} (hjk : j ≤ k) (x : ℝ) :
    dyadicIndex j x = dyadicIndex k x / ((2 : ℕ) ^ (k - j).toNat : ℕ) := by
  rw [dyadicIndex, dyadicIndex, ← Int.floor_div_natCast]
  congr 1
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = j + n := ⟨(k - j).toNat, by omega⟩
  have hn : (j + (n : ℤ) - j).toNat = n := by omega
  rw [hn, zpow_add₀ two_ne_zero, zpow_natCast]
  push_cast
  field_simp

theorem dyadicIndex_eq_of_le {j k : ℤ} (hjk : j ≤ k) {x y : ℝ}
    (h : dyadicIndex k x = dyadicIndex k y) : dyadicIndex j x = dyadicIndex j y := by
  rw [dyadicIndex_of_le hjk x, dyadicIndex_of_le hjk y, h]

variable {E : Type*} [ENorm E]

/-- **Dyadic average.** The average `|I|⁻¹ ∫_I ‖f‖` of `‖f‖ₑ` over the level-`k` dyadic interval
`I` containing `x`, as an extended nonnegative real (Mathlib's set `laverage`). -/
noncomputable def dyadicAverage (k : ℤ) (f : ℝ → E) (x : ℝ) : ℝ≥0∞ :=
  ⨍⁻ y in dyadicInterval k (dyadicIndex k x), ‖f y‖ₑ ∂volume

/-- **Dyadic maximal function.** `M_d f(x) = sup_k |I_k(x)|⁻¹ ∫_{I_k(x)} ‖f‖`, the supremum of the
averages of `‖f‖ₑ` over all dyadic intervals that contain `x` (T. Hytönen, *Dyadic analysis and
weights*, lecture notes, University of Helsinki, version of 2 May 2014, (1.4), with
`d = 1`). -/
noncomputable def dyadicMaximalFunction (f : ℝ → E) (x : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℤ, dyadicAverage k f x

theorem dyadicAverage_congr {k : ℤ} (f : ℝ → E) {x y : ℝ}
    (h : dyadicIndex k x = dyadicIndex k y) : dyadicAverage k f x = dyadicAverage k f y := by
  rw [dyadicAverage, dyadicAverage, h]

theorem measurable_dyadicAverage (k : ℤ) (f : ℝ → E) : Measurable (dyadicAverage k f) := by
  have : dyadicAverage k f =
      (fun m : ℤ => ⨍⁻ y in dyadicInterval k m, ‖f y‖ₑ ∂volume) ∘ dyadicIndex k := rfl
  rw [this]
  exact (measurable_of_countable _).comp (measurable_dyadicIndex k)

theorem measurable_dyadicMaximalFunction (f : ℝ → E) :
    Measurable (dyadicMaximalFunction f) :=
  Measurable.iSup fun k => measurable_dyadicAverage k f

theorem mul_volume_preimage_le_lintegral {f : ℝ → E} {k : ℤ} {T : Set ℤ} {c : ℝ≥0∞}
    (hT : ∀ m ∈ T, c < ⨍⁻ y in dyadicInterval k m, ‖f y‖ₑ ∂volume) :
    c * volume (dyadicIndex k ⁻¹' T) ≤ ∫⁻ y in dyadicIndex k ⁻¹' T, ‖f y‖ₑ := by
  have hU : dyadicIndex k ⁻¹' T = ⋃ m ∈ T, dyadicInterval k m := by
    ext x; simp [mem_dyadicInterval_iff]
  have hd : T.PairwiseDisjoint (dyadicInterval k) := by
    intro m _ m' _ hmm'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [mem_dyadicInterval_iff] at hx hx'
    exact hmm' (hx.symm.trans hx')
  rw [hU, measure_biUnion T.to_countable hd (fun m _ => measurableSet_dyadicInterval k m),
    lintegral_biUnion T.to_countable (fun m _ => measurableSet_dyadicInterval k m) hd,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun m => ?_
  have h := (hT m m.2).le
  rwa [setLAverage_eq, ENNReal.le_div_iff_mul_le (Or.inl (volume_dyadicInterval_pos k m).ne')
    (Or.inl (volume_dyadicInterval_ne_top k m))] at h

/-- **Stopping-time estimate on finitely many levels.** For levels `a ≤ k ≤ b`, the set where
some level-`k` average exceeds `c` satisfies `c |E| ≤ ∫_E ‖f‖`: it is the disjoint union, over
`k`, of the points whose first level above `c` is `k`, and each such set is a union of level-`k`
intervals on which the average exceeds `c`. -/
theorem mul_volume_window_le (f : ℝ → E) (c : ℝ≥0∞) (a b : ℤ) :
    c * volume {x | ∃ k ∈ Finset.Icc a b, c < dyadicAverage k f x} ≤
      ∫⁻ y in {x | ∃ k ∈ Finset.Icc a b, c < dyadicAverage k f x}, ‖f y‖ₑ := by
  classical
  set S : ℤ → Set ℝ := fun k =>
    {x | c < dyadicAverage k f x ∧ ∀ j ∈ Finset.Ico a k, dyadicAverage j f x ≤ c} with hSdef
  have hU : {x | ∃ k ∈ Finset.Icc a b, c < dyadicAverage k f x} = ⋃ k ∈ Finset.Icc a b, S k := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, hSdef]
    constructor
    · rintro ⟨k, hk, hc⟩
      set F := (Finset.Icc a b).filter (fun j => c < dyadicAverage j f x)
      have hF : F.Nonempty := ⟨k, Finset.mem_filter.2 ⟨hk, hc⟩⟩
      have hmin := Finset.mem_filter.1 (Finset.min'_mem F hF)
      refine ⟨F.min' hF, hmin.1, hmin.2, fun j hj => ?_⟩
      by_contra hlt
      push Not at hlt
      have h1 := Finset.mem_Icc.1 hmin.1
      have h2 := Finset.mem_Ico.1 hj
      have hjF : j ∈ F := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h2.1, by omega⟩, hlt⟩
      have := F.min'_le j hjF
      omega
    · rintro ⟨k, hk, hc, -⟩
      exact ⟨k, hk, hc⟩
  have hd : (↑(Finset.Icc a b) : Set ℤ).PairwiseDisjoint S := by
    intro k hk k' hk' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hx, hx'⟩ ⟨hy, hy'⟩
    have hk1 := Finset.mem_Icc.1 hk
    have hk2 := Finset.mem_Icc.1 hk'
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd (hy' k (Finset.mem_Ico.2 ⟨hk1.1, h⟩)) (not_le.2 hx)
    · exact absurd (hx' k' (Finset.mem_Ico.2 ⟨hk2.1, h⟩)) (not_le.2 hy)
  have hS : ∀ k, S k = dyadicIndex k ⁻¹' (dyadicIndex k '' S k) := by
    intro k
    refine (subset_preimage_image _ _).antisymm ?_
    rintro y ⟨x, ⟨hx, hx'⟩, hxy⟩
    have hj : ∀ j ≤ k, dyadicAverage j f y = dyadicAverage j f x := fun j hj =>
      dyadicAverage_congr f (dyadicIndex_eq_of_le hj hxy.symm)
    refine ⟨by rw [hj k le_rfl]; exact hx, fun j hjm => ?_⟩
    rw [hj j (Finset.mem_Ico.1 hjm).2.le]
    exact hx' j hjm
  have hmeas : ∀ k, MeasurableSet (S k) := fun k => by
    rw [hS k]; exact measurable_dyadicIndex k (MeasurableSet.of_discrete)
  rw [hU, measure_biUnion_finset hd (fun k _ => hmeas k),
    lintegral_biUnion_finset hd (fun k _ => hmeas k), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [hS k]
  refine mul_volume_preimage_le_lintegral ?_
  rintro m ⟨x, ⟨hx, -⟩, rfl⟩
  exact hx

/-- **Weak type (1,1) of the dyadic maximal function, localized form.** For every function
`f : ℝ → E` and every `c`, `c |{M_d f > c}| ≤ ∫_{M_d f > c} ‖f‖`. This is the sharper bound
obtained in the proof of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of
Helsinki, version of 2 May 2014, Proposition 1.5 (case `d = 1`), here without the
hypothesis `f ∈ L¹`: the levels are truncated to `[-N, N]` and `N → ∞`. -/
theorem mul_volume_lt_dyadicMaximalFunction_le (f : ℝ → E) (c : ℝ≥0∞) :
    c * volume {x | c < dyadicMaximalFunction f x} ≤
      ∫⁻ y in {x | c < dyadicMaximalFunction f x}, ‖f y‖ₑ := by
  set W : ℕ → Set ℝ := fun N =>
    {x | ∃ k ∈ Finset.Icc (-(N : ℤ)) N, c < dyadicAverage k f x} with hW
  have hU : {x | c < dyadicMaximalFunction f x} = ⋃ N, W N := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, hW, dyadicMaximalFunction, lt_iSup_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k.natAbs, k, Finset.mem_Icc.2 ⟨by omega, by omega⟩, hk⟩
    · rintro ⟨N, k, -, hk⟩
      exact ⟨k, hk⟩
  have hmono : Monotone W := by
    intro N N' hNN' x hx
    obtain ⟨k, hk, hc⟩ := hx
    have := Finset.mem_Icc.1 hk
    exact ⟨k, Finset.mem_Icc.2 ⟨by omega, by omega⟩, hc⟩
  rw [hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun N => (mul_volume_window_le f c (-(N : ℤ)) N).trans ?_
  exact lintegral_mono_set (subset_iUnion W N)

/-- **Weak type (1,1) of the dyadic maximal function.** For every `f : ℝ → E` and every `c`,
`c |{M_d f > c}| ≤ ∫ ‖f‖` (T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of
Helsinki, version of 2 May 2014, Proposition 1.5, case `d = 1`; no integrability
hypothesis is needed since the right-hand side may be infinite). -/
theorem dyadicMaximalFunction_mul_volume_le_lintegral (f : ℝ → E) (c : ℝ≥0∞) :
    c * volume {x | c < dyadicMaximalFunction f x} ≤ ∫⁻ y, ‖f y‖ₑ :=
  (mul_volume_lt_dyadicMaximalFunction_le f c).trans (setLIntegral_le_lintegral _ _)

theorem dyadicInterval_ae_eq_closedBall (k m : ℤ) :
    dyadicInterval k m =ᵐ[volume]
      Metric.closedBall (((m : ℝ) + 1 / 2) / 2 ^ k) (((2 : ℝ) ^ k)⁻¹ / 2) := by
  have h2 : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  rw [Real.closedBall_eq_Icc, dyadicInterval]
  have e1 : ((m : ℝ) + 1 / 2) / 2 ^ k - ((2 : ℝ) ^ k)⁻¹ / 2 = (m : ℝ) / 2 ^ k := by
    field_simp; ring
  have e2 : ((m : ℝ) + 1 / 2) / 2 ^ k + ((2 : ℝ) ^ k)⁻¹ / 2 = ((m : ℝ) + 1) / 2 ^ k := by
    field_simp; ring
  rw [e1, e2]
  exact Ico_ae_eq_Icc

/-- **Dyadic Lebesgue differentiation theorem.** If `‖f‖ₑ` is a.e. measurable and
`∫ ‖f‖ < ∞`, then for almost every `x` the averages of `‖f‖ₑ` over the dyadic intervals of level
`n` containing `x` tend to `‖f(x)‖ₑ` as `n → ∞` (the dyadic case, for `‖f‖`, of
T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May
2014, Theorem 5.1). The proof applies Mathlib's differentiation theorem for the
Vitali family of a doubling measure to the closed intervals `[m 2^{-n}, (m + 1) 2^{-n}]`, which
differ from the dyadic intervals by a null set. -/
theorem ae_tendsto_dyadicAverage {f : ℝ → E} (hf : AEMeasurable (fun y => ‖f y‖ₑ))
    (hf' : ∫⁻ y, ‖f y‖ₑ ≠ ∞) :
    ∀ᵐ x, Tendsto (fun n : ℕ => dyadicAverage (n : ℤ) f x) atTop (𝓝 ‖f x‖ₑ) := by
  have hv := VitaliFamily.ae_tendsto_lintegral_div
    (IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1) hf hf'
  filter_upwards [hv] with x hx
  set w : ℕ → ℝ := fun n => ((dyadicIndex n x : ℝ) + 1 / 2) / 2 ^ (n : ℤ) with hw
  set δ : ℕ → ℝ := fun n => ((2 : ℝ) ^ (n : ℤ))⁻¹ / 2 with hδ
  have hδlim : Tendsto δ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n / 2) atTop (𝓝 (0 / 2)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).div_const 2
      rw [zero_div] at this
      refine this.congr fun n => ?_
      simp [hδ, zpow_natCast]
    · simp only [hδ, mem_Ioi]; positivity
  have hmem : ∀ᶠ n in atTop, x ∈ Metric.closedBall (w n) (1 * δ n) := by
    refine Eventually.of_forall fun n => ?_
    have hx' : x ∈ dyadicInterval n (dyadicIndex n x) := mem_dyadicInterval_iff.2 rfl
    have h2 : (0 : ℝ) < 2 ^ (n : ℤ) := zpow_pos two_pos _
    rw [dyadicInterval, mem_Ico] at hx'
    rw [one_mul, Real.closedBall_eq_Icc, mem_Icc]
    have e1 : w n - δ n = (dyadicIndex n x : ℝ) / 2 ^ (n : ℤ) := by
      simp only [hw, hδ]; field_simp; ring
    have e2 : w n + δ n = ((dyadicIndex n x : ℝ) + 1) / 2 ^ (n : ℤ) := by
      simp only [hw, hδ]; field_simp; ring
    rw [e1, e2]
    exact ⟨hx'.1, hx'.2.le⟩
  have := hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume w δ hδlim hmem)
  refine this.congr fun n => ?_
  have hae := dyadicInterval_ae_eq_closedBall (n : ℤ) (dyadicIndex n x)
  simp only [Function.comp_apply, hw, hδ]
  rw [dyadicAverage, setLAverage_eq, setLIntegral_congr hae, measure_congr hae]

/-- **Dyadic Lebesgue differentiation theorem for locally integrable functions.** For every
locally integrable `f : ℝ → F` with values in a real Banach space, for almost every `x` the
averages `⨍_{I_n(x)} f` over the level-`n` dyadic intervals containing `x` tend to `f x` as
`n → ∞` (T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki,
version of 2 May 2014, Theorem 5.1, along dyadic intervals and with `d = 1`). The proof applies
Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average` to the closed intervals
`[m 2^{-n}, (m + 1) 2^{-n}]`, which differ from the dyadic intervals by a null set. -/
theorem ae_tendsto_setAverage_dyadicInterval {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → F} (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto (fun n : ℕ => ⨍ y in dyadicInterval n (dyadicIndex n x), f y) atTop
      (𝓝 (f x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf 1] with x hx
  set w : ℕ → ℝ := fun n => ((dyadicIndex n x : ℝ) + 1 / 2) / 2 ^ (n : ℤ) with hw
  set δ : ℕ → ℝ := fun n => ((2 : ℝ) ^ (n : ℤ))⁻¹ / 2 with hδ
  have hδlim : Tendsto δ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n / 2) atTop (𝓝 (0 / 2)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).div_const 2
      rw [zero_div] at this
      refine this.congr fun n => ?_
      simp [hδ, zpow_natCast]
    · simp only [hδ, mem_Ioi]; positivity
  have hmem : ∀ᶠ n in atTop, x ∈ Metric.closedBall (w n) (1 * δ n) := by
    refine Eventually.of_forall fun n => ?_
    have hx' : x ∈ dyadicInterval n (dyadicIndex n x) := mem_dyadicInterval_iff.2 rfl
    have h2 : (0 : ℝ) < 2 ^ (n : ℤ) := zpow_pos two_pos _
    rw [dyadicInterval, mem_Ico] at hx'
    rw [one_mul, Real.closedBall_eq_Icc, mem_Icc]
    have e1 : w n - δ n = (dyadicIndex n x : ℝ) / 2 ^ (n : ℤ) := by
      simp only [hw, hδ]; field_simp; ring
    have e2 : w n + δ n = ((dyadicIndex n x : ℝ) + 1) / 2 ^ (n : ℤ) := by
      simp only [hw, hδ]; field_simp; ring
    rw [e1, e2]
    exact ⟨hx'.1, hx'.2.le⟩
  refine (hx w δ hδlim hmem).congr fun n => ?_
  simp only [hw, hδ]
  exact setAverage_congr (dyadicInterval_ae_eq_closedBall _ _).symm

/-- **Pointwise domination by the dyadic maximal function.** Under the hypotheses of the dyadic
Lebesgue differentiation theorem, `‖f(x)‖ₑ ≤ M_d f(x)` for almost every `x`. -/
theorem ae_enorm_le_dyadicMaximalFunction {f : ℝ → E} (hf : AEMeasurable (fun y => ‖f y‖ₑ))
    (hf' : ∫⁻ y, ‖f y‖ₑ ≠ ∞) : ∀ᵐ x, ‖f x‖ₑ ≤ dyadicMaximalFunction f x := by
  filter_upwards [ae_tendsto_dyadicAverage hf hf'] with x hx
  exact le_of_tendsto' hx fun n => le_iSup (fun k : ℤ => dyadicAverage k f x) (n : ℤ)

/-- **Stopping level.** `k` is the stopping level of `x` at height `c` when the level-`k` average
around `x` exceeds `c` and every coarser average is at most `c`. The level-`k` interval around
`x` is then a maximal dyadic interval with average above `c`, as in the stopping-time argument
of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2
May 2014, Proposition 1.5. -/
def IsStoppingLevel (f : ℝ → E) (c : ℝ≥0∞) (x : ℝ) (k : ℤ) : Prop :=
  c < dyadicAverage k f x ∧ ∀ j < k, dyadicAverage j f x ≤ c

theorem IsStoppingLevel.unique {f : ℝ → E} {c : ℝ≥0∞} {x : ℝ} {k k' : ℤ}
    (h : IsStoppingLevel f c x k) (h' : IsStoppingLevel f c x k') : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h'.2 k hlt) (not_le.2 h.1)
  · exact absurd (h.2 k' hlt) (not_le.2 h'.1)

theorem IsStoppingLevel.of_mem {f : ℝ → E} {c : ℝ≥0∞} {x y : ℝ} {k : ℤ}
    (h : IsStoppingLevel f c x k) (hy : y ∈ dyadicInterval k (dyadicIndex k x)) :
    IsStoppingLevel f c y k := by
  rw [mem_dyadicInterval_iff] at hy
  have hj : ∀ j ≤ k, dyadicAverage j f y = dyadicAverage j f x := fun j hj =>
    dyadicAverage_congr f (dyadicIndex_eq_of_le hj hy)
  exact ⟨by rw [hj k le_rfl]; exact h.1, fun j hjk => by rw [hj j hjk.le]; exact h.2 j hjk⟩

theorem IsStoppingLevel.lt_dyadicMaximalFunction {f : ℝ → E} {c : ℝ≥0∞} {x : ℝ} {k : ℤ}
    (h : IsStoppingLevel f c x k) : c < dyadicMaximalFunction f x :=
  h.1.trans_le (le_iSup (fun j : ℤ => dyadicAverage j f x) k)

theorem dyadicInterval_subset_parent (k : ℤ) (x : ℝ) :
    dyadicInterval k (dyadicIndex k x) ⊆ dyadicInterval (k - 1) (dyadicIndex (k - 1) x) := by
  intro y hy
  rw [mem_dyadicInterval_iff] at hy ⊢
  exact dyadicIndex_eq_of_le (by omega) hy

theorem dyadicAverage_le_two_mul_parent (k : ℤ) (f : ℝ → E) (x : ℝ) :
    dyadicAverage k f x ≤ 2 * dyadicAverage (k - 1) f x := by
  simp only [dyadicAverage, setLAverage_eq]
  have hsub := dyadicInterval_subset_parent k x
  have hv : volume (dyadicInterval (k - 1) (dyadicIndex (k - 1) x)) =
      2 * volume (dyadicInterval k (dyadicIndex k x)) := by
    rw [volume_dyadicInterval, volume_dyadicInterval, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), zpow_sub₀ two_ne_zero, zpow_one]
    congr 1
    field_simp
  rw [hv, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.div_le_div_right (lintegral_mono_set hsub) _

theorem IsStoppingLevel.dyadicAverage_le_two_mul {f : ℝ → E} {c : ℝ≥0∞} {x : ℝ} {k : ℤ}
    (h : IsStoppingLevel f c x k) : dyadicAverage k f x ≤ 2 * c :=
  (dyadicAverage_le_two_mul_parent k f x).trans (by gcongr; exact h.2 (k - 1) (by omega))

theorem IsStoppingLevel.eq_or_disjoint {f : ℝ → E} {c : ℝ≥0∞} {x y : ℝ} {k k' : ℤ}
    (hx : IsStoppingLevel f c x k) (hy : IsStoppingLevel f c y k') :
    dyadicInterval k (dyadicIndex k x) = dyadicInterval k' (dyadicIndex k' y) ∨
      Disjoint (dyadicInterval k (dyadicIndex k x)) (dyadicInterval k' (dyadicIndex k' y)) := by
  by_cases hd : Disjoint (dyadicInterval k (dyadicIndex k x))
      (dyadicInterval k' (dyadicIndex k' y))
  · exact Or.inr hd
  · left
    obtain ⟨z, hzx, hzy⟩ := Set.not_disjoint_iff.1 hd
    have hkk : k = k' := (hx.of_mem hzx).unique (hy.of_mem hzy)
    subst hkk
    rw [mem_dyadicInterval_iff] at hzx hzy
    rw [← hzx, hzy]

theorem dyadicAverage_le_div (k : ℤ) (f : ℝ → E) (x : ℝ) :
    dyadicAverage k f x ≤ (∫⁻ y, ‖f y‖ₑ) / ENNReal.ofReal ((2 : ℝ) ^ k)⁻¹ := by
  rw [dyadicAverage, setLAverage_eq, volume_dyadicInterval]
  exact ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _

/-- **Existence of the stopping level.** If `∫ ‖f‖ < ∞`, `c ≠ 0` and `M_d f(x) > c`, then `x` has
a stopping level at height `c`: the averages around `x` are at most `2^k ∫ ‖f‖`, so the levels
whose average exceeds `c` are bounded below and have a least element. -/
theorem exists_isStoppingLevel {f : ℝ → E} {c : ℝ≥0∞} (hf : ∫⁻ y, ‖f y‖ₑ ≠ ∞) (hc : c ≠ 0)
    {x : ℝ} (hx : c < dyadicMaximalFunction f x) : ∃ k, IsStoppingLevel f c x k := by
  classical
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∫⁻ y, ‖f y‖ₑ) / c).toReal
    (by norm_num : (1 : ℝ) < 2)
  have hbdd : ∀ k, c < dyadicAverage k f x → -(n : ℤ) ≤ k := by
    intro k hk
    by_contra hlt
    push Not at hlt
    have h1 := hk.trans_le (dyadicAverage_le_div k f x)
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹ := inv_pos.2 (zpow_pos two_pos k)
    have hv0 : ENNReal.ofReal ((2 : ℝ) ^ k)⁻¹ ≠ 0 := by simpa using hpos
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl ENNReal.ofReal_ne_top), mul_comm,
      ← ENNReal.lt_div_iff_mul_lt (Or.inl hc) (Or.inr hv0)] at h1
    rw [ENNReal.ofReal_lt_iff_lt_toReal hpos.le (ENNReal.div_ne_top hf hc)] at h1
    have h2 : (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ k)⁻¹ := by
      rw [← zpow_neg, ← zpow_natCast]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hne : ∃ k, c < dyadicAverage k f x := by
    simpa [dyadicMaximalFunction, lt_iSup_iff] using hx
  obtain ⟨k, hk, hmin⟩ := Int.exists_least_of_bdd ⟨-(n : ℤ), hbdd⟩ hne
  refine ⟨k, hk, fun j hj => ?_⟩
  by_contra hlt
  exact absurd (hmin j (not_le.1 hlt)) (not_le.2 hj)

/-- **Calderón–Zygmund decomposition, dyadic form.** Let `‖f‖ₑ` be a.e. measurable with
`∫ ‖f‖ < ∞`, and `c ≠ 0`. Let `Ω = {M_d f > c}`. Then `c |Ω| ≤ ∫ ‖f‖`; `‖f(x)‖ₑ ≤ c` for almost
every `x ∉ Ω`; and every `x ∈ Ω` has a stopping level `k` whose interval `Q ∋ x` satisfies
`c < |Q|⁻¹ ∫_Q ‖f‖ ≤ 2c`, lies in `Ω`, and is the stopping interval of each of its points, so
that the stopping intervals partition `Ω` (`IsStoppingLevel.eq_or_disjoint`). This is the
construction in the proof of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of
Helsinki, version of 2 May 2014, Proposition 7.11, with `d = 1` (so `2^d = 2`).
The good and bad parts `g = f 1_{Ωᶜ} + ∑_Q ⟨f⟩_Q 1_Q`, `b = f - g` are not formed here; their
bounds follow from the stated properties. -/
theorem calderon_zygmund {f : ℝ → E} (hf : AEMeasurable (fun y => ‖f y‖ₑ))
    (hf' : ∫⁻ y, ‖f y‖ₑ ≠ ∞) {c : ℝ≥0∞} (hc : c ≠ 0) :
    c * volume {x | c < dyadicMaximalFunction f x} ≤ ∫⁻ y, ‖f y‖ₑ ∧
    (∀ᵐ x, dyadicMaximalFunction f x ≤ c → ‖f x‖ₑ ≤ c) ∧
    ∀ x, c < dyadicMaximalFunction f x → ∃ k, IsStoppingLevel f c x k ∧
      c < dyadicAverage k f x ∧ dyadicAverage k f x ≤ 2 * c ∧
      ∀ y ∈ dyadicInterval k (dyadicIndex k x),
        IsStoppingLevel f c y k ∧ c < dyadicMaximalFunction f y := by
  refine ⟨dyadicMaximalFunction_mul_volume_le_lintegral f c, ?_, fun x hx => ?_⟩
  · filter_upwards [ae_enorm_le_dyadicMaximalFunction hf hf'] with x hx hxc
    exact hx.trans hxc
  · obtain ⟨k, hk⟩ := exists_isStoppingLevel hf' hc hx
    exact ⟨k, hk, hk.1, hk.dyadicAverage_le_two_mul, fun y hy =>
      ⟨hk.of_mem hy, (hk.of_mem hy).lt_dyadicMaximalFunction⟩⟩

/-! ### Strong type `(p, p)` -/

theorem rpow_eq_lintegral_of_ne_top {a : ℝ≥0∞} (ha : a ≠ ∞) {q : ℝ} (hq : 0 < q) :
    a ^ q = ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t := by
  have hset : ∀ t ∈ Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t =
      (Iio a.toReal).indicator (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t := by
    intro t ht
    have : (t ∈ {t : ℝ | ENNReal.ofReal t < a}) ↔ t ∈ Iio a.toReal :=
      ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) ha
    by_cases h : t ∈ Iio a.toReal
    · rw [indicator_of_mem h, indicator_of_mem (this.2 h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (this.1 h'))]
  rw [setLIntegral_congr_fun measurableSet_Ioi hset, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := a)) with h0 | hpos
  · have ha0 : a = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff a).1 h0.symm with h | h
      · exact h
      · exact absurd h ha
    subst ha0
    simp [ENNReal.zero_rpow_of_pos hq]
  · have hint : IntegrableOn (fun t : ℝ => q * t ^ (q - 1)) (Ioo 0 a.toReal) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := q - 1) (by linarith)
        (a := 0) (b := a.toReal)).const_mul q
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpos.le] at this
      exact this
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpos.le,
        intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
      have hq1 : q - 1 + 1 = q := by ring
      rw [hq1, Real.zero_rpow hq.ne', sub_zero, mul_div_cancel₀ _ hq.ne',
        ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le, ENNReal.ofReal_toReal ha]
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
      exact mul_nonneg hq.le (Real.rpow_nonneg ht.1.le _)

theorem rpow_eq_lintegral (a : ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    a ^ q = ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t := by
  rcases eq_or_ne a ∞ with rfl | ha
  · rw [ENNReal.top_rpow_of_pos hq, eq_comm, eq_top_iff]
    have hn : ∀ n : ℕ, ((n : ℝ≥0∞)) ^ q ≤ ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | ENNReal.ofReal t < ∞}.indicator (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t := by
      intro n
      rw [rpow_eq_lintegral_of_ne_top (ENNReal.natCast_ne_top n) hq]
      have hsub : {t : ℝ | ENNReal.ofReal t < (n : ℝ≥0∞)} ⊆ {t : ℝ | ENNReal.ofReal t < ∞} :=
        fun t _ => ENNReal.ofReal_lt_top
      exact lintegral_mono fun t => indicator_le_indicator_of_subset hsub (fun _ => bot_le) t
    have h := ((ENNReal.continuous_rpow_const (y := q)).tendsto ⊤).comp
      ENNReal.tendsto_nat_nhds_top
    rw [ENNReal.top_rpow_of_pos hq] at h
    exact le_of_tendsto' h hn
  · exact rpow_eq_lintegral_of_ne_top ha hq


theorem dyadicAverage_le_indicator_add (k : ℤ) (f : ℝ → E) (s : ℝ≥0∞) (x : ℝ) :
    dyadicAverage k f x ≤
      dyadicAverage k ({y | s < ‖f y‖ₑ}.indicator fun y => ‖f y‖ₑ) x + s := by
  simp only [dyadicAverage, setLAverage_eq]
  set I := dyadicInterval k (dyadicIndex k x)
  have hle : ∫⁻ y in I, ‖f y‖ₑ ≤
      ∫⁻ y in I, (‖({y | s < ‖f y‖ₑ}.indicator fun y => ‖f y‖ₑ) y‖ₑ + s) := by
    refine lintegral_mono fun y => ?_
    by_cases h : s < ‖f y‖ₑ
    · rw [indicator_of_mem (show y ∈ {y | s < ‖f y‖ₑ} from h), enorm_eq_self]
      exact le_self_add
    · rw [indicator_of_notMem (show y ∉ {y | s < ‖f y‖ₑ} from h), enorm_zero, zero_add]
      exact not_lt.1 h
  rw [lintegral_add_right _ measurable_const, setLIntegral_const] at hle
  calc (∫⁻ y in I, ‖f y‖ₑ) / volume I
      ≤ ((∫⁻ y in I, ‖({y | s < ‖f y‖ₑ}.indicator fun y => ‖f y‖ₑ) y‖ₑ) + s * volume I) /
          volume I := ENNReal.div_le_div_right hle _
    _ = _ := by
      rw [ENNReal.add_div, ENNReal.mul_div_cancel_right (volume_dyadicInterval_pos _ _).ne'
        (volume_dyadicInterval_ne_top _ _)]

theorem volume_two_mul_lt_dyadicMaximalFunction_le (f : ℝ → E) {s : ℝ≥0∞} (hs0 : s ≠ 0)
    (hs : s ≠ ∞) :
    volume {x | 2 * s < dyadicMaximalFunction f x} ≤
      s⁻¹ * ∫⁻ y, {y | s < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ) y := by
  set g : ℝ → ℝ≥0∞ := {y | s < ‖f y‖ₑ}.indicator fun y => ‖f y‖ₑ with hg
  have hsub : {x | 2 * s < dyadicMaximalFunction f x} ⊆ {x | s < dyadicMaximalFunction g x} := by
    intro x hx
    simp only [mem_ofPred_eq, dyadicMaximalFunction, lt_iSup_iff] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    by_contra h
    push Not at h
    have h2 : dyadicAverage k g x + s ≤ s + s := by gcongr
    have := (dyadicAverage_le_indicator_add k f s x).trans h2
    rw [two_mul] at hk
    exact absurd (hk.trans_le this) (lt_irrefl _)
  have hweak := dyadicMaximalFunction_mul_volume_le_lintegral g s
  simp only [enorm_eq_self] at hweak
  calc volume {x | 2 * s < dyadicMaximalFunction f x}
      ≤ volume {x | s < dyadicMaximalFunction g x} := measure_mono hsub
    _ = s⁻¹ * (s * volume {x | s < dyadicMaximalFunction g x}) := by
      rw [ENNReal.inv_mul_cancel_left hs0 hs]
    _ ≤ s⁻¹ * ∫⁻ y, g y := by gcongr


theorem lintegral_rpow_eq_lintegral_volume_mul {M : ℝ → ℝ≥0∞} (hM : Measurable M) {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ x, M x ^ p =
      ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < M x} *
        ENNReal.ofReal (p * t ^ (p - 1)) := by
  have hFm : Measurable fun t : ℝ => ENNReal.ofReal (p * t ^ (p - 1)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  simp_rw [rpow_eq_lintegral (M _) hp]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun t => ?_
    have : (fun x => {t : ℝ | ENNReal.ofReal t < M x}.indicator
        (fun t => ENNReal.ofReal (p * t ^ (p - 1))) t) =
        {x | ENNReal.ofReal t < M x}.indicator (fun _ => ENNReal.ofReal (p * t ^ (p - 1))) := by
      ext x; simp [Set.indicator_apply]
    rw [this, lintegral_indicator_const (measurableSet_lt measurable_const hM), mul_comm]
  · apply Measurable.aemeasurable
    have hs : MeasurableSet {z : ℝ × ℝ | ENNReal.ofReal z.2 < M z.1} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hM.comp measurable_fst)
    have : Function.uncurry (fun x t => {t : ℝ | ENNReal.ofReal t < M x}.indicator
        (fun t => ENNReal.ofReal (p * t ^ (p - 1))) t) =
        {z : ℝ × ℝ | ENNReal.ofReal z.2 < M z.1}.indicator
          (fun z => ENNReal.ofReal (p * z.2 ^ (p - 1))) := by
      ext ⟨x, t⟩; simp [Set.indicator_apply]
    rw [this]
    exact (hFm.comp measurable_snd).indicator hs

theorem volume_mul_le_lintegral_split (f : ℝ → E) {p t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < dyadicMaximalFunction f x} *
        ENNReal.ofReal (p * t ^ (p - 1)) ≤
      ∫⁻ x, {x | ENNReal.ofReal (t / 2) < ‖f x‖ₑ}.indicator (fun y => ‖f y‖ₑ) x *
        ENNReal.ofReal (2 * p * t ^ (p - 2)) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have hs0 : ENNReal.ofReal (t / 2) ≠ 0 := by simpa using ht2
  have h2s : ENNReal.ofReal t = 2 * ENNReal.ofReal (t / 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  have hw := volume_two_mul_lt_dyadicMaximalFunction_le f hs0 ENNReal.ofReal_ne_top
  rw [← h2s] at hw
  have hinv : (ENNReal.ofReal (t / 2))⁻¹ * ENNReal.ofReal (p * t ^ (p - 1)) =
      ENNReal.ofReal (2 * p * t ^ (p - 2)) := by
    rw [← ENNReal.ofReal_inv_of_pos ht2, ← ENNReal.ofReal_mul (inv_nonneg.2 ht2.le)]
    congr 1
    have : t ^ (p - 1) = t ^ (p - 2) * t := by
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
    rw [this]
    have ht0 : t ≠ 0 := (ne_of_lt ht).symm
    field_simp
  calc volume {x | ENNReal.ofReal t < dyadicMaximalFunction f x} *
        ENNReal.ofReal (p * t ^ (p - 1))
      ≤ ((ENNReal.ofReal (t / 2))⁻¹ *
          ∫⁻ y, {y | ENNReal.ofReal (t / 2) < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ) y) *
          ENNReal.ofReal (p * t ^ (p - 1)) := by gcongr
    _ = (∫⁻ y, {y | ENNReal.ofReal (t / 2) < ‖f y‖ₑ}.indicator (fun y => ‖f y‖ₑ) y) *
          ENNReal.ofReal (2 * p * t ^ (p - 2)) := by
        rw [mul_comm (ENNReal.ofReal (t / 2))⁻¹, mul_assoc, hinv]
    _ = _ := (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm

theorem lintegral_indicator_mul_le (a : ℝ≥0∞) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal (t / 2) < a}.indicator (fun _ => a) t *
        ENNReal.ofReal (2 * p * t ^ (p - 2)) ≤
      ENNReal.ofReal (2 ^ p * p / (p - 1)) * a ^ p := by
  have hp1 : 0 < p - 1 := by linarith
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      {t : ℝ | ENNReal.ofReal (t / 2) < a}.indicator (fun _ => a) t *
        ENNReal.ofReal (2 * p * t ^ (p - 2)) = (a * ENNReal.ofReal (2 * p / (p - 1))) *
      {t : ℝ | ENNReal.ofReal t < 2 * a}.indicator
        (fun t => ENNReal.ofReal ((p - 1) * t ^ (p - 1 - 1))) t := by
    intro t ht
    have hiff : ENNReal.ofReal (t / 2) < a ↔ ENNReal.ofReal t < 2 * a := by
      have h2s : ENNReal.ofReal t = 2 * ENNReal.ofReal (t / 2) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
      rw [h2s, ENNReal.mul_lt_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top]
    by_cases h : ENNReal.ofReal (t / 2) < a
    · rw [indicator_of_mem (show t ∈ {t : ℝ | ENNReal.ofReal (t / 2) < a} from h),
        indicator_of_mem (show t ∈ {t : ℝ | ENNReal.ofReal t < 2 * a} from hiff.1 h),
        mul_assoc a, ← ENNReal.ofReal_mul (by positivity), show p - 1 - 1 = p - 2 by ring]
      congr 2
      field_simp
    · rw [indicator_of_notMem (show t ∉ {t : ℝ | ENNReal.ofReal (t / 2) < a} from h),
        indicator_of_notMem (show t ∉ {t : ℝ | ENNReal.ofReal t < 2 * a} from
          fun h' => h (hiff.2 h')), zero_mul, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr, lintegral_const_mul]
  · rw [← rpow_eq_lintegral (2 * a) hp1, ENNReal.mul_rpow_of_nonneg _ _ hp1.le]
    have hap : a ^ p = a * a ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [ENNReal.rpow_add_of_nonneg (x := a) 1 (p - 1) zero_le_one hp1.le, ENNReal.rpow_one]
    have h2 : (2 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (2 ^ (p - 1)) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hp1.le, ENNReal.ofReal_ofNat]
    have hc : ENNReal.ofReal (2 * p / (p - 1)) * ENNReal.ofReal (2 ^ (p - 1)) =
        ENNReal.ofReal (2 ^ p * p / (p - 1)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp
    rw [hap, h2, ← hc]
    apply le_of_eq
    ring
  · exact (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_id.pow_const _))).indicator
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

/-- **`L^p` bound for the dyadic maximal function with constant `2^p p / (p - 1)`.** For `1 < p`
and `‖f‖ₑ` a.e. measurable, `∫ (M_d f)^p ≤ 2^p p / (p - 1) ∫ ‖f‖^p`. The proof is the
Marcinkiewicz argument: split `f` at height `t / 2`, apply the weak type (1,1) bound to the large
part, and integrate in `t` (layer-cake formula and Tonelli). It needs no finiteness assumption
and is used to obtain the sharp constant in `lintegral_rpow_dyadicMaximalFunction_le`. -/
theorem lintegral_rpow_dyadicMaximal_le_two_rpow_mul {f : ℝ → E}
    (hf : AEMeasurable (fun y => ‖f y‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, dyadicMaximalFunction f x ^ p ≤
      ENNReal.ofReal (2 ^ p * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hH : Measurable fun z : ℝ × ℝ≥0∞ =>
      {z : ℝ × ℝ≥0∞ | ENNReal.ofReal (z.1 / 2) < z.2}.indicator (fun z => z.2) z *
        ENNReal.ofReal (2 * p * z.1 ^ (p - 2)) := by
    refine Measurable.mul (measurable_snd.indicator ?_) ?_
    · exact measurableSet_lt (ENNReal.measurable_ofReal.comp
        (measurable_fst.div_const 2)) measurable_snd
    · exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul (measurable_fst.pow_const _))
  have hΦm : AEMeasurable (Function.uncurry fun (t x : ℝ) =>
      {x | ENNReal.ofReal (t / 2) < ‖f x‖ₑ}.indicator (fun y => ‖f y‖ₑ) x *
        ENNReal.ofReal (2 * p * t ^ (p - 2))) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have := hH.comp_aemeasurable (measurable_fst.aemeasurable.prodMk hf.comp_snd)
      (μ := (volume.restrict (Ioi (0 : ℝ))).prod volume)
    refine this.congr (Eventually.of_forall fun z => ?_)
    rcases z with ⟨t, x⟩
    simp [Set.indicator_apply]
  calc ∫⁻ x, dyadicMaximalFunction f x ^ p
      = ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < dyadicMaximalFunction f x} *
          ENNReal.ofReal (p * t ^ (p - 1)) :=
        lintegral_rpow_eq_lintegral_volume_mul (measurable_dyadicMaximalFunction f)
          (by linarith)
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
          {x | ENNReal.ofReal (t / 2) < ‖f x‖ₑ}.indicator (fun y => ‖f y‖ₑ) x *
            ENNReal.ofReal (2 * p * t ^ (p - 2)) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => volume_mul_le_lintegral_split f ht
    _ = ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ),
          {x | ENNReal.ofReal (t / 2) < ‖f x‖ₑ}.indicator (fun y => ‖f y‖ₑ) x *
            ENNReal.ofReal (2 * p * t ^ (p - 2)) := lintegral_lintegral_swap hΦm
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 ^ p * p / (p - 1)) * ‖f x‖ₑ ^ p := by
        refine lintegral_mono fun x => le_of_eq_of_le ?_ (lintegral_indicator_mul_le ‖f x‖ₑ hp)
        refine lintegral_congr fun t => ?_
        simp [Set.indicator_apply]
    _ = ENNReal.ofReal (2 ^ p * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Doob-type inequality for the dyadic maximal function.** For `1 < p` and `‖f‖ₑ` a.e.
measurable, `∫ (M_d f)^p ≤ p / (p - 1) ∫ ‖f‖ (M_d f)^{p - 1}`: integrate the localized weak
type (1,1) bound `t |{M_d f > t}| ≤ ∫_{M_d f > t} ‖f‖` against `p t^{p - 2} dt`. -/
theorem lintegral_rpow_le_lintegral_mul_dyadicMaximalFunction {f : ℝ → E}
    (hf : AEMeasurable (fun y => ‖f y‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, dyadicMaximalFunction f x ^ p ≤
      ENNReal.ofReal (p / (p - 1)) *
        ∫⁻ x, ‖f x‖ₑ * dyadicMaximalFunction f x ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hMm := measurable_dyadicMaximalFunction f
  have hstep : ∀ t ∈ Ioi (0 : ℝ),
      volume {x | ENNReal.ofReal t < dyadicMaximalFunction f x} *
          ENNReal.ofReal (p * t ^ (p - 1)) ≤
        ∫⁻ x, {x | ENNReal.ofReal t < dyadicMaximalFunction f x}.indicator
          (fun y => ‖f y‖ₑ) x * ENNReal.ofReal (p * t ^ (p - 2)) := by
    intro t ht
    have hw := mul_volume_lt_dyadicMaximalFunction_le f (ENNReal.ofReal t)
    rw [← lintegral_indicator (measurableSet_lt measurable_const hMm)] at hw
    have hsplit : ENNReal.ofReal (p * t ^ (p - 1)) =
        ENNReal.ofReal t * ENNReal.ofReal (p * t ^ (p - 2)) := by
      rw [← ENNReal.ofReal_mul (le_of_lt ht)]
      congr 1
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
      ring
    rw [hsplit, ← mul_assoc, mul_comm (volume _) (ENNReal.ofReal t),
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    gcongr
  have hH : Measurable fun z : ℝ × (ℝ≥0∞ × ℝ≥0∞) =>
      {z : ℝ × (ℝ≥0∞ × ℝ≥0∞) | ENNReal.ofReal z.1 < z.2.2}.indicator (fun z => z.2.1) z *
        ENNReal.ofReal (p * z.1 ^ (p - 2)) := by
    refine Measurable.mul (measurable_snd.fst.indicator ?_) ?_
    · exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        measurable_snd.snd
    · exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul (measurable_fst.pow_const _))
  have hΦm : AEMeasurable (Function.uncurry fun (t x : ℝ) =>
      {x | ENNReal.ofReal t < dyadicMaximalFunction f x}.indicator (fun y => ‖f y‖ₑ) x *
        ENNReal.ofReal (p * t ^ (p - 2))) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have := hH.comp_aemeasurable (measurable_fst.aemeasurable.prodMk
      (hf.comp_snd.prodMk (hMm.comp measurable_snd).aemeasurable))
      (μ := (volume.restrict (Ioi (0 : ℝ))).prod volume)
    refine this.congr (Eventually.of_forall fun z => ?_)
    rcases z with ⟨t, x⟩
    simp [Set.indicator_apply]
  have hinner : ∀ x, ∫⁻ t in Ioi (0 : ℝ),
      {x | ENNReal.ofReal t < dyadicMaximalFunction f x}.indicator (fun y => ‖f y‖ₑ) x *
        ENNReal.ofReal (p * t ^ (p - 2)) =
      ENNReal.ofReal (p / (p - 1)) * (‖f x‖ₑ * dyadicMaximalFunction f x ^ (p - 1)) := by
    intro x
    have hcongr : ∀ t ∈ Ioi (0 : ℝ),
        {x | ENNReal.ofReal t < dyadicMaximalFunction f x}.indicator (fun y => ‖f y‖ₑ) x *
          ENNReal.ofReal (p * t ^ (p - 2)) =
        (‖f x‖ₑ * ENNReal.ofReal (p / (p - 1))) *
          {t : ℝ | ENNReal.ofReal t < dyadicMaximalFunction f x}.indicator
            (fun t => ENNReal.ofReal ((p - 1) * t ^ (p - 1 - 1))) t := by
      intro t ht
      by_cases h : ENNReal.ofReal t < dyadicMaximalFunction f x
      · rw [indicator_of_mem (show x ∈ {x | ENNReal.ofReal t < dyadicMaximalFunction f x} from h),
          indicator_of_mem (show t ∈ {t : ℝ | ENNReal.ofReal t < dyadicMaximalFunction f x}
            from h), mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show p - 1 - 1 = p - 2 by ring]
        congr 2
        field_simp
      · rw [indicator_of_notMem
          (show x ∉ {x | ENNReal.ofReal t < dyadicMaximalFunction f x} from h),
          indicator_of_notMem
            (show t ∉ {t : ℝ | ENNReal.ofReal t < dyadicMaximalFunction f x} from h),
          zero_mul, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr, lintegral_const_mul,
      ← rpow_eq_lintegral _ hp1]
    · ring
    · exact (ENNReal.measurable_ofReal.comp (measurable_const.mul
        (measurable_id.pow_const _))).indicator
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  calc ∫⁻ x, dyadicMaximalFunction f x ^ p
      = ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < dyadicMaximalFunction f x} *
          ENNReal.ofReal (p * t ^ (p - 1)) := lintegral_rpow_eq_lintegral_volume_mul hMm hp0
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioi hstep
    _ = _ := lintegral_lintegral_swap hΦm
    _ = ∫⁻ x, ENNReal.ofReal (p / (p - 1)) *
          (‖f x‖ₑ * dyadicMaximalFunction f x ^ (p - 1)) := lintegral_congr hinner
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **`L^p` bound for the dyadic maximal function.** For `1 < p < ∞` and every `f : ℝ → E` with
`‖f‖ₑ` a.e. measurable, `∫ (M_d f)^p ≤ (p / (p - 1))^p ∫ ‖f‖^p`, that is `‖M_d f‖_p ≤ p' ‖f‖_p`
with `p' = p / (p - 1)` (T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of
Helsinki, version of 2 May 2014, Theorem 3.8, with `μ = ν` the Lebesgue measure on `ℝ`; the case
`p = ∞` there is not stated). Hölder's inequality turns the Doob-type inequality into
`X ≤ p' G^{1/p} X^{1/p'}` with `X = ∫ (M_d f)^p`, `G = ∫ ‖f‖^p`; the bound with constant
`2^p p / (p - 1)` shows `X < ∞` when `G < ∞`, so `X^{1/p'}` can be cancelled. -/
theorem lintegral_rpow_dyadicMaximalFunction_le {f : ℝ → E}
    (hf : AEMeasurable (fun y => ‖f y‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, dyadicMaximalFunction f x ^ p ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set X := ∫⁻ x, dyadicMaximalFunction f x ^ p with hXdef
  set G := ∫⁻ x, ‖f x‖ₑ ^ p with hGdef
  have hcpos : 0 < (p / (p - 1)) ^ p := Real.rpow_pos_of_pos (div_pos hp0 hp1) p
  rcases eq_or_ne G ∞ with hG | hG
  · rw [hG, ENNReal.mul_top (by simpa using hcpos)]
    exact le_top
  have hX : X ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_rpow_dyadicMaximal_le_two_rpow_mul hf hp)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG
  rcases eq_or_ne X 0 with hX0 | hX0
  · rw [hX0]; exact zero_le
  set q := p / (p - 1) with hq
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hq0 : 0 < q := div_pos hp0 hp1
  have hMq : ∀ x, (dyadicMaximalFunction f x ^ (p - 1)) ^ q = dyadicMaximalFunction f x ^ p := by
    intro x
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hq]; field_simp
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hf
    ((measurable_dyadicMaximalFunction f).pow_const (p - 1)).aemeasurable
  simp only [Pi.mul_apply, hMq] at hholder
  have hmain := (lintegral_rpow_le_lintegral_mul_dyadicMaximalFunction hf hp).trans
    (mul_le_mul_of_nonneg_left hholder zero_le)
  rw [← hXdef, ← hGdef] at hmain
  have hsum : 1 / p + 1 / q = 1 := by rw [hq]; field_simp; ring
  have hsplit : X = X ^ (1 / p) * X ^ (1 / q) := by
    rw [← ENNReal.rpow_add _ _ hX0 hX, hsum, ENNReal.rpow_one]
  have hXq0 : X ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hX0) hX).ne'
  have hXqt : X ^ (1 / q) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hX
  have h1 : X ^ (1 / p) ≤ ENNReal.ofReal q * G ^ (1 / p) := by
    rw [← ENNReal.mul_le_mul_iff_left hXq0 hXqt, ← hsplit, mul_assoc]
    exact hmain
  have h2 := ENNReal.rpow_le_rpow h1 hp0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
    ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg hq0.le hp0.le] at h2
  exact h2

end MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal
