/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TruncatedMomentRV
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Tests for the corrected truncated-second-moment asymptotic

The Pareto measure with tail index `α ∈ (0, 2)` is the canonical example: its
combined tail is exactly `x ^ (-α)` for `x ≥ 1`, and the truncated second
moment ratio can be computed directly. The direct computation gives the limit
`α / (2 - α)`, which is the corrected constant of `truncatedMoment_tendsto`;
`v1`'s stated constant `2 / (2 - α)` is wrong (for `α = 1` the limit is `1`,
while `v1` claims `2`).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MathlibExtTest.TruncatedMomentRV

open MathlibExt.Probability.TruncatedMoment
open MathlibExt.Probability.RegularVariation

/-- Pareto density (real-valued): `α * x ^ (-α - 1)` on `[1, ∞)`, `0` elsewhere. -/
noncomputable def paretoDensityReal (α : ℝ) (x : ℝ) : ℝ :=
  if 1 ≤ x then α * x ^ (-α - 1) else 0

/-- The Pareto probability measure on `ℝ` with tail index `α > 0`. -/
noncomputable def paretoMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (paretoDensityReal α x))

theorem paretoDensityReal_nonneg {α : ℝ} (hα : 0 < α) (x : ℝ) :
    0 ≤ paretoDensityReal α x := by
  unfold paretoDensityReal
  split_ifs with h
  · exact mul_nonneg hα.le (Real.rpow_nonneg (by linarith) _)
  · exact le_refl 0

theorem paretoDensityReal_eq {α : ℝ} {x : ℝ} (hx : 1 ≤ x) :
    paretoDensityReal α x = α * x ^ (-α - 1) := by
  unfold paretoDensityReal
  simp only [hx, ite_true]

theorem paretoDensityReal_eq_zero {α : ℝ} {x : ℝ} (hx : x < 1) :
    paretoDensityReal α x = 0 := by
  unfold paretoDensityReal
  simp only [show ¬ (1:ℝ) ≤ x from by linarith, ite_false]

/-- The tail integral of the Pareto density. -/
theorem integral_Ioi_paretoDensity {α : ℝ} (hα : 0 < α)
    {x : ℝ} (hx : 1 ≤ x) :
    ∫ y in Set.Ioi x, paretoDensityReal α y = x ^ (-α) := by
  have hInt : IntegrableOn (fun y => α * y ^ (-α - 1)) (Set.Ioi x) volume :=
    (integrableOn_Ioi_rpow_of_lt (show -α - 1 < -1 by linarith)
      (show (0:ℝ) < x by linarith)).const_mul α
  have hDeriv : ∀ y ∈ Set.Ici x,
      HasDerivAt (fun y => -(y ^ (-α))) (α * y ^ (-α - 1)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      have hylt : (0:ℝ) < y := by linarith [Set.mem_Ici.mp hy]
      exact ne_of_gt hylt
    have h := (hasDerivAt_id y).rpow_const (p := -α) (Or.inl hy0)
    have h2 := h.neg
    have h3 : -(1 * -α * y ^ (-α - 1)) = α * y ^ (-α - 1) := by ring
    simpa only [id_eq, h3, Pi.neg_def] using h2
  have hTend : Tendsto (fun y : ℝ => -(y ^ (-α))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun y : ℝ => 0 - y ^ (-α)) atTop (𝓝 (0 - 0)) := by
      have h1 : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0) := tendsto_const_nhds
      have h3 : Tendsto (fun y : ℝ => y ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
      exact h1.sub h3
    have hEq : (fun y : ℝ => -(y ^ (-α))) =ᶠ[atTop] (fun y : ℝ => 0 - y ^ (-α)) := by
      filter_upwards with y
      rw [zero_sub]
    rw [sub_zero] at h2
    exact Filter.Tendsto.congr' hEq.symm h2
  have hEq : (∫ y in Set.Ioi x, paretoDensityReal α y)
      = ∫ y in Set.Ioi x, α * y ^ (-α - 1) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy1 : (1:ℝ) ≤ y := by linarith [Set.mem_Ioi.mp hy, hx]
    rw [paretoDensityReal_eq hy1]
  rw [hEq, integral_Ioi_of_hasDerivAt_of_tendsto' hDeriv hInt hTend]
  simp

/-- The Pareto measure is a probability measure. -/
theorem pareto_prob {α : ℝ} (hα : 0 < α) :
    (paretoMeasure α) Set.univ = 1 := by
  have hInt : IntegrableOn (paretoDensityReal α) (Set.Ioi 1) volume := by
    apply IntegrableOn.congr_fun
      ((integrableOn_Ioi_rpow_of_lt (show -α - 1 < -1 by linarith)
        (show (0:ℝ) < 1 by norm_num)).const_mul α) _ measurableSet_Ioi
    intro y hy
    have hy1 : (1:ℝ) ≤ y := by linarith [Set.mem_Ioi.mp hy]
    rw [paretoDensityReal_eq hy1]
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi 1)] paretoDensityReal α :=
    ae_of_all _ (fun y => paretoDensityReal_nonneg hα y)
  unfold paretoMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hSplit : (∫⁻ y, ENNReal.ofReal (paretoDensityReal α y))
      = (∫⁻ y in Set.Ioi 1, ENNReal.ofReal (paretoDensityReal α y))
        + (∫⁻ y in (Set.Ioi (1:ℝ))ᶜ, ENNReal.ofReal (paretoDensityReal α y)) :=
    (lintegral_add_compl (fun y => ENNReal.ofReal (paretoDensityReal α y))
      measurableSet_Ioi).symm
  have hCompl : (∫⁻ y in (Set.Ioi (1:ℝ))ᶜ, ENNReal.ofReal (paretoDensityReal α y)) = 0 := by
    rw [Set.compl_Ioi]
    have hUnion : Set.Iic (1:ℝ) = Set.Iio 1 ∪ {1} := by
      ext y
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
      exact le_iff_lt_or_eq
    rw [hUnion, lintegral_union (A := Set.Iio (1:ℝ)) (measurableSet_singleton (1:ℝ))
      (Set.disjoint_singleton_right.mpr (fun h => lt_irrefl (1:ℝ) h))]
    have h1 : (∫⁻ y in Set.Iio (1:ℝ), ENNReal.ofReal (paretoDensityReal α y)) = 0 := by
      have hEq : Set.EqOn (fun y => ENNReal.ofReal (paretoDensityReal α y)) (fun _ => 0)
          (Set.Iio (1:ℝ)) := by
        intro y hy
        simp only [Set.mem_Iio] at hy
        show ENNReal.ofReal (paretoDensityReal α y) = 0
        rw [paretoDensityReal_eq_zero hy]
        simp
      rw [setLIntegral_congr_fun measurableSet_Iio hEq]
      exact lintegral_zero
    have h2 : (∫⁻ y in ({1} : Set ℝ), ENNReal.ofReal (paretoDensityReal α y)) = 0 := by
      rw [lintegral_singleton, Real.volume_singleton, mul_zero]
    rw [h1, h2, add_zero]
  rw [hSplit, hCompl, add_zero, ← ofReal_integral_eq_lintegral_ofReal hInt hNonneg,
    integral_Ioi_paretoDensity hα (show (1:ℝ) ≤ 1 by norm_num)]
  simp [Real.one_rpow]

/-- Atoms of the Pareto measure vanish. -/
theorem pareto_atom {α : ℝ} (t : ℝ) :
    (paretoMeasure α) {t} = 0 := by
  unfold paretoMeasure
  rw [withDensity_apply _ (measurableSet_singleton t), lintegral_singleton,
    Real.volume_singleton, mul_zero]

theorem pareto_rightTail {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    rightTail (paretoMeasure α) x = x ^ (-α) := by
  unfold rightTail
  have h : (paretoMeasure α) (Set.Ioi x)
      = ENNReal.ofReal (x ^ (-α)) := by
    unfold paretoMeasure
    rw [withDensity_apply _ measurableSet_Ioi]
    have hInt : IntegrableOn (paretoDensityReal α) (Set.Ioi x) volume := by
      apply IntegrableOn.congr_fun
        ((integrableOn_Ioi_rpow_of_lt (show -α - 1 < -1 by linarith)
          (show (0:ℝ) < x by linarith)).const_mul α) _ measurableSet_Ioi
      intro y hy
      have hy1 : (1:ℝ) ≤ y := by linarith [Set.mem_Ioi.mp hy, hx]
      rw [paretoDensityReal_eq hy1]
    have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi x)] paretoDensityReal α :=
      ae_of_all _ (fun y => paretoDensityReal_nonneg hα y)
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hNonneg,
      integral_Ioi_paretoDensity hα hx]
  rw [h, ENNReal.toReal_ofReal (Real.rpow_nonneg (by linarith) _)]

theorem pareto_leftTail_zero {α : ℝ} {x : ℝ} (hx : 1 ≤ x) :
    leftTail (paretoMeasure α) x = 0 := by
  unfold leftTail
  have h : (paretoMeasure α) (Set.Iio (-x)) = 0 := by
    unfold paretoMeasure
    rw [withDensity_apply _ measurableSet_Iio]
    have hEq : Set.EqOn (fun y => ENNReal.ofReal (paretoDensityReal α y)) (fun _ => 0)
        (Set.Iio (-x)) := by
      intro y hy
      simp only [Set.mem_Iio] at hy
      show ENNReal.ofReal (paretoDensityReal α y) = 0
      rw [paretoDensityReal_eq_zero (by linarith : y < 1)]
      simp
    rw [setLIntegral_congr_fun measurableSet_Iio hEq]
    exact lintegral_zero
  rw [h]
  simp

theorem pareto_combinedTail {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    combinedTail (paretoMeasure α) x = x ^ (-α) := by
  unfold combinedTail
  rw [pareto_rightTail hα hx, pareto_leftTail_zero hx, add_zero]

theorem pareto_tailGe {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 1 ≤ t) :
    tailGe (paretoMeasure α) t = t ^ (-α) := by
  let _ : IsProbabilityMeasure (paretoMeasure α) := ⟨pareto_prob hα⟩
  rw [tailGe_eq_combinedTail_add_atoms (paretoMeasure α)
      (show (0:ℝ) < t by linarith),
    pareto_combinedTail hα ht, pareto_atom t, pareto_atom (-t), ENNReal.toReal_zero, add_zero, add_zero]

theorem pareto_tailGt {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    tailGt (paretoMeasure α) x = x ^ (-α) := by
  let _ : IsProbabilityMeasure (paretoMeasure α) := ⟨pareto_prob hα⟩
  rw [tailGt_eq_combinedTail (paretoMeasure α) (by linarith : (0 : ℝ) ≤ x),
    pareto_combinedTail hα hx]

theorem pareto_tailGe_one {α : ℝ} (hα : 0 < α)
    {t : ℝ} (ht1 : t ≤ 1) :
    tailGe (paretoMeasure α) t = 1 := by
  have hprob := pareto_prob hα
  have hmeas : MeasurableSet {y : ℝ | ¬ t ≤ |y|} := by
    have h : {y : ℝ | ¬ t ≤ |y|} = {y : ℝ | |y| < t} := by
      ext y
      simp only [Set.mem_ofPred_eq, not_le]
    rw [h]
    exact measurableSet_lt continuous_abs.measurable measurable_const
  have hcompl : (paretoMeasure α) {y : ℝ | ¬ t ≤ |y|} = 0 := by
    unfold paretoMeasure
    rw [withDensity_apply _ hmeas]
    have hEq : Set.EqOn (fun y => ENNReal.ofReal (paretoDensityReal α y)) (fun _ => 0)
        {y : ℝ | ¬ t ≤ |y|} := by
      intro y hy
      have hy1 : y < 1 := by
        have hlt : |y| < t := not_le.mp hy
        have hy_le : y ≤ |y| := le_abs_self y
        linarith [hlt, ht1, hy_le]
      show ENNReal.ofReal (paretoDensityReal α y) = 0
      rw [paretoDensityReal_eq_zero hy1]
      simp
    rw [setLIntegral_congr_fun hmeas hEq]
    exact lintegral_zero
  have hmain : (paretoMeasure α) {y : ℝ | t ≤ |y|} = 1 := by
    have hmeas2 : MeasurableSet {y : ℝ | t ≤ |y|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have h := measure_add_measure_compl (μ := paretoMeasure α) hmeas2
    rw [hprob] at h
    have hsc : {y : ℝ | t ≤ |y|}ᶜ = {y : ℝ | ¬ t ≤ |y|} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [hsc, hcompl, add_zero] at h
    exact h
  unfold tailGe
  rw [hmain]
  simp

private theorem intervalIntegrable_id_mul_tailGe {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => t * tailGe μ t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
  · exact (measurable_id.mul (antitone_tailGe μ).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tailGe_nonneg μ t)]
    have ht1 : t ≤ b := (Set.mem_Icc.mp ht).2
    have ht0 : (0:ℝ) ≤ t := le_trans ha (Set.mem_Icc.mp ht).1
    calc |t| * tailGe μ t = t * tailGe μ t := by rw [abs_of_nonneg ht0]
      _ ≤ b * 1 := mul_le_mul ht1 (tailGe_le_one μ t) (tailGe_nonneg μ t) (by linarith)
      _ = b := mul_one b
      _ ≤ 1 + b := by linarith

theorem pareto_integral_tailGe {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (0:ℝ)..x, t * tailGe (paretoMeasure α) t
      = 1 / 2 + (x ^ (2 - α) - 1) / (2 - α) := by
  have hInt01 : IntervalIntegrable (fun t => t * tailGe (paretoMeasure α) t) volume
      (0:ℝ) 1 :=
    @intervalIntegrable_id_mul_tailGe (paretoMeasure α) ⟨pareto_prob hα⟩ 0 1
      (by norm_num) (by norm_num)
  have hInt1x : IntervalIntegrable (fun t => t * tailGe (paretoMeasure α) t) volume
      (1:ℝ) x :=
    @intervalIntegrable_id_mul_tailGe (paretoMeasure α) ⟨pareto_prob hα⟩ 1 x
      (by norm_num) hx
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt01 hInt1x]
  have h01 : (∫ t in (0:ℝ)..(1:ℝ), t * tailGe (paretoMeasure α) t) = 1 / 2 := by
    have hCongr : (∫ t in (0:ℝ)..(1:ℝ), t * tailGe (paretoMeasure α) t)
        = ∫ t in (0:ℝ)..(1:ℝ), t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      show t * tailGe (paretoMeasure α) t = t
      rw [pareto_tailGe_one hα (Set.mem_Icc.mp ht).2, mul_one]
    have hId : (∫ t in (0:ℝ)..(1:ℝ), t) = ∫ t in (0:ℝ)..(1:ℝ), t ^ (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      show t = t ^ (1:ℝ)
      rw [Real.rpow_one]
    rw [hCongr, hId, integral_rpow (Or.inl (show (-1:ℝ) < 1 by norm_num))]
    norm_num [Real.one_rpow, Real.zero_rpow]
  have h1x : (∫ t in (1:ℝ)..x, t * tailGe (paretoMeasure α) t)
      = (x ^ (2 - α) - 1) / (2 - α) := by
    have hCongr : (∫ t in (1:ℝ)..x, t * tailGe (paretoMeasure α) t)
        = ∫ t in (1:ℝ)..x, t ^ (1 - α) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : (0:ℝ) < t := by linarith [(Set.mem_Icc.mp ht).1]
      show t * tailGe (paretoMeasure α) t = t ^ (1 - α)
      rw [pareto_tailGe hα (Set.mem_Icc.mp ht).1]
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht0]
      congr 1
    rw [hCongr, integral_rpow (Or.inl (show (-1:ℝ) < 1 - α by linarith))]
    rw [show (1:ℝ) - α + 1 = 2 - α by ring, Real.one_rpow]
  rw [h01, h1x]

/-- Direct computation of the Pareto truncated-moment ratio, by the layer cake.
This is the evidence that `v1`'s constant `2 / (2 - α)` is wrong: the limit is
`α / (2 - α)` (for `α = 1`, the limit is `1`, not `2`). -/
theorem pareto_ratio_direct {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    Tendsto (fun x => (∫ y in Set.Icc (-x) x, y ^ 2 ∂(paretoMeasure α))
        / (x ^ 2 * combinedTail (paretoMeasure α) x)) atTop (𝓝 (α / (2 - α))) := by
  have hEq : (fun x => (∫ y in Set.Icc (-x) x, y ^ 2 ∂(paretoMeasure α))
        / (x ^ 2 * combinedTail (paretoMeasure α) x))
      =ᶠ[atTop] (fun x => (α / (2 - α)) * (1 - x ^ (-(2 - α)))) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hx0 : (0:ℝ) ≤ x := by linarith
    rw [@layerCake (paretoMeasure α) ⟨pareto_prob hα⟩ x hx0,
      pareto_tailGt hα hx, pareto_combinedTail hα hx,
      pareto_integral_tailGe hα hα2 hx]
    have hx2 : (x:ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith : x ≠ 0)
    have h2α : (2:ℝ) - α ≠ 0 := by linarith
    have hrw : (x:ℝ) ^ 2 * x ^ (-α) = x ^ (2 - α) := by
      rw [← Real.rpow_two x, ← Real.rpow_add (show (0:ℝ) < x by linarith)]
      congr 1
    have hrw2 : (x:ℝ) ^ (-(2 - α)) = (x ^ (2 - α))⁻¹ := by
      rw [Real.rpow_neg hx0]
    rw [hrw, hrw2]
    have hxp : (x:ℝ) ^ (2 - α) ≠ 0 :=
      (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < x) _).ne'
    field_simp
    ring
  have hlim : Tendsto (fun x => (α / (2 - α)) * (1 - x ^ (-(2 - α)))) atTop
      (𝓝 ((α / (2 - α)) * (1 - 0))) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_rpow_neg_atTop (show (0:ℝ) < 2 - α by linarith)))
  rw [sub_zero, mul_one] at hlim
  exact Filter.Tendsto.congr' hEq.symm hlim

theorem pareto_regularlyVarying {α : ℝ} (hα : 0 < α) :
    IsRegularlyVarying (combinedTail (paretoMeasure α)) (-α) := by
  apply (isRegularlyVarying_rpow (-α)).of_eventuallyEq
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa using (pareto_combinedTail hα hx).symm

theorem pareto_ratio_via_theorem {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    Tendsto (fun x => (∫ y in Set.Icc (-x) x, y ^ 2 ∂(paretoMeasure α))
        / (x ^ 2 * combinedTail (paretoMeasure α) x)) atTop (𝓝 (α / (2 - α))) := by
  exact @truncatedMoment_tendsto (paretoMeasure α) ⟨pareto_prob hα⟩ α hα hα2
    (pareto_regularlyVarying hα)

#print axioms pareto_ratio_via_theorem

#print axioms pareto_ratio_direct

end MathlibExtTest.TruncatedMomentRV
