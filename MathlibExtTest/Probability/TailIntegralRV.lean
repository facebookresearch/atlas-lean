/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TailIntegralRV
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Tests for the corrected regularly-varying tail integral

The Pareto measure with tail index `α > 0` is the canonical example: its
combined tail is exactly `x ^ (-α)` for `x ≥ 1`, and its tail balance is
`p = 1`. The main theorem applied at `α = 1 / 2`, `c = 4` gives the limit `2`.

The Pareto density, measure and tail computations adapt
`MathlibExtTest/Probability/TruncatedMomentRV.lean` at commit
`e3e3f8ecc896e5925ae9c2b5da576063df868e2e`. This file tests the first moment
and the `α > 1` divergence, rather than that source's second moment.

The falsification: for `α = 3 / 2` the ratio diverges to `+∞`, while v1's
formula `p * α * c ^ (1 - α) / (1 - α)` (with `p = 1`, `c = 1`) gives the
finite negative constant `-3`. Hence v1's statement for `α > 1` is false.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MathlibExtTest.TailIntegralRV

open MathlibExt.Probability.TailIntegralRV
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

/-- Nonpositive Pareto parameters give zero density after `ofReal`. -/
theorem paretoMeasure_eq_zero_of_nonpos {α : ℝ} (hα : α ≤ 0) :
    paretoMeasure α = 0 := by
  have hzero : (fun x => ENNReal.ofReal (paretoDensityReal α x)) = fun _ => 0 := by
    funext x
    unfold paretoDensityReal
    split_ifs with hx
    · apply ENNReal.ofReal_eq_zero.mpr
      exact mul_nonpos_of_nonpos_of_nonneg hα (Real.rpow_nonneg (by linarith) _)
    · simp
  unfold paretoMeasure
  rw [hzero]
  simp

/-- Every real-parameter Pareto measure is finite; positive parameters have mass one. -/
instance paretoMeasure_isFinite (α : ℝ) : IsFiniteMeasure (paretoMeasure α) := by
  by_cases hα : 0 < α
  · have : IsProbabilityMeasure (paretoMeasure α) := ⟨pareto_prob hα⟩
    infer_instance
  · rw [paretoMeasure_eq_zero_of_nonpos (le_of_not_gt hα)]
    infer_instance

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

/-- The Pareto right tail is `1` below `1` (the support lies in `[1, ∞)`). -/
theorem pareto_rightTail_of_lt_one {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : t < 1) :
    rightTail (paretoMeasure α) t = 1 := by
  have hIic : (paretoMeasure α) (Set.Iic t) = 0 := by
    unfold paretoMeasure
    rw [withDensity_apply _ measurableSet_Iic]
    have hEq : Set.EqOn (fun y => ENNReal.ofReal (paretoDensityReal α y)) (fun _ => 0)
        (Set.Iic t) := by
      intro y hy
      have hy1 : y < 1 := lt_of_le_of_lt (Set.mem_Iic.mp hy) ht
      show ENNReal.ofReal (paretoDensityReal α y) = 0
      rw [paretoDensityReal_eq_zero hy1]
      simp
    rw [setLIntegral_congr_fun measurableSet_Iic hEq]
    exact lintegral_zero
  have hcompl : (paretoMeasure α) (Set.Ioi t) = 1 := by
    have h := measure_add_measure_compl (μ := paretoMeasure α) (s := Set.Iic t) measurableSet_Iic
    rw [Set.compl_Iic] at h
    rw [pareto_prob hα] at h
    rw [hIic, zero_add] at h
    exact h
  unfold rightTail
  rw [hcompl, ENNReal.toReal_one]

/-- The Pareto measure has tail balance `p = 1`. -/
theorem pareto_tailBalance {α : ℝ} (hα : 0 < α) :
    HasTailBalance (paretoMeasure α) 1 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [pareto_combinedTail hα hx]
    exact Real.rpow_pos_of_pos (by linarith) _
  · have hEv : (fun x => rightTail (paretoMeasure α) x / combinedTail (paretoMeasure α) x)
        =ᶠ[atTop] fun _ => (1:ℝ) := by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      rw [pareto_rightTail hα hx, pareto_combinedTail hα hx]
      exact div_self (ne_of_gt (Real.rpow_pos_of_pos (by linarith) _))
    exact Filter.Tendsto.congr' hEv.symm tendsto_const_nhds

/-- The Pareto combined tail is regularly varying of index `-α`. -/
theorem pareto_regularlyVarying {α : ℝ} (hα : 0 < α) :
    IsRegularlyVarying (combinedTail (paretoMeasure α)) (-α) := by
  refine ⟨fun _ => 1, isSlowlyVarying_one, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  rw [pareto_combinedTail hα hx, mul_one]

/-- The main theorem applied to the Pareto law with `α = 1 / 2`, `c = 4`:
the limit is `2`. -/
theorem pareto_tailIntegral_via_theorem :
    Tendsto (fun x => (∫ y in Set.Ioc 0 (4 * x), y ∂(paretoMeasure (1 / 2 : ℝ)))
        / (x * combinedTail (paretoMeasure (1 / 2 : ℝ)) x)) atTop (𝓝 2) := by
  have : IsProbabilityMeasure (paretoMeasure (1 / 2 : ℝ)) :=
    ⟨pareto_prob (by norm_num)⟩
  have h := tailIntegral_tendsto (μ := paretoMeasure (1 / 2 : ℝ))
    (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1:ℝ) / 2 < 1)
    (pareto_tailBalance (by norm_num)) (pareto_regularlyVarying (by norm_num))
    (c := (4:ℝ)) (by norm_num)
  have h4 : (4:ℝ) ^ ((1:ℝ) / 2) = 2 := by
    rw [show (4:ℝ) = (2:ℝ) ^ 2 by norm_num, ← Real.rpow_natCast (2:ℝ) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      show ((2:ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  have h41 : (4:ℝ) ^ ((1:ℝ) - 1 / 2) = 2 := by
    have e : (1:ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [e]
    exact h4
  have hlim : (1:ℝ) * (1 / 2) * (4:ℝ) ^ ((1:ℝ) - 1 / 2) / ((1:ℝ) - 1 / 2) = 2 := by
    rw [h41]
    norm_num
  rw [hlim] at h
  exact h

/-- For `α = 3 / 2` the first-moment tail ratio diverges to `+∞`: the
numerator stays bounded away from `0` while the denominator tends to `0`. -/
theorem pareto_tailIntegral_diverges {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => (∫ y in Set.Ioc 0 (c * x), y ∂(paretoMeasure (3 / 2 : ℝ)))
        / (x * combinedTail (paretoMeasure (3 / 2 : ℝ)) x)) atTop atTop := by
  have : IsProbabilityMeasure (paretoMeasure (3 / 2 : ℝ)) :=
    ⟨pareto_prob (by norm_num)⟩
  set m := 1 - (2:ℝ) ^ (-(3 / 2 : ℝ)) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    have h : (2:ℝ) ^ (-(3 / 2 : ℝ)) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
    linarith
  have htop : Tendsto (fun x => (m / 2) * x ^ ((1:ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).const_mul_atTop (by linarith)
  apply tendsto_atTop_mono' atTop _ htop
  filter_upwards [eventually_ge_atTop (max (2 / c) 1)] with x hx
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hcx : 2 ≤ c * x := by
    have h1 : 2 / c ≤ x := le_trans (le_max_left _ _) hx
    rw [div_le_iff₀ hc] at h1
    linarith [h1]
  have hCx : combinedTail (paretoMeasure (3 / 2 : ℝ)) x = x ^ (-(3 / 2 : ℝ)) :=
    pareto_combinedTail (by norm_num) hx1
  have hR2 : rightTail (paretoMeasure (3 / 2 : ℝ)) 2 = (2:ℝ) ^ (-(3 / 2 : ℝ)) :=
    pareto_rightTail (by norm_num) (by norm_num)
  -- numerator lower bound: the first-moment integral is at least `(1 / 2) * m`
  have hN : (1 / 2 : ℝ) * m ≤ ∫ y in Set.Ioc 0 (c * x), y ∂(paretoMeasure (3 / 2 : ℝ)) := by
    have hcx0 : 0 ≤ c * x := mul_nonneg hc.le hxpos.le
    rw [layerCake_firstMoment hcx0]
    have hIntDiff : ∀ a b : ℝ, a ≤ b → IntervalIntegrable
        (fun t => rightTail (paretoMeasure (3 / 2 : ℝ)) t
          - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)) volume a b := by
      intro a b hab
      exact (intervalIntegrable_of_antitone_bdd
        (rightTail_antitone (paretoMeasure (3 / 2 : ℝ)))
        (fun t => rightTail_nonneg _ t)
        ⟨1, fun t => rightTail_le_one _ t⟩ hab).sub intervalIntegrable_const
    have hsplit : (∫ t in (0:ℝ)..(c * x),
          (rightTail (paretoMeasure (3 / 2 : ℝ)) t
            - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)))
        = (∫ t in (0:ℝ)..(1 / 2),
          (rightTail (paretoMeasure (3 / 2 : ℝ)) t
            - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)))
          + (∫ t in (1 / 2 : ℝ)..(c * x),
            (rightTail (paretoMeasure (3 / 2 : ℝ)) t
              - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x))) :=
      (intervalIntegral.integral_add_adjacent_intervals (hIntDiff 0 (1 / 2) (by norm_num))
        (hIntDiff (1 / 2) (c * x) (by linarith))).symm
    have hnn : 0 ≤ ∫ t in (1 / 2 : ℝ)..(c * x),
        (rightTail (paretoMeasure (3 / 2 : ℝ)) t
          - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)) := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro t ht
      have hle : rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)
          ≤ rightTail (paretoMeasure (3 / 2 : ℝ)) t :=
        rightTail_antitone _ ht.2
      linarith
    have hcongr : (∫ t in (0:ℝ)..(1 / 2),
          (rightTail (paretoMeasure (3 / 2 : ℝ)) t
            - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)))
        = ∫ t in (0:ℝ)..(1 / 2), (1 - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (show (0:ℝ) ≤ 1 / 2 by norm_num)] at ht
      show rightTail (paretoMeasure (3 / 2 : ℝ)) t
          - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)
          = 1 - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)
      have hRt : rightTail (paretoMeasure (3 / 2 : ℝ)) t = 1 := by
        apply pareto_rightTail_of_lt_one (by norm_num)
        linarith [ht.2]
      rw [hRt]
    rw [hsplit, hcongr]
    have hRcx : rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)
        ≤ rightTail (paretoMeasure (3 / 2 : ℝ)) 2 :=
      rightTail_antitone _ hcx
    have h1m : m ≤ (1:ℝ) - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x) := by
      rw [hmdef]
      linarith [hRcx, hR2]
    have hA : (∫ t in (0:ℝ)..(1 / 2),
          (1 - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)))
        = ((1:ℝ) / 2 - 0) * (1 - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    calc (1 / 2 : ℝ) * m
        ≤ (1 / 2 - 0) * (1 - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)) := by
          rw [sub_zero]
          exact mul_le_mul_of_nonneg_left h1m (by norm_num)
      _ = (∫ t in (0:ℝ)..(1 / 2), (1 - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x))) :=
          hA.symm
      _ ≤ (∫ t in (0:ℝ)..(1 / 2), (1 - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x)))
          + (∫ t in (1 / 2 : ℝ)..(c * x),
            (rightTail (paretoMeasure (3 / 2 : ℝ)) t
              - rightTail (paretoMeasure (3 / 2 : ℝ)) (c * x))) :=
          le_add_of_nonneg_right hnn
  -- divide by `x * C x = x ^ (-1 / 2)`
  have hden : x * combinedTail (paretoMeasure (3 / 2 : ℝ)) x = x ^ (-((1:ℝ) / 2)) := by
    rw [hCx]
    have h := Real.rpow_add hxpos (1:ℝ) (-(3 / 2 : ℝ))
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  rw [hden]
  have hpos : 0 < x ^ (-((1:ℝ) / 2)) := Real.rpow_pos_of_pos hxpos _
  have hle : (m / 2) * x ^ ((1:ℝ) / 2)
      ≤ (∫ y in Set.Ioc 0 (c * x), y ∂(paretoMeasure (3 / 2 : ℝ)))
        / x ^ (-((1:ℝ) / 2)) := by
    rw [le_div_iff₀ hpos]
    have hmul : x ^ ((1:ℝ) / 2) * x ^ (-((1:ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add hxpos, show (1:ℝ) / 2 + -((1:ℝ) / 2) = 0 by ring, Real.rpow_zero]
    calc (m / 2) * x ^ ((1:ℝ) / 2) * x ^ (-((1:ℝ) / 2))
        = (m / 2) * (x ^ ((1:ℝ) / 2) * x ^ (-((1:ℝ) / 2))) := by ring
      _ = m / 2 := by rw [hmul, mul_one]
      _ ≤ ∫ y in Set.Ioc 0 (c * x), y ∂(paretoMeasure (3 / 2 : ℝ)) := by linarith [hN]
  exact hle

/-- v1's formula for `α = 3 / 2`, `c = 1`, `p = 1` gives the constant `-3`,
but the ratio diverges, so it cannot converge to `-3`. -/
theorem pareto_not_tendsto_v1_constant :
    ¬ Tendsto (fun x => (∫ y in Set.Ioc 0 (1 * x), y ∂(paretoMeasure (3 / 2 : ℝ)))
        / (x * combinedTail (paretoMeasure (3 / 2 : ℝ)) x)) atTop (𝓝 (-3)) := by
  intro h
  have htop := pareto_tailIntegral_diverges (c := (1:ℝ)) (by norm_num)
  have h1 : ∀ᶠ x in atTop, (0:ℝ) ≤
      (∫ y in Set.Ioc 0 (1 * x), y ∂(paretoMeasure (3 / 2 : ℝ)))
        / (x * combinedTail (paretoMeasure (3 / 2 : ℝ)) x) :=
    (tendsto_atTop.mp htop) 0
  have h2 : ∀ᶠ x in atTop,
      (∫ y in Set.Ioc 0 (1 * x), y ∂(paretoMeasure (3 / 2 : ℝ)))
        / (x * combinedTail (paretoMeasure (3 / 2 : ℝ)) x) < -2 := by
    filter_upwards [(Metric.tendsto_nhds.mp h) 1 one_pos] with x hx
    rw [Real.dist_eq] at hx
    have hlt := (abs_lt.mp hx).2
    linarith
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  linarith

#print axioms pareto_tailIntegral_via_theorem
#print axioms pareto_tailIntegral_diverges
#print axioms pareto_not_tendsto_v1_constant

end MathlibExtTest.TailIntegralRV
