/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.WassersteinConvergence
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

namespace MathlibExtTest.MeasureTheory.OptimalTransport.WassersteinConvergence

/-- The Dirac probability measure at a real number. -/
noncomputable def δ (x : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩

/-- `δ_{1/(k+1)} → δ_0` weakly, deduced from `W_1(δ_{1/(k+1)}, δ_0) = 1/(k+1) → 0`. -/
example : Tendsto (fun k : ℕ => δ (1 / ((k : ℝ) + 1))) atTop (𝓝 (δ 0)) := by
  refine tendsto_of_tendsto_wasserstein le_rfl ?_
  simp only [δ, wasserstein_dirac one_pos]
  exact (tendsto_iff_edist_tendsto_0).1 tendsto_one_div_add_atTop_nhds_zero_nat

private noncomputable def point (k : ℕ) : ℝ := 1 + 1 / ((k : ℝ) + 1)

private theorem point_tendsto : Tendsto point atTop (𝓝 1) := by
  change Tendsto (fun k : ℕ => (1 : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 1)
  simpa only [add_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat

private noncomputable def secondMoment (x₀ : ℝ) (ν : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ∫⁻ y, edist x₀ y ^ (2 : ℝ) ∂(ν : Measure ℝ)

private theorem secondMoment_dirac (x₀ x : ℝ) :
    secondMoment x₀ (diracProba x) = edist x₀ x ^ (2 : ℝ) := by
  change ∫⁻ y, edist x₀ y ^ (2 : ℝ) ∂Measure.dirac x = _
  rw [lintegral_dirac]

-- Check all three limits directly, without using the convergence criterion.
private theorem moving_dirac_limits (x₀ : ℝ) :
    Tendsto (fun k => wasserstein 2 (diracProba (point k)) (diracProba 1)) atTop (𝓝 0) ∧
      Tendsto (fun k => diracProba (point k)) atTop (𝓝 (diracProba 1)) ∧
      Tendsto (fun k => secondMoment x₀ (diracProba (point k))) atTop
        (𝓝 (secondMoment x₀ (diracProba 1))) := by
  refine ⟨?_, continuous_diracProba.continuousAt.tendsto.comp point_tendsto, ?_⟩
  · exact ((tendsto_iff_edist_tendsto_0).1 point_tendsto).congr fun k =>
      (wasserstein_dirac (by norm_num : (0 : ℝ) < 2) (point k) 1).symm
  · simp only [secondMoment_dirac]
    have hc : Continuous (fun x : ℝ => edist x₀ x ^ (2 : ℝ)) :=
      ENNReal.continuous_rpow_const.comp (continuous_const.edist continuous_id)
    exact hc.continuousAt.tendsto.comp point_tendsto

private theorem secondMoment_dirac_lt_top (x₀ x : ℝ) : secondMoment x₀ (diracProba x) < ∞ := by
  rw [secondMoment_dirac]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (edist_ne_top x₀ x)

private theorem secondMoment_two_dirac_one : secondMoment 2 (diracProba 1) = 1 := by
  rw [secondMoment_dirac]
  norm_num [edist_dist, Real.dist_eq, ENNReal.rpow_two]

open MathlibExt.MeasureTheory.WassersteinWanted (tendsto_wasserstein_iff)

-- Forward direction: the moment about 2 converges to 1, not 0.
example : Tendsto (fun k => diracProba (point k)) atTop (𝓝 (diracProba 1)) ∧
    Tendsto (fun k => secondMoment 2 (diracProba (point k))) atTop (𝓝 1) := by
  have h := (tendsto_wasserstein_iff (p := 2) (by norm_num) (2 : ℝ)
    (fun k => diracProba (point k)) (diracProba 1)
    (hμs := fun k => secondMoment_dirac_lt_top 2 (point k))
    (hμ := secondMoment_dirac_lt_top 2 1)).mp (moving_dirac_limits 2).1
  change Tendsto (fun k => diracProba (point k)) atTop (𝓝 (diracProba 1)) ∧
    Tendsto (fun k => secondMoment 2 (diracProba (point k))) atTop
      (𝓝 (secondMoment 2 (diracProba 1))) at h
  simpa only [secondMoment_two_dirac_one] using h

-- Reverse direction: use the independently verified weak and second-moment limits at center 2.
example : Tendsto (fun k => wasserstein 2 (diracProba (point k)) (diracProba 1)) atTop (𝓝 0) := by
  exact (tendsto_wasserstein_iff (p := 2) (by norm_num) (2 : ℝ)
    (fun k => diracProba (point k)) (diracProba 1)
    (hμs := fun k => secondMoment_dirac_lt_top 2 (point k))
    (hμ := secondMoment_dirac_lt_top 2 1)).mpr (moving_dirac_limits 2).2

private noncomputable def twoAtoms {X : Type*} [MeasurableSpace X] (a b : X) :
    ProbabilityMeasure X :=
  ⟨(1 / 2 : ℝ≥0∞) • Measure.dirac a + (1 / 2 : ℝ≥0∞) • Measure.dirac b, ⟨by
    simpa using ENNReal.add_halves (1 : ℝ≥0∞)⟩⟩

private theorem twoAtoms_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) (a b : X) :
    (twoAtoms a b).map f = twoAtoms (f a) (f b) := by
  apply Subtype.ext
  change Measure.map f (twoAtoms a b : Measure X) = (twoAtoms (f a) (f b) : Measure Y)
  simp [twoAtoms, Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]

private noncomputable def joint : ProbabilityMeasure (ℝ × ℝ) := twoAtoms (0, 0) (3, 1)

-- The joint law pairs 0 with 0 and 3 with 1, so its squared cost is exactly 2.
example :
    (∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(joint : Measure (ℝ × ℝ))) = 2 ∧
      wasserstein 2 (twoAtoms (0 : ℝ) 3) (twoAtoms (0 : ℝ) 1) ≤ (2 : ℝ≥0∞) ^ (1 / (2 : ℝ)) := by
  have hcost : (∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(joint : Measure (ℝ × ℝ))) = 2 := by
    simp only [joint, twoAtoms, ProbabilityMeasure.coe_mk, lintegral_add_measure,
      lintegral_smul_measure, lintegral_dirac, smul_eq_mul, edist_self, ENNReal.rpow_two,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add]
    norm_num [edist_dist, Real.dist_eq]
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]
  refine ⟨hcost, ?_⟩
  have hπ := (MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted.isCoupling_iff_map
    (twoAtoms (0 : ℝ) 3) (twoAtoms (0 : ℝ) 1) joint).2
      ⟨twoAtoms_map measurable_fst ((0, 0) : ℝ × ℝ) (3, 1),
        twoAtoms_map measurable_snd ((0, 0) : ℝ × ℝ) (3, 1)⟩
  simpa only [hcost] using wasserstein_le_of_isCoupling (by norm_num : (0 : ℝ) ≤ 2) hπ

end MathlibExtTest.MeasureTheory.OptimalTransport.WassersteinConvergence
