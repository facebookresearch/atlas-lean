/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Decision.Risk.Countable
public import Mathlib.Probability.Kernel.Basic

/-!
# Finite unequal-cost binary risk

Finite unequal-cost binary risk equals Mathlib's canonical finite `avgRisk`
for the loss table that charges `cFP` on a false positive and `cFN` on a
false negative.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace MathlibExt.Probability.Decision

/-- Production statement (leaf F12-L-BINARY-RISK).

Finite unequal-cost binary risk equals Mathlib's canonical finite `avgRisk`.
Parameter `θ : Bool` (`false` = negative, `true` = positive), decisions in `Bool`,
observations in a finite type `𝒳`. Loss table: `0` on correct decisions,
`cFP` (`ENNReal.ofReal`) on `false ↦ true`, `cFN` on `true ↦ false`.
Experiment `P` is `Kernel.boolKernel P0meas P1meas` with `P0meas`/`P1meas` the
finite Dirac mixtures of the normalized tables `P0`/`P1`; prior is the
`π`-mixture of Diracs on `Bool`; decision kernel sends `x` to the
`δ x`-Bernoulli measure on `Bool`. The real risk is
`(1-π)·cFP·∑ P0·δ + π·cFN·∑ P1·(1-δ)`, and `avgRisk` is finite (`≠ ⊤`). -/
theorem finiteBinaryRisk_eq_avgRisk
    {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [Fintype 𝒳]
    (P0 P1 δ : 𝒳 → ℝ) (π cFP cFN : ℝ)
    (hP0 : ∀ x, 0 ≤ P0 x) (hP0sum : ∑ x, P0 x = 1)
    (hP1 : ∀ x, 0 ≤ P1 x) (hP1sum : ∑ x, P1 x = 1)
    (hδ : ∀ x, δ x ∈ Set.Icc (0 : ℝ) 1)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hcFP : 0 < cFP) (hcFN : 0 < cFN) :
    (avgRisk
        (fun θ y => if θ = y then 0
          else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        (Kernel.boolKernel
          (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
          (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
        (Kernel.ofFunOfCountable (fun x =>
          ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true))
        (ENNReal.ofReal (1 - π) • Measure.dirac false
          + ENNReal.ofReal π • Measure.dirac true) ≠ ⊤)
      ∧ (avgRisk
          (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
          (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
          (Kernel.ofFunOfCountable (fun x =>
            ENNReal.ofReal (1 - δ x) • Measure.dirac false
              + ENNReal.ofReal (δ x) • Measure.dirac true))
          (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true)).toReal
        = (1 - π) * cFP * (∑ x, P0 x * δ x) + π * cFN * (∑ x, P1 x * (1 - δ x)) := by
  have hδ0 : ∀ x, 0 ≤ δ x := fun x => (hδ x).1
  have hδ1 : ∀ x, δ x ≤ 1 := fun x => (hδ x).2
  have h1δ : ∀ x, 0 ≤ 1 - δ x := fun x => sub_nonneg.mpr (hδ1 x)
  have hcFP0 : 0 ≤ cFP := hcFP.le
  have hcFN0 : 0 ≤ cFN := hcFN.le
  have hπ01 : 0 ≤ π := hπ0.le
  have h1π : 0 ≤ 1 - π := sub_nonneg.mpr hπ1.le
  have hS0 : 0 ≤ ∑ x, P0 x * δ x :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hP0 x) (hδ0 x))
  have hS1 : 0 ≤ ∑ x, P1 x * (1 - δ x) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hP1 x) (h1δ x))
  have hker_false : ∀ x : 𝒳,
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if True then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        ∂(((Kernel.ofFunOfCountable (fun x =>
          ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true) : Kernel 𝒳 Bool)) x))
      = ENNReal.ofReal (δ x * cFP) := by
    intro x
    show (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if True then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        ∂(ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true)) = _
    rw [lintegral_add_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    simp only [ite_true, ite_eq_right (show (false:Bool) ≠ true from by decide), mul_zero, zero_add]
    rw [← ENNReal.ofReal_mul (hδ0 x)]
  have hker_true : ∀ x : 𝒳,
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        ∂(((Kernel.ofFunOfCountable (fun x =>
          ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true) : Kernel 𝒳 Bool)) x))
      = ENNReal.ofReal ((1 - δ x) * cFN) := by
    intro x
    show (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        ∂(ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true)) = _
    rw [lintegral_add_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    simp only [ite_eq_right (show (true:Bool) ≠ false from by decide), ite_true, mul_zero, add_zero]
    rw [← ENNReal.ofReal_mul (h1δ x)]
  have hinner_false :
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        ∂(((Kernel.ofFunOfCountable (fun x =>
          ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true) : Kernel 𝒳 Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x)) false))
      = ENNReal.ofReal (cFP * ∑ x, P0 x * δ x) := by
    have hm : Measurable (fun y : Bool => if (false:Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [hker_false]
    rw [Kernel.boolKernel_false]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have hterm : ∀ x : 𝒳, ENNReal.ofReal (P0 x) * ENNReal.ofReal (δ x * cFP)
        = ENNReal.ofReal (P0 x * (δ x * cFP)) := fun x => (ENNReal.ofReal_mul (hP0 x)).symm
    simp only [hterm]
    have hnn : ∀ i ∈ (Finset.univ : Finset 𝒳), 0 ≤ P0 i * (δ i * cFP) :=
      fun i _ => mul_nonneg (hP0 i) (mul_nonneg (hδ0 i) hcFP0)
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hinner_true :
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        ∂(((Kernel.ofFunOfCountable (fun x =>
          ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true) : Kernel 𝒳 Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x)) true))
      = ENNReal.ofReal (cFN * ∑ x, P1 x * (1 - δ x)) := by
    have hm : Measurable (fun y : Bool => if (true:Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [hker_true]
    rw [Kernel.boolKernel_true]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have hterm : ∀ x : 𝒳, ENNReal.ofReal (P1 x) * ENNReal.ofReal ((1 - δ x) * cFN)
        = ENNReal.ofReal (P1 x * ((1 - δ x) * cFN)) := fun x => (ENNReal.ofReal_mul (hP1 x)).symm
    simp only [hterm]
    have hnn : ∀ i ∈ (Finset.univ : Finset 𝒳), 0 ≤ P1 i * ((1 - δ i) * cFN) :=
      fun i _ => mul_nonneg (hP1 i) (mul_nonneg (h1δ i) hcFN0)
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hpi_false : (ENNReal.ofReal (1 - π) • Measure.dirac false
        + ENNReal.ofReal π • Measure.dirac true) {false} = ENNReal.ofReal (1 - π) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∈ ({false} : Set Bool) := by simp
    have h2 : true ∉ ({false} : Set Bool) := by simp
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_one, mul_zero, add_zero]
  have hpi_true : (ENNReal.ofReal (1 - π) • Measure.dirac false
        + ENNReal.ofReal π • Measure.dirac true) {true} = ENNReal.ofReal π := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∉ ({true} : Set Bool) := by simp
    have h2 : true ∈ ({true} : Set Bool) := by simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_zero, mul_one, zero_add]
  have havg : avgRisk
        (fun θ y => if θ = y then 0
          else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
        (Kernel.boolKernel
          (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
          (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
        (Kernel.ofFunOfCountable (fun x =>
          ENNReal.ofReal (1 - δ x) • Measure.dirac false
            + ENNReal.ofReal (δ x) • Measure.dirac true))
        (ENNReal.ofReal (1 - π) • Measure.dirac false
          + ENNReal.ofReal π • Measure.dirac true)
      = ENNReal.ofReal ((1 - π) * cFP * (∑ x, P0 x * δ x) + π * cFN * (∑ x, P1 x * (1 - δ x))) := by
    rw [avgRisk_fintype, Fintype.sum_bool, hinner_true, hinner_false, hpi_true, hpi_false]
    have hA : 0 ≤ cFN * ∑ x, P1 x * (1 - δ x) := mul_nonneg hcFN0 hS1
    have hB : 0 ≤ cFP * ∑ x, P0 x * δ x := mul_nonneg hcFP0 hS0
    rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB]
    have hC : 0 ≤ (cFN * ∑ x, P1 x * (1 - δ x)) * π := mul_nonneg hA hπ01
    have hD : 0 ≤ (cFP * ∑ x, P0 x * δ x) * (1 - π) := mul_nonneg hB h1π
    rw [← ENNReal.ofReal_add hC hD]
    congr 1
    ring
  have hRHS : 0 ≤ (1 - π) * cFP * (∑ x, P0 x * δ x) + π * cFN * (∑ x, P1 x * (1 - δ x)) :=
    add_nonneg (mul_nonneg (mul_nonneg h1π hcFP0) hS0) (mul_nonneg (mul_nonneg hπ01 hcFN0) hS1)
  constructor
  · rw [havg]
    exact ENNReal.ofReal_ne_top
  · rw [havg, ENNReal.toReal_ofReal hRHS]

end MathlibExt.Probability.Decision
