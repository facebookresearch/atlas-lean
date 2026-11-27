/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Binary unequal-cost Bayes adapter

For two dominated probability laws and finite decision costs,
subtracting the truth-dependent constants gives a nonnegative
shifted loss. The threshold rule that compares the two posterior
losses is Bayes optimal in Mathlib's estimator framework, and the
truth-only shift does not change the original-cost minimizer.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Decision.BinaryCostAdapter

/-- Finite binary cost `Cij`: the cost of decision `i` when the truth is `j`
(`false` = 0, `true` = 1). -/
def binaryCost (C00 C01 C10 C11 : ℝ) : Bool → Bool → ℝ
  | false, false => C00
  | false, true => C01
  | true, false => C10
  | true, true => C11

/-- The cost shifted by the truth-only constants `C00`, `C11`, as a Mathlib loss
(truth `θ` first, decision `y` second): `ofReal (C y θ - C θ θ)`. -/
noncomputable def binaryShiftedLoss (C00 C01 C10 C11 : ℝ) (θ y : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (binaryCost C00 C01 C10 C11 y θ - binaryCost C00 C01 C10 C11 θ θ)

/-- Binary prior `pi0 • δ_false + pi1 • δ_true` on the truth. -/
noncomputable abbrev binaryPrior (pi0 pi1 : ℝ) : Measure Bool :=
  Real.toNNReal pi0 • Measure.dirac false + Real.toNNReal pi1 • Measure.dirac true

/-- The finite-cost threshold rule: decide `true` where
`pi1 * (C01 - C11) * p1 x > pi0 * (C10 - C00) * p0 x`, the tie decision `tie` where the
two sides are equal, and `false` otherwise. -/
noncomputable def binaryCostRule {𝓧 : Type*} (pi0 pi1 C00 C01 C10 C11 : ℝ)
    (p0 p1 : 𝓧 → ℝ) (tie : Bool) (x : 𝓧) : Bool :=
  if pi0 * (C10 - C00) * p0 x < pi1 * (C01 - C11) * p1 x then true
  else if pi1 * (C01 - C11) * p1 x = pi0 * (C10 - C00) * p0 x then tie
  else false

/-- Real-valued Bayes average cost of a decision kernel `κ` under the original costs:
`pi0 * E_{κ∘P0}[C(·, 0)] + pi1 * E_{κ∘P1}[C(·, 1)]`. -/
noncomputable def binaryCostAvgRisk {𝓧 : Type*} [MeasurableSpace 𝓧]
    (C00 C01 C10 C11 : ℝ) (P : Kernel Bool 𝓧) (κ : Kernel 𝓧 Bool) (pi0 pi1 : ℝ) : ℝ :=
  pi0 * ∫ y, binaryCost C00 C01 C10 C11 y false ∂((κ ∘ₖ P) false) +
    pi1 * ∫ y, binaryCost C00 C01 C10 C11 y true ∂((κ ∘ₖ P) true)

/-! ### Encoding lemmas -/

/-- A law given by a density against `μ` is a probability measure exactly when the density
integrates to one; forward direction. -/
theorem lintegral_density_eq_one {𝓧 : Type*} [MeasurableSpace 𝓧] (μ : Measure 𝓧)
    (P : Measure 𝓧) [IsProbabilityMeasure P] (p : 𝓧 → ℝ)
    (hP : P = μ.withDensity fun x => ENNReal.ofReal (p x)) :
    ∫⁻ x, ENNReal.ofReal (p x) ∂μ = 1 := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hP]
  exact measure_univ

/-- Converse: a density integrating to one gives a probability law, so every
such density instantiates the measure-plus-density hypotheses used below. -/
theorem isProbabilityMeasure_withDensity_of_lintegral_eq_one {𝓧 : Type*}
    [MeasurableSpace 𝓧] (μ : Measure 𝓧) (p : 𝓧 → ℝ)
    (hp : ∫⁻ x, ENNReal.ofReal (p x) ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (p x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact hp

/-- The prior in the `ENNReal.ofReal` form used by Atlas `FiniteBinaryRisk`. -/
theorem binaryPrior_eq_ofReal_smul (pi0 pi1 : ℝ) :
    binaryPrior pi0 pi1 =
      ENNReal.ofReal pi0 • Measure.dirac false + ENNReal.ofReal pi1 • Measure.dirac true := by
  simp only [binaryPrior, ENNReal.smul_def, ENNReal.ofNNReal_toNNReal]

/-- The shifted loss as a table: `0` on correct decisions, `C10 - C00` on a false
positive, `C01 - C11` on a false negative (the Atlas `FiniteBinaryRisk` loss with
`cFP = C10 - C00`, `cFN = C01 - C11`). -/
theorem binaryShiftedLoss_eq_table (C00 C01 C10 C11 : ℝ) :
    binaryShiftedLoss C00 C01 C10 C11 = fun θ y =>
      if θ = y then 0
      else if θ = false then ENNReal.ofReal (C10 - C00) else ENNReal.ofReal (C01 - C11) := by
  funext θ y
  cases θ <;> cases y <;> simp [binaryShiftedLoss, binaryCost]

/-- The tie branch of the rule is the stated tie decision. -/
theorem binaryCostRule_of_tie {𝓧 : Type*} (pi0 pi1 C00 C01 C10 C11 : ℝ) (p0 p1 : 𝓧 → ℝ)
    (tie : Bool) (x : 𝓧) (h : pi1 * (C01 - C11) * p1 x = pi0 * (C10 - C00) * p0 x) :
    binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie x = tie := by
  unfold binaryCostRule
  have hlt : ¬ pi0 * (C10 - C00) * p0 x < pi1 * (C01 - C11) * p1 x := by
    rw [← h]
    exact lt_irrefl _
  rw [ite_eq_right hlt, ite_eq_left h]

/-- The rule is measurable for measurable densities. -/
theorem measurable_binaryCostRule {𝓧 : Type*} [MeasurableSpace 𝓧]
    (pi0 pi1 C00 C01 C10 C11 : ℝ) (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0)
    (hp1m : Measurable p1) (tie : Bool) :
    Measurable (binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie) := by
  unfold binaryCostRule
  have hA : Measurable fun x => pi0 * (C10 - C00) * p0 x := hp0m.const_mul _
  have hB : Measurable fun x => pi1 * (C01 - C11) * p1 x := hp1m.const_mul _
  exact Measurable.ite (measurableSet_lt hA hB) measurable_const
    (Measurable.ite (measurableSet_eq_fun hB hA) measurable_const measurable_const)

/-! ### Private helpers (not part of the pin) -/

private theorem withDensity_withDensity' {𝓧 : Type*} [MeasurableSpace 𝓧] (μ : Measure 𝓧)
    {g h : 𝓧 → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) :
    (μ.withDensity g).withDensity h = μ.withDensity (fun x => g x * h x) := by
  ext s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hg hh hs]
  simp only [Pi.mul_apply]

private theorem binaryPrior_apply_false (pi0 pi1 : ℝ) :
    binaryPrior pi0 pi1 {false} = ENNReal.ofReal pi0 := by
  simp only [binaryPrior, ENNReal.smul_def, ENNReal.ofNNReal_toNNReal, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  simp

private theorem binaryPrior_apply_true (pi0 pi1 : ℝ) :
    binaryPrior pi0 pi1 {true} = ENNReal.ofReal pi1 := by
  simp only [binaryPrior, ENNReal.smul_def, ENNReal.ofNNReal_toNNReal, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  simp

private theorem marginal_eq_withDensity {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧)
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 ≤ pi0) (hpi1 : 0 ≤ pi1) :
    Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1 =
      μ.withDensity fun x => ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) := by
  have hf0 : Measurable fun x => ENNReal.ofReal (p0 x) := hp0m.ennreal_ofReal
  have hf1 : Measurable fun x => ENNReal.ofReal (p1 x) := hp1m.ennreal_ofReal
  rw [boolKernel_comp_measure, binaryPrior_apply_true, binaryPrior_apply_false, hP0, hP1,
    ← withDensity_smul _ hf1, ← withDensity_smul _ hf0,
    ← withDensity_add_left (hf1.const_smul _) _]
  congr with x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hpi1, ← ENNReal.ofReal_mul hpi0,
    ← ENNReal.ofReal_add (mul_nonneg hpi1 (hp1 x)) (mul_nonneg hpi0 (hp0 x))]
  congr 1
  ring

private theorem core_ae_false {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) :
    ∀ᵐ x ∂(Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1),
      ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
        P0.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x =
        ENNReal.ofReal (p0 x) := by
  have hmarg := marginal_eq_withDensity μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1 pi0 pi1
    hpi0.le hpi1.le
  have hpt : ∀ x : 𝓧, ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
      (ENNReal.ofReal (p0 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x)) =
      ENNReal.ofReal (p0 x) := by
    intro x
    by_cases hx : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) = 0
    · rw [hx, zero_mul]
      have hle : pi0 * p0 x + pi1 * p1 x ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
      have h0 : pi0 * p0 x + pi1 * p1 x = 0 := le_antisymm hle
        (add_nonneg (mul_nonneg hpi0.le (hp0 x)) (mul_nonneg hpi1.le (hp1 x)))
      have h00 : pi0 * p0 x = 0 :=
        ((add_eq_zero_iff_of_nonneg (mul_nonneg hpi0.le (hp0 x))
          (mul_nonneg hpi1.le (hp1 x))).mp h0).1
      have hpx : p0 x = 0 := by
        rcases mul_eq_zero.mp h00 with h | h
        · exact absurd h (ne_of_gt hpi0)
        · exact h
      rw [hpx, ENNReal.ofReal_zero]
    · exact ENNReal.mul_div_cancel hx ENNReal.ofReal_ne_top
  have hm : Measurable fun x => ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) :=
    ((hp0m.const_mul _).add (hp1m.const_mul _)).ennreal_ofReal
  have hh : Measurable fun x : 𝓧 =>
      ENNReal.ofReal (p0 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) :=
    hp0m.ennreal_ofReal.div hm
  have hwd : (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1).withDensity
      (fun x => ENNReal.ofReal (p0 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x)) = P0 := by
    rw [hmarg, withDensity_withDensity' _ hm hh, hP0]
    congr with x
    exact hpt x
  have hadd : P0 = 0 + (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1).withDensity
      (fun x => ENNReal.ofReal (p0 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x)) := by
    rw [zero_add, hwd]
  have hae := Measure.eq_rnDeriv (μ := P0) (ν := Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1)
    (s := 0) (f := fun x => ENNReal.ofReal (p0 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x))
    hh Measure.MutuallySingular.zero_left hadd
  filter_upwards [hae] with x hx
  rw [← hx]
  exact hpt x

private theorem core_ae_true {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) :
    ∀ᵐ x ∂(Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1),
      ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
        P1.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x =
        ENNReal.ofReal (p1 x) := by
  have hmarg := marginal_eq_withDensity μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1 pi0 pi1
    hpi0.le hpi1.le
  have hpt : ∀ x : 𝓧, ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
      (ENNReal.ofReal (p1 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x)) =
      ENNReal.ofReal (p1 x) := by
    intro x
    by_cases hx : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) = 0
    · rw [hx, zero_mul]
      have hle : pi0 * p0 x + pi1 * p1 x ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
      have h0 : pi0 * p0 x + pi1 * p1 x = 0 := le_antisymm hle
        (add_nonneg (mul_nonneg hpi0.le (hp0 x)) (mul_nonneg hpi1.le (hp1 x)))
      have h00 : pi1 * p1 x = 0 :=
        ((add_eq_zero_iff_of_nonneg (mul_nonneg hpi0.le (hp0 x))
          (mul_nonneg hpi1.le (hp1 x))).mp h0).2
      have hpx : p1 x = 0 := by
        rcases mul_eq_zero.mp h00 with h | h
        · exact absurd h (ne_of_gt hpi1)
        · exact h
      rw [hpx, ENNReal.ofReal_zero]
    · exact ENNReal.mul_div_cancel hx ENNReal.ofReal_ne_top
  have hm : Measurable fun x => ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) :=
    ((hp0m.const_mul _).add (hp1m.const_mul _)).ennreal_ofReal
  have hh : Measurable fun x : 𝓧 =>
      ENNReal.ofReal (p1 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) :=
    hp1m.ennreal_ofReal.div hm
  have hwd : (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1).withDensity
      (fun x => ENNReal.ofReal (p1 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x)) = P1 := by
    rw [hmarg, withDensity_withDensity' _ hm hh, hP1]
    congr with x
    exact hpt x
  have hadd : P1 = 0 + (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1).withDensity
      (fun x => ENNReal.ofReal (p1 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x)) := by
    rw [zero_add, hwd]
  have hae := Measure.eq_rnDeriv (μ := P1) (ν := Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1)
    (s := 0) (f := fun x => ENNReal.ofReal (p1 x) / ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x))
    hh Measure.MutuallySingular.zero_left hadd
  filter_upwards [hae] with x hx
  rw [← hx]
  exact hpt x

private theorem marginal_ne_zero_ae {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧)
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 ≤ pi0) (hpi1 : 0 ≤ pi1) :
    ∀ᵐ x ∂(Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1),
      ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) ≠ 0 := by
  have hmarg := marginal_eq_withDensity μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1 pi0 pi1
    hpi0 hpi1
  have hm : Measurable fun x => ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) :=
    ((hp0m.const_mul _).add (hp1m.const_mul _)).ennreal_ofReal
  rw [hmarg, ae_withDensity_iff' hm.aemeasurable]
  exact Filter.Eventually.of_forall fun x h => h

private theorem prob_ne_top_singleton (ν : Measure Bool) [IsProbabilityMeasure ν] (b : Bool) :
    ν {b} ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by
    rw [measure_univ]
    exact ENNReal.one_lt_top))

private theorem prob_toReal_singletons_add (ν : Measure Bool) [IsProbabilityMeasure ν] :
    (ν {false}).toReal + (ν {true}).toReal = 1 := by
  have hU : ({false} : Set Bool) ∪ {true} = Set.univ := by ext b; cases b <;> simp
  have hD : Disjoint ({false} : Set Bool) {true} :=
    Set.disjoint_left.mpr (by rintro b rfl; decide)
  have hunion : ν {false} + ν {true} = 1 := by
    rw [← measure_union hD (measurableSet_singleton true), hU]
    exact measure_univ
  have h := congrArg ENNReal.toReal hunion
  rw [ENNReal.toReal_add (prob_ne_top_singleton ν false) (prob_ne_top_singleton ν true),
    ENNReal.toReal_one] at h
  exact h

private theorem integrable_bool (f : Bool → ℝ) (ν : Measure Bool) [IsFiniteMeasure ν] :
    Integrable f ν := by
  have hC : (0:ℝ) ≤ ‖f false‖ + ‖f true‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine Integrable.mono (integrable_const (‖f false‖ + ‖f true‖))
    (measurable_of_finite _).aestronglyMeasurable ?_
  filter_upwards with y
  have hCrw : ‖‖f false‖ + ‖f true‖‖ = ‖f false‖ + ‖f true‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hC]
  rw [hCrw]
  cases y
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)

private theorem isProbabilityMeasure_binaryPrior (pi0 pi1 : ℝ) (hpi0 : 0 < pi0)
    (hpi1 : 0 < pi1) (hpi : pi0 + pi1 = 1) : IsProbabilityMeasure (binaryPrior pi0 pi1) := by
  refine ⟨?_⟩
  have hsum : binaryPrior pi0 pi1 Set.univ = ENNReal.ofReal pi0 + ENNReal.ofReal pi1 := by
    simp [binaryPrior_eq_ofReal_smul, Measure.add_apply, Measure.smul_apply]
  rw [hsum, ← ENNReal.ofReal_add hpi0.le hpi1.le, hpi, ENNReal.ofReal_one]

private theorem avgRisk_binaryShiftedLoss_ne_top {𝓧 : Type*} [MeasurableSpace 𝓧]
    (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) (hpi : pi0 + pi1 = 1)
    (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01)
    (κ : Kernel 𝓧 Bool) [IsMarkovKernel κ] :
    avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1) κ
      (binaryPrior pi0 pi1) ≠ ⊤ := by
  have hπ : IsProbabilityMeasure (binaryPrior pi0 pi1) :=
    isProbabilityMeasure_binaryPrior pi0 pi1 hpi0 hpi1 hpi
  have hval : ∀ r : ℝ, r ≤ (C10 - C00) + (C01 - C11) →
      ENNReal.ofReal r ≤ ((Real.toNNReal ((C10 - C00) + (C01 - C11)) : ℝ≥0) : ℝ≥0∞) := by
    intro r hr
    rw [ENNReal.ofNNReal_toNNReal]
    exact ENNReal.ofReal_le_ofReal hr
  have hC : ∀ θ y : Bool, binaryShiftedLoss C00 C01 C10 C11 θ y ≤
      ((Real.toNNReal ((C10 - C00) + (C01 - C11)) : ℝ≥0) : ℝ≥0∞) := by
    intro θ y
    cases θ <;> cases y <;> simp only [binaryShiftedLoss, binaryCost] <;>
      exact hval _ (by linarith)
  have hle := avgRisk_le_mul (Kernel.boolKernel P0 P1) κ (binaryPrior pi0 pi1) hC
  refine ne_of_lt (lt_of_le_of_lt hle ?_)
  simp

/-! ### Posterior losses and Bayes optimality -/

/-- **Posterior losses.** Almost everywhere under the marginal law of the data, the
posterior expected shifted loss of each decision, multiplied by the marginal density
`pi0 * p0 + pi1 * p1`, is `pi0 * (C10 - C00) * p0` for decision `true` and
`pi1 * (C01 - C11) * p1` for decision `false`. -/
theorem posterior_lintegral_binaryShiftedLoss {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) (hpi : pi0 + pi1 = 1)
    (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01) :
    ∀ᵐ x ∂(Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1), ∀ y : Bool,
      ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
          ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ y
            ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x =
        ENNReal.ofReal (if y then pi0 * (C10 - C00) * p0 x else pi1 * (C01 - C11) * p1 x) := by
  have hpost0 := posterior_boolKernel_apply_false P0 P1 (binaryPrior pi0 pi1)
  have hpost1 := posterior_boolKernel_apply_true P0 P1 (binaryPrior pi0 pi1)
  have hcore0 := core_ae_false μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1 pi0 pi1 hpi0 hpi1
  have hcore1 := core_ae_true μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1 pi0 pi1 hpi0 hpi1
  have e00 : binaryShiftedLoss C00 C01 C10 C11 false false = 0 := by
    simp [binaryShiftedLoss, binaryCost]
  have e01 : binaryShiftedLoss C00 C01 C10 C11 false true = ENNReal.ofReal (C10 - C00) := by
    simp [binaryShiftedLoss, binaryCost]
  have e10 : binaryShiftedLoss C00 C01 C10 C11 true false = ENNReal.ofReal (C01 - C11) := by
    simp [binaryShiftedLoss, binaryCost]
  have e11 : binaryShiftedLoss C00 C01 C10 C11 true true = 0 := by
    simp [binaryShiftedLoss, binaryCost]
  filter_upwards [hpost0, hpost1, hcore0, hcore1] with x hx0 hx1 hcx0 hcx1
  intro y
  cases y
  · show ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
        ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
          ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x =
        ENNReal.ofReal (pi1 * (C01 - C11) * p1 x)
    simp only [lintegral_fintype, Fintype.sum_bool, e00, e10]
    rw [hx1, binaryPrior_apply_true]
    simp only [zero_mul, add_zero]
    have hcalc : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
        (ENNReal.ofReal (C01 - C11) *
          (ENNReal.ofReal pi1 * P1.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x)) =
        ENNReal.ofReal (C01 - C11) * ENNReal.ofReal pi1 * ENNReal.ofReal (p1 x) := by
      have hring : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
          (ENNReal.ofReal (C01 - C11) *
            (ENNReal.ofReal pi1 * P1.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x)) =
          ENNReal.ofReal (C01 - C11) * ENNReal.ofReal pi1 *
            (ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
              P1.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x) := by
        ring
      rw [hring, hcx1]
    rw [hcalc, ← ENNReal.ofReal_mul (sub_nonneg.mpr hC1.le),
      ← ENNReal.ofReal_mul (mul_nonneg (sub_nonneg.mpr hC1.le) hpi1.le)]
    congr 1
    ring
  · show ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
        ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
          ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x =
        ENNReal.ofReal (pi0 * (C10 - C00) * p0 x)
    simp only [lintegral_fintype, Fintype.sum_bool, e11, e01]
    rw [hx0, binaryPrior_apply_false]
    simp only [zero_mul, zero_add]
    have hcalc : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
        (ENNReal.ofReal (C10 - C00) *
          (ENNReal.ofReal pi0 * P0.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x)) =
        ENNReal.ofReal (C10 - C00) * ENNReal.ofReal pi0 * ENNReal.ofReal (p0 x) := by
      have hring : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
          (ENNReal.ofReal (C10 - C00) *
            (ENNReal.ofReal pi0 * P0.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x)) =
          ENNReal.ofReal (C10 - C00) * ENNReal.ofReal pi0 *
            (ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
              P0.rnDeriv (Kernel.boolKernel P0 P1 ∘ₘ binaryPrior pi0 pi1) x) := by
        ring
      rw [hring, hcx0]
    rw [hcalc, ← ENNReal.ofReal_mul (sub_nonneg.mpr hC0.le),
      ← ENNReal.ofReal_mul (mul_nonneg (sub_nonneg.mpr hC0.le) hpi0.le)]
    congr 1
    ring

/-- The threshold rule is a measurable posterior-loss minimizer
(`ProbabilityTheory.IsArgminEstimator`) for the shifted loss. -/
theorem isArgminEstimator_binaryCostRule {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) (hpi : pi0 + pi1 = 1)
    (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01) (tie : Bool) :
    IsArgminEstimator (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1)
      (binaryPrior pi0 pi1) (binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie) := by
  have hpost := posterior_lintegral_binaryShiftedLoss μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1
    pi0 pi1 hpi0 hpi1 hpi C00 C01 C10 C11 hC0 hC1
  have hne := marginal_ne_zero_ae μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1 pi0 pi1 hpi0.le
    hpi1.le
  refine ⟨measurable_binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 hp0m hp1m tie, ?_⟩
  filter_upwards [hpost, hne] with x hx hcx
  have hLf : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
      ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
        ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x =
      ENNReal.ofReal (pi1 * (C01 - C11) * p1 x) := hx false
  have hLt : ENNReal.ofReal (pi0 * p0 x + pi1 * p1 x) *
      ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
        ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x =
      ENNReal.ofReal (pi0 * (C10 - C00) * p0 x) := hx true
  have hAf : 0 ≤ pi1 * (C01 - C11) * p1 x :=
    mul_nonneg (mul_nonneg hpi1.le (sub_nonneg.mpr hC1.le)) (hp1 x)
  have hAt : 0 ≤ pi0 * (C10 - C00) * p0 x :=
    mul_nonneg (mul_nonneg hpi0.le (sub_nonneg.mpr hC0.le)) (hp0 x)
  have hord : ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
        ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ≤
        ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
          ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ↔
      pi1 * (C01 - C11) * p1 x ≤ pi0 * (C10 - C00) * p0 x := by
    rw [← ENNReal.ofReal_le_ofReal_iff hAt, ← hLf, ← hLt]
    exact (ENNReal.mul_le_mul_iff_right hcx ENNReal.ofReal_ne_top).symm
  have hord2 : ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
        ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ≤
        ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
          ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ↔
      pi0 * (C10 - C00) * p0 x ≤ pi1 * (C01 - C11) * p1 x := by
    rw [← ENNReal.ofReal_le_ofReal_iff hAf, ← hLt, ← hLf]
    exact (ENNReal.mul_le_mul_iff_right hcx ENNReal.ofReal_ne_top).symm
  by_cases h1 : pi0 * (C10 - C00) * p0 x < pi1 * (C01 - C11) * p1 x
  · have hfx : binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie x = true := by
      unfold binaryCostRule
      rw [ite_eq_left h1]
    have hle : ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
          ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ≤
          ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
            ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x :=
      le_of_lt (lt_of_not_ge (mt hord.mp (not_le_of_gt h1)))
    rw [hfx]
    refine le_antisymm (le_iInf fun y => ?_) (iInf_le _ true)
    cases y
    · exact hle
    · exact le_rfl
  · by_cases h2 : pi1 * (C01 - C11) * p1 x = pi0 * (C10 - C00) * p0 x
    · have hfx : binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie x = tie := by
        unfold binaryCostRule
        rw [ite_eq_right h1, ite_eq_left h2]
      have hle1 : ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
            ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ≤
            ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
              ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x :=
        hord.mpr h2.le
      have hle2 : ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
            ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ≤
            ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
              ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x :=
        hord2.mpr h2.ge
      rw [hfx]
      cases tie
      · refine le_antisymm (le_iInf fun y => ?_) (iInf_le _ false)
        cases y
        · exact le_rfl
        · exact hle1
      · refine le_antisymm (le_iInf fun y => ?_) (iInf_le _ true)
        cases y
        · exact hle2
        · exact le_rfl
    · have hfx : binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie x = false := by
        unfold binaryCostRule
        rw [ite_eq_right h1, ite_eq_right h2]
      have hle : ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ false
            ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x ≤
            ∫⁻ θ, binaryShiftedLoss C00 C01 C10 C11 θ true
              ∂((Kernel.boolKernel P0 P1)†(binaryPrior pi0 pi1)) x :=
        hord.mpr (le_of_not_gt h1)
      rw [hfx]
      refine le_antisymm (le_iInf fun y => ?_) (iInf_le _ false)
      cases y
      · exact le_rfl
      · exact hle

/-- **Finite-cost binary Bayes test.** For two laws dominated by `μ` with measurable
nonnegative densities `p0`, `p1`, positive priors summing to one and costs with
`C10 > C00`, `C01 > C11`, the rule choosing `1` where
`pi1 * (C01 - C11) * p1 > pi0 * (C10 - C00) * p0` (tie decision `tie` on equality) is
measurable, and its deterministic decision kernel attains the Bayes risk of the shifted
loss in Mathlib's framework (`ProbabilityTheory.IsBayesEstimator`). -/
theorem isBayesEstimator_binaryCostRule {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) (hpi : pi0 + pi1 = 1)
    (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01) (tie : Bool) :
    ∃ hf : Measurable (binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie),
      IsBayesEstimator (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1)
        (Kernel.deterministic _ hf) (binaryPrior pi0 pi1) := by
  have harg := isArgminEstimator_binaryCostRule μ P0 P1 p0 p1 hp0m hp1m hp0 hp1 hP0 hP1
    pi0 pi1 hpi0 hpi1 hpi C00 C01 C10 C11 hC0 hC1 tie
  have hl : Measurable (Function.uncurry (binaryShiftedLoss C00 C01 C10 C11)) :=
    measurable_of_finite _
  exact ⟨harg.measurable, harg.isBayesEstimator hl⟩

/-- **Truth-only shift.** For every Markov decision kernel, the weighted cost
`binaryCostAvgRisk` of the original costs, for positive weights `pi0` and `pi1`, equals the real
part (`ENNReal.toReal`, which sends `∞` to `0`) of Mathlib's `avgRisk` of the shifted loss under
`binaryPrior pi0 pi1`, plus the constant `pi0 * C00 + pi1 * C11`. The weights need not sum to
`1`; when they do, the weighted cost is the Bayes expectation under the prior `(pi0, pi1)`. That
the shift does not change the minimizer is a consequence this theorem does not state. -/
theorem binaryCostAvgRisk_eq_toReal_avgRisk_add {𝓧 : Type*} [MeasurableSpace 𝓧]
    (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1)
    (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01)
    (κ : Kernel 𝓧 Bool) [IsMarkovKernel κ] :
    binaryCostAvgRisk C00 C01 C10 C11 (Kernel.boolKernel P0 P1) κ pi0 pi1 =
      (avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1) κ
          (binaryPrior pi0 pi1)).toReal + (pi0 * C00 + pi1 * C11) := by
  haveI hprob0 : IsProbabilityMeasure ((κ ∘ₖ Kernel.boolKernel P0 P1) false) := by
    rw [Kernel.comp_apply, Kernel.boolKernel_false]
    infer_instance
  haveI hprob1 : IsProbabilityMeasure ((κ ∘ₖ Kernel.boolKernel P0 P1) true) := by
    rw [Kernel.comp_apply, Kernel.boolKernel_true]
    infer_instance
  have hsum0 := prob_toReal_singletons_add ((κ ∘ₖ Kernel.boolKernel P0 P1) false)
  have hsum1 := prob_toReal_singletons_add ((κ ∘ₖ Kernel.boolKernel P0 P1) true)
  have e00 : binaryShiftedLoss C00 C01 C10 C11 false false = 0 := by
    simp [binaryShiftedLoss, binaryCost]
  have e01 : binaryShiftedLoss C00 C01 C10 C11 false true = ENNReal.ofReal (C10 - C00) := by
    simp [binaryShiftedLoss, binaryCost]
  have e10 : binaryShiftedLoss C00 C01 C10 C11 true false = ENNReal.ofReal (C01 - C11) := by
    simp [binaryShiftedLoss, binaryCost]
  have e11 : binaryShiftedLoss C00 C01 C10 C11 true true = 0 := by
    simp [binaryShiftedLoss, binaryCost]
  have hexpand : avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1) κ
      (binaryPrior pi0 pi1) =
      ENNReal.ofReal (C10 - C00) * ((κ ∘ₖ Kernel.boolKernel P0 P1) false) {true} *
        ENNReal.ofReal pi0 +
      ENNReal.ofReal (C01 - C11) * ((κ ∘ₖ Kernel.boolKernel P0 P1) true) {false} *
        ENNReal.ofReal pi1 := by
    simp only [avgRisk, lintegral_fintype, Fintype.sum_bool, e00, e01, e10, e11,
      binaryPrior_apply_false, binaryPrior_apply_true]
    ring
  have hLHS : binaryCostAvgRisk C00 C01 C10 C11 (Kernel.boolKernel P0 P1) κ pi0 pi1 =
      pi0 * ((((κ ∘ₖ Kernel.boolKernel P0 P1) false) {true}).toReal * C10 +
        (((κ ∘ₖ Kernel.boolKernel P0 P1) false) {false}).toReal * C00) +
      pi1 * ((((κ ∘ₖ Kernel.boolKernel P0 P1) true) {false}).toReal * C01 +
        (((κ ∘ₖ Kernel.boolKernel P0 P1) true) {true}).toReal * C11) := by
    simp only [binaryCostAvgRisk,
      integral_fintype (integrable_bool (fun y => binaryCost C00 C01 C10 C11 y false)
        ((κ ∘ₖ Kernel.boolKernel P0 P1) false)),
      integral_fintype (integrable_bool (fun y => binaryCost C00 C01 C10 C11 y true)
        ((κ ∘ₖ Kernel.boolKernel P0 P1) true)),
      Fintype.sum_bool, Measure.real_def, smul_eq_mul]
    simp only [binaryCost]
    ring
  have hfin0 : ENNReal.ofReal (C10 - C00) * ((κ ∘ₖ Kernel.boolKernel P0 P1) false) {true} *
      ENNReal.ofReal pi0 ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (prob_ne_top_singleton ((κ ∘ₖ Kernel.boolKernel P0 P1) false) true))
      ENNReal.ofReal_ne_top
  have hfin1 : ENNReal.ofReal (C01 - C11) * ((κ ∘ₖ Kernel.boolKernel P0 P1) true) {false} *
      ENNReal.ofReal pi1 ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (prob_ne_top_singleton ((κ ∘ₖ Kernel.boolKernel P0 P1) true) false))
      ENNReal.ofReal_ne_top
  rw [hLHS, hexpand, ENNReal.toReal_add hfin0 hfin1]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hC0.le),
    ENNReal.toReal_ofReal hpi0.le, ENNReal.toReal_ofReal (sub_nonneg.mpr hC1.le),
    ENNReal.toReal_ofReal hpi1.le]
  linear_combination (pi0 * C00) * hsum0 + (pi1 * C11) * hsum1

/-- **Original-cost optimality.** Under the hypotheses above, the threshold rule minimizes
the real Bayes average of the original costs `Cij` over all Markov decision kernels. -/
theorem binaryCostRule_minimizes_binaryCostAvgRisk {𝓧 : Type*} [MeasurableSpace 𝓧]
    (μ : Measure 𝓧) (P0 P1 : Measure 𝓧) [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (p0 p1 : 𝓧 → ℝ) (hp0m : Measurable p0) (hp1m : Measurable p1)
    (hp0 : ∀ x, 0 ≤ p0 x) (hp1 : ∀ x, 0 ≤ p1 x)
    (hP0 : P0 = μ.withDensity fun x => ENNReal.ofReal (p0 x))
    (hP1 : P1 = μ.withDensity fun x => ENNReal.ofReal (p1 x))
    (pi0 pi1 : ℝ) (hpi0 : 0 < pi0) (hpi1 : 0 < pi1) (hpi : pi0 + pi1 = 1)
    (C00 C01 C10 C11 : ℝ) (hC0 : C00 < C10) (hC1 : C11 < C01) (tie : Bool) :
    ∃ hf : Measurable (binaryCostRule pi0 pi1 C00 C01 C10 C11 p0 p1 tie),
      ∀ κ : Kernel 𝓧 Bool, IsMarkovKernel κ →
        binaryCostAvgRisk C00 C01 C10 C11 (Kernel.boolKernel P0 P1)
            (Kernel.deterministic _ hf) pi0 pi1 ≤
          binaryCostAvgRisk C00 C01 C10 C11 (Kernel.boolKernel P0 P1) κ pi0 pi1 := by
  obtain ⟨hf, hbayes⟩ := isBayesEstimator_binaryCostRule μ P0 P1 p0 p1 hp0m hp1m hp0 hp1
    hP0 hP1 pi0 pi1 hpi0 hpi1 hpi C00 C01 C10 C11 hC0 hC1 tie
  refine ⟨hf, fun κ hκ => ?_⟩
  haveI := hκ
  have hshift_rule := binaryCostAvgRisk_eq_toReal_avgRisk_add P0 P1 pi0 pi1 hpi0 hpi1
    C00 C01 C10 C11 hC0 hC1 (Kernel.deterministic _ hf)
  have hshift_κ := binaryCostAvgRisk_eq_toReal_avgRisk_add P0 P1 pi0 pi1 hpi0 hpi1
    C00 C01 C10 C11 hC0 hC1 κ
  rw [hshift_rule, hshift_κ]
  have hle : avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1)
      (Kernel.deterministic _ hf) (binaryPrior pi0 pi1) ≤
      avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1) κ
        (binaryPrior pi0 pi1) := by
    calc avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1)
            (Kernel.deterministic _ hf) (binaryPrior pi0 pi1)
        = bayesRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1)
            (binaryPrior pi0 pi1) := hbayes
      _ ≤ avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1) κ
            (binaryPrior pi0 pi1) := bayesRisk_le_avgRisk _ _ _ _
  have hfin : avgRisk (binaryShiftedLoss C00 C01 C10 C11) (Kernel.boolKernel P0 P1) κ
      (binaryPrior pi0 pi1) ≠ ⊤ :=
    avgRisk_binaryShiftedLoss_ne_top P0 P1 pi0 pi1 hpi0 hpi1 hpi C00 C01 C10 C11 hC0 hC1 κ
  have hmono := ENNReal.toReal_mono hfin hle
  linarith

/-! ### Validation -/

/-- Asymmetric costs `C00 = 0, C01 = 4, C10 = 2, C11 = 1`: a false positive costs
`C10 - C00 = 2`, a false negative `C01 - C11 = 3`. -/
theorem binaryShiftedLoss_asymmetric_example :
    binaryShiftedLoss 0 4 2 1 false true = 2 ∧ binaryShiftedLoss 0 4 2 1 true false = 3 ∧
      binaryShiftedLoss 0 4 2 1 false false = 0 ∧ binaryShiftedLoss 0 4 2 1 true true = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [binaryShiftedLoss, binaryCost]; norm_num

/-- Asymmetric priors `pi0 = 1/4, pi1 = 3/4` and the costs above, at a point with
`p0 = 2`, `p1 = 1`: `3/4 * 3 * 1 > 1/4 * 2 * 2`, so the rule decides `true`. -/
theorem binaryCostRule_asymmetric_example (tie : Bool) :
    binaryCostRule (1 / 4) (3 / 4) 0 4 2 1 (fun _ : Unit => (2 : ℝ)) (fun _ => 1) tie () =
      true := by
  simp only [binaryCostRule]
  rw [ite_eq_left (by norm_num)]

/-- Transposing `C01` and `C10` flips the decision at the same point:
`3/4 * 1 * 1 < 1/4 * 4 * 2`. -/
theorem binaryCostRule_transposed_costs_example (tie : Bool) :
    binaryCostRule (1 / 4) (3 / 4) 0 2 4 1 (fun _ : Unit => (2 : ℝ)) (fun _ => 1) tie () =
      false := by
  simp only [binaryCostRule]
  rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]

/-- Swapping the priors flips the decision at the same point: `1/4 * 3 * 1 < 3/4 * 2 * 2`. -/
theorem binaryCostRule_swapped_priors_example (tie : Bool) :
    binaryCostRule (3 / 4) (1 / 4) 0 4 2 1 (fun _ : Unit => (2 : ℝ)) (fun _ => 1) tie () =
      false := by
  simp only [binaryCostRule]
  rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]

/-- Zero-one costs give the zero-one loss `if θ = y then 0 else 1`. -/
theorem binaryShiftedLoss_zeroOne :
    binaryShiftedLoss 0 1 1 0 = fun θ y => if θ = y then 0 else 1 := by
  funext θ y
  cases θ <;> cases y <;> simp [binaryShiftedLoss, binaryCost]

/-- Zero-one costs and equal priors: the rule is the likelihood-ratio-one
(posterior-argmax) test, with the tie set `{p1 = p0}` sent to `tie`. -/
theorem binaryCostRule_zeroOne_equalPrior {𝓧 : Type*} (p0 p1 : 𝓧 → ℝ) (tie : Bool)
    (x : 𝓧) :
    binaryCostRule (1 / 2) (1 / 2) 0 1 1 0 p0 p1 tie x =
      if p0 x < p1 x then true else if p1 x = p0 x then tie else false := by
  have hlt : (1 / 2 : ℝ) * (1 - 0) * p0 x < (1 / 2 : ℝ) * (1 - 0) * p1 x ↔ p0 x < p1 x := by
    constructor <;> intro h <;> linarith
  have heq : (1 / 2 : ℝ) * (1 - 0) * p1 x = (1 / 2 : ℝ) * (1 - 0) * p0 x ↔ p1 x = p0 x := by
    constructor <;> intro h <;> linarith
  simp only [binaryCostRule, hlt, heq]

/-- Violated premise `C10 > C00`: with `C00 = 1, C01 = 1, C10 = 0, C11 = 0`, one
observation point, equal priors and the constant decision `true`, the original average
cost is `0` but the clipped shifted risk plus `pi0 * C00 + pi1 * C11` is `1/2`. -/
theorem binaryCostAvgRisk_ne_shifted_of_cost_inversion :
    binaryCostAvgRisk 1 1 0 0
        (Kernel.boolKernel (Measure.dirac ()) (Measure.dirac ()))
        (Kernel.const Unit (Measure.dirac true)) (1 / 2) (1 / 2) ≠
      (avgRisk (binaryShiftedLoss 1 1 0 0)
          (Kernel.boolKernel (Measure.dirac ()) (Measure.dirac ()))
          (Kernel.const Unit (Measure.dirac true)) (binaryPrior (1 / 2) (1 / 2))).toReal +
        (1 / 2 * 1 + 1 / 2 * 0) := by
  have hcomp : ∀ b : Bool, ((Kernel.const Unit (Measure.dirac true)) ∘ₖ
      (Kernel.boolKernel (Measure.dirac ()) (Measure.dirac ()))) b = Measure.dirac true := by
    intro b
    cases b <;> simp
  have hLHS : binaryCostAvgRisk 1 1 0 0
        (Kernel.boolKernel (Measure.dirac ()) (Measure.dirac ()))
        (Kernel.const Unit (Measure.dirac true)) (1 / 2) (1 / 2) = 0 := by
    simp [binaryCostAvgRisk, binaryCost]
  have havg : avgRisk (binaryShiftedLoss 1 1 0 0)
        (Kernel.boolKernel (Measure.dirac ()) (Measure.dirac ()))
        (Kernel.const Unit (Measure.dirac true)) (binaryPrior (1 / 2) (1 / 2)) = 0 := by
    have e1 : binaryShiftedLoss 1 1 0 0 false false = 0 := by simp [binaryShiftedLoss, binaryCost]
    have e2 : binaryShiftedLoss 1 1 0 0 false true = 0 := by
      simp only [binaryShiftedLoss, binaryCost]
      exact ENNReal.ofReal_of_nonpos (by norm_num)
    have e3 : binaryShiftedLoss 1 1 0 0 true true = 0 := by simp [binaryShiftedLoss, binaryCost]
    simp only [avgRisk, lintegral_fintype, hcomp]
    simp [e2, e3]
  rw [hLHS, havg, ENNReal.toReal_zero]
  norm_num

end MathlibExt.Probability.Decision.BinaryCostAdapter
