/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.IdentifiableHazardContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

namespace MathlibExtTest.Probability.Statistics.IdentifiableHazardContinuous

/-! ### Point-mass laws, computed from the definitions -/

/-- The observed-data law of point masses is the point mass at the observation. -/
theorem censoredObsLaw_dirac (a b : ℝ) :
    censoredObsLaw (Measure.dirac a) (Measure.dirac b) =
      Measure.dirac (censoredObsMap (a, b)) := by
  rw [censoredObsLaw, Measure.dirac_prod_dirac, Measure.map_dirac' measurable_censoredObsMap]

/-- The observable set of the point mass at `1` is `(-∞, 1]` (it contains its horizon). -/
example : observableSet (Measure.dirac (1 : ℝ)) = Iic 1 := by
  ext s
  simp [observableSet, Measure.dirac_apply' _ measurableSet_Ici]

/-- Boundary: for censoring at `1`, `h = 1` satisfies both `G[h, ∞) ≠ 0` (identification up to
`h`) and `G(h, ∞) = 0` (nothing identified beyond `h`), so the horizon is attained. -/
example : Measure.dirac (1 : ℝ) (Ici 1) ≠ 0 ∧ Measure.dirac (1 : ℝ) (Ioi 1) = 0 := by
  simp [Measure.dirac_apply' _ measurableSet_Ici, Measure.dirac_apply' _ measurableSet_Ioi]

/-- Ties count as failures: failure and censoring both at `1` is an observed failure. -/
example : censoredObsMap (1, 1) = (1, true) := by
  simp [censoredObsMap, obsTime]

/-- **The tail beyond the horizon is not identified** (computed, not via the theorem): with
censoring at `1`, failure laws `δ₂` and `δ₃` are different but give the same observed-data law,
the point mass at `(1, censored)`. -/
example : Measure.dirac (2 : ℝ) ≠ Measure.dirac 3 ∧
    censoredObsLaw (Measure.dirac 2) (Measure.dirac 1) =
      censoredObsLaw (Measure.dirac 3) (Measure.dirac (1 : ℝ)) := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrArg (fun μ : Measure ℝ => μ {2}) h
    simp [Measure.dirac_apply' _ (measurableSet_singleton _)] at this
  · rw [censoredObsLaw_dirac, censoredObsLaw_dirac]
    congr 1
    simp only [censoredObsMap, obsTime, Prod.mk.injEq]
    norm_num

/-- **Times before the horizon are identified** (computed): with censoring at `1`, failures at
`0` and at `1/2` give different observed-data laws. -/
example : censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac 1) ≠
    censoredObsLaw (Measure.dirac (1 / 2 : ℝ)) (Measure.dirac 1) := by
  rw [censoredObsLaw_dirac, censoredObsLaw_dirac]
  intro h
  have := congrArg (fun μ : Measure (ℝ × Bool) => μ {((0 : ℝ), true)}) h
  simp [Measure.dirac_apply' _ (measurableSet_singleton _), censoredObsMap, obsTime] at this
  norm_num at this

/-- **The horizon itself is identified** (computed, boundary `t = h`): with censoring at `1`, a
failure at `1` (a tie, observed) and a failure at `2` (censored) give different laws. -/
example : censoredObsLaw (Measure.dirac (1 : ℝ)) (Measure.dirac 1) ≠
    censoredObsLaw (Measure.dirac (2 : ℝ)) (Measure.dirac 1) := by
  rw [censoredObsLaw_dirac, censoredObsLaw_dirac]
  intro h
  have := congrArg (fun μ : Measure (ℝ × Bool) => μ {((1 : ℝ), true)}) h
  simp [Measure.dirac_apply' _ (measurableSet_singleton _), censoredObsMap, obsTime] at this

/-- The hazard measure of `δ₂` on `(-∞, 1]` is zero, computed from `hazardMeasure`. -/
theorem hazardMeasure_dirac_two_restrict :
    (hazardMeasure (Measure.dirac (2 : ℝ))).restrict (Iic 1) = 0 := by
  rw [hazardMeasure, restrict_withDensity measurableSet_Iic,
    Measure.restrict_eq_zero.2 (by simp [Measure.dirac_apply' _ measurableSet_Iic]),
    withDensity_zero_left]

/-- The hazard measure of `δ₁` charges `(-∞, 1]` with the terminal atom `F{1} / F[1, ∞) = 1`. -/
example : hazardMeasure (Measure.dirac (1 : ℝ)) (Iic 1) = 1 := by
  rw [hazardMeasure, withDensity_apply _ measurableSet_Iic, restrict_dirac' measurableSet_Iic]
  simp [Measure.dirac_apply' _ measurableSet_Ici]

/-! ### Non-vacuity of the main theorems -/

/-- Non-vacuity of `hazardMeasure_restrict_Ico_eq_of_censoredObsLaw_eq`: its hypotheses hold for
censoring at `1`, `h = 1`, and two failure laws with the same observed-data law. -/
example : (hazardMeasure (Measure.dirac (2 : ℝ))).restrict (Ico 0 1) =
    (hazardMeasure (Measure.dirac (3 : ℝ))).restrict (Ico 0 1) := by
  refine hazardMeasure_restrict_Ico_eq_of_censoredObsLaw_eq (G := Measure.dirac 1) (h := 1)
    (by simp [Measure.dirac_apply' _ measurableSet_Ici]) ?_
  rw [censoredObsLaw_dirac, censoredObsLaw_dirac]
  congr 1
  simp only [censoredObsMap, obsTime, Prod.mk.injEq]
  norm_num

/-- Non-vacuity of `censoredObsLaw_eq_of_restrict_Iic_eq`: `δ₂` and `δ₃` agree on `(-∞, 1]`
(both vanish there), and censoring at `1` puts no mass after `1`. -/
example : censoredObsLaw (Measure.dirac (2 : ℝ)) (Measure.dirac 1) =
    censoredObsLaw (Measure.dirac (3 : ℝ)) (Measure.dirac (1 : ℝ)) :=
  censoredObsLaw_eq_of_restrict_Iic_eq (h := 1)
    (by simp [Measure.dirac_apply' _ measurableSet_Ioi])
    (by rw [Measure.restrict_eq_zero.2 (by simp [Measure.dirac_apply' _ measurableSet_Iic]),
      Measure.restrict_eq_zero.2 (by norm_num [Measure.dirac_apply' _ measurableSet_Iic])])

/-! ### A continuous censoring law: the horizon is not attained -/

/-- Uniform censoring mass on `[0, 1]`. -/
noncomputable def unifCens : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsFiniteMeasure unifCens :=
  isFiniteMeasure_restrict.2 (by simp)

/-- Boundary: for a continuous censoring law on `[0, 1]`, `G[1, ∞) = 0`, so `h = 1` fails the
hypothesis of the identification theorems, while every `h < 1` satisfies it. -/
example : unifCens (Ici 1) = 0 ∧ unifCens (Ici (1 / 2)) ≠ 0 := by
  constructor
  · rw [unifCens, Measure.restrict_apply measurableSet_Ici]
    refine measure_mono_null (fun x hx => ?_) (Real.volume_singleton (a := 1))
    exact le_antisymm hx.2.2 hx.1
  · have hset : Ici (1 / 2 : ℝ) ∩ Icc 0 1 = Icc (1 / 2) 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by linarith, h2⟩
    rw [unifCens, Measure.restrict_apply measurableSet_Ici, hset, Real.volume_Icc]
    norm_num

end MathlibExtTest.Probability.Statistics.IdentifiableHazardContinuous
