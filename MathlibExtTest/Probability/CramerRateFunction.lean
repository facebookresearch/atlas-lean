/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerRateFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Tests: the Cramér rate function

Signature restatements of the theorems in
`MathlibExt.Probability.CramerRateFunction`, plus the concrete
demonstration that v1's definition of the rate function (supremum in `ℝ`
before `ENNReal.ofReal`) collapses to `0` for an identically constant random
vector away from its constant, while the corrected definition gives `⊤`
there.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.CramerRateFunction
open MathlibExt.Probability.CramerUpperBound

namespace MathlibExtTest.Probability.CramerRateFunction

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Signature restatement: the cumulant generating function at `0`. -/
theorem logMGFVec_zero_test {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] :
    logMGFVec X μ 0 = 0 :=
  logMGFVec_zero X

/-- Signature restatement: the cumulant generating function of a constant. -/
theorem logMGFVec_const_test {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] (t : EuclideanSpace ℝ (Fin d)) :
    logMGFVec (fun _ => c) μ t = ⟪t, c⟫_ℝ :=
  logMGFVec_const c t

/-- Extended Fenchel–Young excludes nonintegrable directions with log moment top. -/
theorem le_cramerRateFunction_test {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (x t : EuclideanSpace ℝ (Fin d)) :
    (((⟪t, x⟫_ℝ : ℝ) : EReal) - extendedLogMGFVec X μ t).toENNReal ≤
      cramerRateFunction X μ x :=
  le_cramerRateFunction X μ x t

/-- Finite-domain agreement retains the bounded-supremum formula for actual finite moments. -/
theorem cramerRateFunction_eq_ofReal_iSup_test {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hbdd : BddAbove (Set.range fun t => ⟪t, x⟫_ℝ - logMGFVec X μ t)) :
    cramerRateFunction X μ x =
      ENNReal.ofReal (⨆ t, ⟪t, x⟫_ℝ - logMGFVec X μ t) :=
  cramerRateFunction_eq_ofReal_iSup X μ hInt hbdd

/-- Signature restatement: the rate function vanishes at the mean. -/
theorem cramerRateFunction_eq_zero_at_mean_test {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ]
    (hX : Integrable X μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ) :
    cramerRateFunction X μ (∫ ω, X ω ∂μ) = 0 :=
  cramerRateFunction_eq_zero_at_mean X hX hInt

/-- The mean theorem applied to a constant random vector: its mean is the
constant, and the rate there is `0`. -/
theorem cramerRateFunction_const_mean_test {d : ℕ}
    (c : EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ] :
    cramerRateFunction (fun _ => c) μ (∫ ω, (fun _ => c) ω ∂μ) = 0 := by
  have hInt : (∫ ω, (fun _ => c) ω ∂μ) = c := by
    simp [integral_const, Measure.real]
  rw [hInt]
  exact (cramerRateFunction_const c).1

/-- Signature restatement: lower semicontinuity. -/
theorem lowerSemicontinuous_cramerRateFunction_test {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) :
    LowerSemicontinuous (cramerRateFunction X μ) :=
  lowerSemicontinuous_cramerRateFunction X μ

/-- Signature restatement: convexity. -/
theorem cramerRateFunction_convex_test {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) {x y : EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cramerRateFunction X μ (a • x + b • y) ≤
      ENNReal.ofReal a * cramerRateFunction X μ x +
        ENNReal.ofReal b * cramerRateFunction X μ y :=
  cramerRateFunction_convex X μ ha hb hab

/-- Signature restatement: the rate function of a constant random vector. -/
theorem cramerRateFunction_const_test {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] :
    cramerRateFunction (fun _ => c) μ c = 0 ∧
    ∀ x : EuclideanSpace ℝ (Fin d), x ≠ c → cramerRateFunction (fun _ => c) μ x = ⊤ :=
  cramerRateFunction_const c

/-- v1's definition of the rate function, with the supremum taken in `ℝ`
before applying `ENNReal.ofReal`. -/
noncomputable def v1RateFunction {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal (⨆ t, ⟪t, x⟫_ℝ - logMGFVec X μ t)

/-- **v1's definition collapses for a constant random vector.** For
`X = c` and `x ≠ c`, the values `⟪t, x⟫ - Λ(t) = ⟪t, x - c⟫` are
unbounded above in `ℝ`, so their supremum in `ℝ` is `0` and v1's rate
function is `0` at `x`, while the corrected rate function is `⊤` there
(see `cramerRateFunction_const`). -/
theorem v1RateFunction_const_eq_zero {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ (Fin d)) (hx : x ≠ c) :
    v1RateFunction (fun _ => c) μ x = 0 := by
  have hq : (0 : ℝ) < ‖x - c‖ ^ 2 := by
    apply sq_pos_of_pos
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hx
  have hunbdd : ¬ BddAbove (Set.range (fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, x⟫_ℝ - logMGFVec (fun _ => c) μ t)) := by
    rintro ⟨B, hB⟩
    have hmem : (⟪((B + 1) / ‖x - c‖ ^ 2) • (x - c), x⟫_ℝ -
        logMGFVec (fun _ => c) μ (((B + 1) / ‖x - c‖ ^ 2) • (x - c))) ∈
        Set.range (fun t : EuclideanSpace ℝ (Fin d) =>
          ⟪t, x⟫_ℝ - logMGFVec (fun _ => c) μ t) :=
      ⟨((B + 1) / ‖x - c‖ ^ 2) • (x - c), rfl⟩
    have hle := hB hmem
    have hval : ⟪((B + 1) / ‖x - c‖ ^ 2) • (x - c), x⟫_ℝ -
        logMGFVec (fun _ => c) μ (((B + 1) / ‖x - c‖ ^ 2) • (x - c)) = B + 1 := by
      rw [logMGFVec_const, ← inner_sub_right]
      simp [inner_smul_left, hq.ne']
    linarith
  show ENNReal.ofReal (⨆ t, ⟪t, x⟫_ℝ - logMGFVec (fun _ => c) μ t) = 0
  rw [Real.iSup_of_not_bddAbove hunbdd, ENNReal.ofReal_zero]

#print axioms cramerRateFunction_eq_ofReal_iSup
#print axioms cramerRateFunction_eq_zero_at_mean
#print axioms lowerSemicontinuous_cramerRateFunction
#print axioms cramerRateFunction_convex
#print axioms cramerRateFunction_const
#print axioms v1RateFunction_const_eq_zero

end MathlibExtTest.Probability.CramerRateFunction
