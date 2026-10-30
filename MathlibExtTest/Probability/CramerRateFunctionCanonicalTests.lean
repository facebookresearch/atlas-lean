/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerRateFunction
public import MathlibExt.Probability.LegendreTransform
public import MathlibExt.Probability.LargeDeviationPrinciple
public import MathlibExtTest.Probability.CramerRateFunctionExponentialFixture

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace
open MathlibExt.Probability.CramerRateFunction
open MathlibExtTest.Probability.CramerRateFunctionExponentialFixture

namespace MathlibExtTest.Probability.CramerRateFunctionCanonicalTests

/-- The actual law has finite extended log moments precisely below one. -/
theorem exponential_log_of_lt_one {t : ℝ} (ht : t < 1) :
    extendedLogMGFVec oneVector (expMeasure 1) (oneVector t) =
      ((-Real.log (1 - t) : ℝ) : EReal) := by
  unfold extendedLogMGFVec
  simp_rw [inner_oneVector]
  rw [lintegral_exp_of_lt_one ht, ENNReal.log_ofReal_of_pos
    (div_pos zero_lt_one (sub_pos.mpr ht))]
  simp

/-- The boundary t=1 and all larger directions have an infinite log moment. -/
theorem exponential_log_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    extendedLogMGFVec oneVector (expMeasure 1) (oneVector t) = ⊤ := by
  unfold extendedLogMGFVec
  simp_rw [inner_oneVector]
  rw [lintegral_exp_of_one_le ht, ENNReal.log_top]

/-- The positive-x rate is the finite Cramér rate of the actual exponential law. -/
theorem exponential_rate_of_pos {x : ℝ} (hx : 0 < x) :
    cramerRateFunction oneVector (expMeasure 1) (oneVector x) =
      ENNReal.ofReal (x - 1 - Real.log x) := by
  have hconj : MathlibExt.Probability.LegendreTransform.legendreTransform
      (extendedLogMGFVec oneVector (expMeasure 1)) (oneVector x) =
      ((x - 1 - Real.log x : ℝ) : EReal) := by
    apply le_antisymm
    · rw [MathlibExt.Probability.LegendreTransform.legendreTransform_eq_iSup]
      apply iSup_le
      intro v
      rw [eq_oneVector v, inner_oneVector]
      by_cases ht : v.ofLp 0 < 1
      · rw [exponential_log_of_lt_one ht, ← EReal.coe_sub]
        apply EReal.coe_le_coe_iff.mpr
        have hd : 0 < 1 - v.ofLp 0 := sub_pos.mpr ht
        have hprod : 0 < (1 - v.ofLp 0) * x := mul_pos hd hx
        have hlog := Real.log_le_sub_one_of_pos hprod
        rw [Real.log_mul (ne_of_gt hd) (ne_of_gt hx)] at hlog
        nlinarith
      · rw [exponential_log_of_one_le (le_of_not_gt ht), EReal.sub_top]
        exact bot_le
    · let t : ℝ := 1 - 1 / x
      have ht : t < 1 := by dsimp [t]; have := div_pos zero_lt_one hx; linarith
      have hvalue : ((x - 1 - Real.log x : ℝ) : EReal) =
          ((⟪oneVector t, oneVector x⟫_ℝ : ℝ) : EReal) -
            extendedLogMGFVec oneVector (expMeasure 1) (oneVector t) := by
        rw [inner_oneVector, exponential_log_of_lt_one ht, ← EReal.coe_sub]
        congr 1
        have hd : 1 - t = 1 / x := by dsimp [t]; ring
        rw [hd]
        simp only [one_div, Real.log_inv]
        dsimp [t]
        field_simp
      rw [hvalue]
      exact MathlibExt.Probability.LegendreTransform.le_legendreTransform
  unfold cramerRateFunction
  rw [hconj, EReal.real_coe_toENNReal]

/-- The old positive-x top defect is excluded by an explicit finite positive value. -/
theorem exponential_rate_two :
    cramerRateFunction oneVector (expMeasure 1) (oneVector 2) =
      ENNReal.ofReal (1 - Real.log 2) ∧
    cramerRateFunction oneVector (expMeasure 1) (oneVector 2) ≠ ⊤ ∧
    0 < cramerRateFunction oneVector (expMeasure 1) (oneVector 2) := by
  have h := exponential_rate_of_pos (x := 2) (by norm_num)
  norm_num at h
  refine ⟨h, ?_, ?_⟩
  · rw [h]
    exact ENNReal.ofReal_ne_top
  · rw [h]
    exact ENNReal.ofReal_pos.mpr target_rate_two_pos

/-- The zero direction is genuinely in the finite domain of this non-globally-finite law. -/
theorem exponential_origin_log :
    extendedLogMGFVec oneVector (expMeasure 1) (oneVector 0) = 0 := by
  rw [exponential_log_of_lt_one (t := 0) (by norm_num)]
  simp

/-- This non-globally-finite law composes with the canonical finite-direction log. -/
theorem exponential_finite_direction_bridge {t : ℝ} (ht : t < 1) :
    extendedLogMGFVec oneVector (expMeasure 1) (oneVector t) =
      ((MathlibExt.Probability.CramerUpperBound.logMGFVec oneVector (expMeasure 1)
        (oneVector t) : ℝ) : EReal) := by
  apply extendedLogMGFVec_eq_coe_logMGFVec
  simpa only [inner_oneVector] using integrable_exp_of_lt_one ht

/-- Actual scalar Chernoff at the finite direction one half uses M(1/2)=2. -/
theorem exponential_half_chernoff :
    (expMeasure 1).real {x : ℝ | 2 ≤ x} ≤ 2 * Real.exp (-1) := by
  have hi := integrable_exp_of_lt_one (t := (1 / 2 : ℝ)) (by norm_num)
  have hm : mgf (fun x : ℝ => x) (expMeasure 1) (1 / 2) = 2 := by
    rw [mgf, integral_exp_of_lt_one (by norm_num)]
    norm_num
  have h := measure_ge_le_exp_mul_mgf (μ := expMeasure 1) (X := fun x : ℝ => x)
    (t := (1 / 2 : ℝ)) 2 (by norm_num) hi
  norm_num [hm, mul_comm] at h ⊢
  exact h

/-- A constant-law endpoint still has zero rate at the constant and top away. -/
theorem constant_rate_endpoint :
    cramerRateFunction (fun _ : Unit => oneVector 1) (Measure.dirac ()) (oneVector 1) = 0 ∧
    cramerRateFunction (fun _ : Unit => oneVector 1) (Measure.dirac ()) (oneVector 2) = ⊤ := by
  refine ⟨(cramerRateFunction_const (μ := Measure.dirac ()) (oneVector 1)).1,
    (cramerRateFunction_const (μ := Measure.dirac ()) (oneVector 1)).2 _ ?_⟩
  intro h
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v.ofLp 0) h
  norm_num [oneVector] at hcoord

/-- Dimension zero retains its probability-space endpoint. -/
theorem dimension_zero_rate (X : Unit → EuclideanSpace ℝ (Fin 0)) :
    cramerRateFunction X (Measure.dirac ()) 0 = 0 := by
  have hX : X = fun _ => 0 := by funext u; exact Subsingleton.elim _ _
  rw [hX]
  exact (cramerRateFunction_const (μ := Measure.dirac ()) 0).1

/-- The rate is exposed through the existing LDP convex-rate interface. -/
theorem exponential_canonical_rate_structure :
    MathlibExt.Probability.LargeDeviationPrinciple.IsConvexRateFunction
      (cramerRateFunction oneVector (expMeasure 1)) :=
  isConvexRateFunction_cramerRateFunction oneVector (expMeasure 1)

end MathlibExtTest.Probability.CramerRateFunctionCanonicalTests
