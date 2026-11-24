/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Non-vacuity of the hypotheses of the wanted Lieb–Thirring inequality

`WantedExt.Analysis.FunctionSpaces.LiebThirringWanted.lieb_thirring_kinetic` quantifies over
families of smooth compactly supported functions on `ℝ^d` that are orthonormal in `L²`. This test
exhibits such a family with `N = 1` in dimension `3`: a bump function rescaled to unit `L²` norm.
So the hypotheses are jointly satisfiable and the wanted statement is not vacuous.
-/

open MeasureTheory
open scoped ContDiff

namespace MathlibExtTest.Analysis.FunctionSpaces.LiebThirringHypotheses

/-- A smooth compactly supported complex function on `ℝ³` with `∫ |u|² = 1` exists. -/
example : ∃ u : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
    ∫ x, star (u x) * u x = 1 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨1, 2, one_pos, one_lt_two⟩
  set c : ℝ := ∫ x, b x ^ 2 with hc
  have hcs : HasCompactSupport (fun x => b x ^ 2) := by
    have h := b.hasCompactSupport.mul_left (f := fun x => b x)
    simpa only [sq, Pi.mul_def] using h
  have hint : Integrable (fun x => b x ^ 2) :=
    (b.continuous.pow 2).integrable_of_hasCompactSupport hcs
  have hcpos : 0 < c := by
    rw [hc, integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
    have : Function.support (fun x => b x ^ 2) = Function.support b := by
      ext x; simp
    rw [this, b.support_eq]
    exact Metric.measure_ball_pos _ _ b.rOut_pos
  refine ⟨fun x => ((Real.sqrt c)⁻¹ * b x : ℝ), ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul b.contDiff)
  · exact (b.hasCompactSupport.mul_left).comp_left Complex.ofReal_zero
  · have h : ∀ x, star (((Real.sqrt c)⁻¹ * b x : ℝ) : ℂ) * (((Real.sqrt c)⁻¹ * b x : ℝ) : ℂ) =
        ((c⁻¹ * b x ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      rw [mul_mul_mul_comm, ← mul_inv, Real.mul_self_sqrt hcpos.le, sq]
    simp_rw [h]
    rw [integral_complex_ofReal, integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne',
      Complex.ofReal_one]

end MathlibExtTest.Analysis.FunctionSpaces.LiebThirringHypotheses
