/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import MathlibExt.Analysis.FunctionSpaces.LiebThirring

/-!
# Tests for the Lieb–Thirring kinetic energy inequality

A normalized smooth compactly supported function gives a one-member orthonormal family
to which the kinetic energy inequality applies.
-/

open MeasureTheory
open scoped ContDiff

namespace MathlibExtTest.Analysis.FunctionSpaces.LiebThirring

/-- A smooth compactly supported complex function on `ℝ³` with `∫ |u|² = 1` exists. -/
private theorem normalizedBump : ∃ u : EuclideanSpace ℝ (Fin 3) → ℂ,
    ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ ∫ x, star (u x) * u x = 1 := by
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

open MathlibExt.Analysis.FunctionSpaces.LiebThirringWanted

example : ∃ K : ℝ, 0 < K ∧ ∃ u : EuclideanSpace ℝ (Fin 3) → ℂ,
    ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ (∫ x, star (u x) * u x) = 1 ∧
    K * (∫ x, (‖u x‖ ^ 2) ^ (5 / 3 : ℝ)) ≤
      ∫ x, ∑ k, ‖fderiv ℝ u x (EuclideanSpace.single k 1)‖ ^ 2 := by
  obtain ⟨K, hK, h⟩ := lieb_thirring_kinetic 3 (by decide)
  obtain ⟨u, hu, huc, huo⟩ := normalizedBump
  refine ⟨K, hK, u, hu, huc, huo, ?_⟩
  have hortho : ∀ i j : Fin 1, ∫ x, star (u x) * u x = if i = j then 1 else 0 := by
    intro i j
    simpa only [ite_eq_left (Subsingleton.elim i j)] using huo
  simpa only [Fin.sum_univ_one, Nat.cast_ofNat, show (1 + 2 / 3 : ℝ) = 5 / 3 by norm_num] using
    h 1 (fun _ => u) (fun _ => hu) (fun _ => huc) hortho

end MathlibExtTest.Analysis.FunctionSpaces.LiebThirring
