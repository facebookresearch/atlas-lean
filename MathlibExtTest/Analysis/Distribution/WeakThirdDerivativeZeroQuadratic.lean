/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.WeakThirdDerivativeZeroQuadratic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open scoped ContDiff Interval Topology
open MathlibExt.Analysis.Distribution.WeakThirdDerivativeZeroQuadraticWanted
  (ae_eq_quadratic_of_integral_mul_iteratedDeriv_three_eq_zero)

private noncomputable def endpointValue (x : ℝ) : ℝ := if x = 0 then 2 else 1

/-- Changing an endpoint value does not affect the hypothesis or the a.e. conclusion. -/
example : endpointValue 0 ≠ 1 ∧
    ∃ a b c : ℝ, ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      endpointValue x = a + b * x + c * x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hne : ∀ᵐ x ∂μ, x ≠ (0 : ℝ) := by
    rw [ae_iff]
    simp
  have hae : endpointValue =ᵐ[μ] (fun _ => 1) := hne.mono fun x hx => by simp [endpointValue, hx]
  have hLp : MemLp endpointValue 1 μ := (memLp_congr_ae hae).mpr (memLp_const 1)
  refine ⟨by norm_num [endpointValue], ?_⟩
  apply ae_eq_quadratic_of_integral_mul_iteratedDeriv_three_eq_zero endpointValue hLp
  intro g hg ⟨a, b, hs, hu⟩
  have hg₁ := (contDiff_infty_iff_deriv.mp hg).2
  have hg₂ := (contDiff_infty_iff_deriv.mp hg₁).2
  have hg₃ := (contDiff_infty_iff_deriv.mp hg₂).2
  have he (z : ℝ) (hz : z ∉ Icc a b) : deriv (deriv g) z = 0 := by
    have hnear : g =ᶠ[𝓝 z] (0 : ℝ → ℝ) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hz] with x hx
      change g x = 0
      by_contra h
      exact hx (hs (Function.mem_support.mpr h))
    simpa only [deriv_zero, Pi.zero_apply] using hnear.deriv.deriv_eq
  have h0 := he 0 (fun h => (hu h).1.false)
  have h1 := he 1 (fun h => (hu h).2.false)
  calc
    _ = ∫ x, deriv (deriv (deriv g)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [show endpointValue x = 1 from hx, one_mul]
    _ = ∫ x in (0 : ℝ)..1, deriv (deriv (deriv g)) x := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      change _ = ∫ x, deriv (deriv (deriv g)) x ∂(volume.restrict (Ioc (0 : ℝ) 1))
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    _ = deriv (deriv g) 1 - deriv (deriv g) 0 :=
      intervalIntegral.integral_deriv_eq_sub (fun _ _ =>
        ((contDiff_infty_iff_deriv.mp hg₂).1 _)) (hg₃.continuous.intervalIntegrable 0 1)
    _ = 0 := by rw [h0, h1, sub_self]
