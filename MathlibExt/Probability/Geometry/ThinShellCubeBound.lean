/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.UniformInterval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The cube lower bound for thin-shell variance

The one-dimensional isotropic cube gives a lower bound of `4 / 5` for the thin-shell
variance constant.
-/

namespace MathlibExt.Probability.ThinShell

open MeasureTheory
open scoped ENNReal

namespace fourFifths_le_thinShellVarianceConstant

private lemma integral_square_sub_one (a : ℝ) :
    (∫ x in -a..a, (x ^ 2 - 1) ^ 2) = 2 * (a ^ 5 / 5 - 2 * (a ^ 3 / 3) + a) := by
  have hpow (n : ℕ) : IntervalIntegrable (fun x : ℝ => x ^ n) volume (-a) a :=
    (continuous_id.pow n).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-a) a :=
    continuous_const.intervalIntegrable _ _
  have hmul := (hpow 2).const_mul (2 : ℝ)
  rw [show (fun x : ℝ => (x ^ 2 - 1) ^ 2) = fun x => x ^ 4 - 2 * x ^ 2 + 1 by
    funext x
    ring]
  rw [intervalIntegral.integral_add ((hpow 4).sub hmul) hconst,
    intervalIntegral.integral_sub (hpow 4) hmul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private lemma normalizedRadiusVariance_interval :
    normalizedRadiusVariance (uniformInterval (Real.sqrt 3)) = ENNReal.ofReal (4 / 5) := by
  let a : ℝ := Real.sqrt 3
  have ha : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have ha2 : a ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlen : 0 < a - -a := by linarith
  let f : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => (‖x‖ ^ 2 - 1) ^ 2
  have hcomp : f ∘ lineIsometry = fun x : ℝ => (x ^ 2 - 1) ^ 2 := by
    funext x
    simp [f, Real.norm_eq_abs, sq_abs]
  have hμ := lineIsometry_uniformInterval a
  have hf : Integrable f (uniformInterval a) := by
    apply (hμ.integrable_comp_emb lineIsometry.toHomeomorph.measurableEmbedding).mp
    rw [hcomp, ProbabilityTheory.cond]
    apply ((by fun_prop : Continuous (fun x : ℝ => (x ^ 2 - 1) ^ 2)).integrableOn_Icc).smul_measure
    rw [Real.volume_Icc]
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hlen))
  have hnonneg : 0 ≤ᵐ[uniformInterval a] f :=
    Filter.Eventually.of_forall fun x => sq_nonneg (‖x‖ ^ 2 - 1)
  have hint : (∫ x, f x ∂uniformInterval a) = 4 / 5 := by
    rw [← hμ.integral_comp lineIsometry.toHomeomorph.measurableEmbedding f]
    change (∫ x, (f ∘ lineIsometry) x ∂ProbabilityTheory.cond volume (Set.Icc (-a) a)) = _
    rw [hcomp, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hlen.le, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -a ≤ a), integral_square_sub_one]
    rw [smul_eq_mul, inv_mul_eq_div, div_eq_iff (ne_of_gt hlen)]
    linear_combination (2 / 5 * a ^ 3 - 2 / 15 * a) * ha2
  simpa only [normalizedRadiusVariance, Nat.cast_one, div_one, f] using
    (ofReal_integral_eq_lintegral_ofReal hf hnonneg).symm.trans (congrArg ENNReal.ofReal hint)

end fourFifths_le_thinShellVarianceConstant

/-- **Cube lower bound for the thin-shell variance constant.** The thin-shell variance constant,
an element of $[0, \infty]$, is at least $4/5$.

The value $4/5$ is the exact normalized radius variance of the uniform law on a cube scaled to
identity covariance.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem fourFifths_le_thinShellVarianceConstant :
    ENNReal.ofReal (4 / 5) ≤ thinShellVarianceConstant := by
  rw [← fourFifths_le_thinShellVarianceConstant.normalizedRadiusVariance_interval]
  exact uniformInterval_variance_le_thinShellConstant

end MathlibExt.Probability.ThinShell
