/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.KLS
import MathlibExt.Probability.Geometry.UniformInterval
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A lower bound for the KLS constant

Cutting the isotropic uniform interval at its midpoint gives a lower bound of
$\sqrt{3}$ for the KLS constant, which implies the Gaussian bound $\sqrt{\pi/2}$.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MathlibExt.Probability.ThinShell

namespace MathlibExt.Probability.KLS

-- The ball of radius a about −a cuts the support at zero. Increasing its radius
-- by ε adds exactly the interval (0, ε] until the right endpoint reaches a.
private theorem uniformInterval_ball_mass {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε) (hεa : ε ≤ a) :
    uniformInterval a (closedBall (lineIsometry (-a)) (ε + a)) =
      ENNReal.ofReal ((a + ε) / (2 * a)) := by
  rw [← (lineIsometry_uniformInterval a).measure_preimage isClosed_closedBall.nullMeasurableSet,
    lineIsometry.isometry.preimage_closedBall, Real.closedBall_eq_Icc,
    ProbabilityTheory.cond_apply measurableSet_Icc, Icc_inter_Icc, Real.volume_Icc, Real.volume_Icc]
  rw [sup_eq_left.mpr (by linarith), inf_eq_right.mpr (by linarith),
    ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith))]
  congr 1
  ring

private theorem uniformInterval_le_inverseCheeger {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a ≤ inverseCheegerConstant (uniformInterval a) := by
  let A := closedBall (lineIsometry (-a)) a
  have hmass : uniformInterval a A = ENNReal.ofReal (1 / 2) := by
    simpa only [A, zero_add, add_zero, show a / (2 * a) = 1 / 2 by field_simp] using
      uniformInterval_ball_mass ha le_rfl ha.le
  have hboundary : outerMinkowskiBoundary (uniformInterval a) A =
      ENNReal.ofReal (1 / (2 * a)) := by
    apply Tendsto.liminf_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ha)]
      with ε hε hεa
    have hpos : 0 < ε := hε
    rw [hmass, cthickening_closedBall hpos.le ha.le, uniformInterval_ball_mass ha hpos.le hεa.le,
      ← ENNReal.ofReal_sub _ (by norm_num), ← ENNReal.ofReal_div_of_pos hpos]
    congr 1
    field_simp
    ring
  have hratio : outerMinkowskiBoundary (uniformInterval a) A /
      min (uniformInterval a A) (1 - uniformInterval a A) = (ENNReal.ofReal a)⁻¹ := by
    rw [hboundary, hmass, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, min_self]
    rw [← ENNReal.ofReal_div_of_pos (by norm_num), ← ENNReal.ofReal_inv_of_pos ha]
    congr 1
    ring
  apply ENNReal.inv_le_inv.mp
  rw [inverseCheegerConstant, inv_inv]
  exact sInf_le ⟨A, isClosed_closedBall.measurableSet, by rw [hmass]; positivity,
    by rw [hmass]; norm_num, hratio⟩

/-- **A lower bound for the KLS constant.** The KLS constant is at least $\sqrt{\pi/2}$.

The bound comes from the standard Gaussian measure in any dimension $n \ge 1$, whose inverse Cheeger
constant is $\sqrt{\pi/2}$.

Source: optimizationproblems `constants/20c.md`, classical Gaussian lower-bound row. -/
public theorem sqrtPiDivTwo_le_klsConstant :
    ENNReal.ofReal (Real.sqrt (Real.pi / 2)) ≤ klsConstant := by
  calc
    ENNReal.ofReal (Real.sqrt (Real.pi / 2)) ≤ ENNReal.ofReal (Real.sqrt 3) :=
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four]))
    _ ≤ inverseCheegerConstant (uniformInterval (Real.sqrt 3)) :=
      uniformInterval_le_inverseCheeger (by positivity)
    _ ≤ klsConstant :=
      inverseCheegerConstant_le_constant (by decide)
        uniformInterval_sqrt_three_isIsotropicLogConcave

end MathlibExt.Probability.KLS
