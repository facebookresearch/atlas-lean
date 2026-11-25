/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PathSignature.UniversalApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set MathlibExt.Analysis.PathSignature
open MathlibExt.Analysis.PathSignature.UniversalApproximationWanted

namespace MathlibExtTest.Analysis.PathSignature.UniversalApproximation

noncomputable section

private abbrev μ := volume.restrict (Icc (0 : ℝ) 1)
private abbrev V := Lp (Fin 2 → ℝ) 1 μ

private def step (t : ℝ) : Fin 2 → ℝ :=
  (Iic (1 / 2 : ℝ)).piecewise (fun _ => ![0, 1]) (fun _ => ![0, -1]) t

private theorem step_mem : MemLp step 1 μ :=
  MemLp.piecewise measurableSet_Iic.nullMeasurableSet (memLp_const _) (memLp_const _)

private def time : V := Lp.const 1 μ ![1, 0]

private def velocity (r : ℝ) : V := time + r • step_mem.toLp step

-- The spatial velocity switches from r to -r at the midpoint. All paths have the same
-- displacement, while their squared L¹ distances to the pure time path vary with r.
example {ε : ℝ} (hε : 0 < ε) :
    ∃ L : List (ℝ × List (Fin 2)), ∀ r ∈ Icc (-1 : ℝ) 1,
      |‖velocity r - time‖ ^ 2 -
        (L.map fun p => p.1 * signature (fun i u => velocity r u i) 0 1 p.2).sum| < ε := by
  have hc : Continuous velocity := continuous_const.add (continuous_id.smul continuous_const)
  let K := velocity '' Icc (-1 : ℝ) 1
  have ht : ∀ f ∈ K, ∀ᵐ u ∂μ, f u 0 = 1 := by
    rintro _ ⟨r, _, rfl⟩
    filter_upwards [Lp.coeFn_add time (r • step_mem.toLp step),
      Lp.coeFn_smul r (step_mem.toLp step), step_mem.coeFn_toLp,
      Lp.coeFn_const (p := 1) (μ := μ) (![1, 0] : Fin 2 → ℝ)] with u hadd hsmul hs htime
    change (time + r • step_mem.toLp step) u 0 = 1
    change time u = _ at htime
    rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hs, htime]
    simp only [step, Set.piecewise]
    split <;> simp
  obtain ⟨L, hL⟩ := exists_signature_linear_approx (d := 1) zero_lt_one K
    (isCompact_Icc.image hc) ht (fun f => ‖f - time‖ ^ 2)
    (((continuous_id.sub continuous_const).norm.pow 2).continuousOn) hε
  exact ⟨L, fun r hr => hL (velocity r) ⟨r, hr, rfl⟩⟩

end

end MathlibExtTest.Analysis.PathSignature.UniversalApproximation
