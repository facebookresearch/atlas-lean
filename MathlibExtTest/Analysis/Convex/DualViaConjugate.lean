/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.DualViaConjugate

namespace MathlibExt.Analysis.Convex.DualViaConjugate

open LagrangeDuality FenchelMoreau

-- Minimize `0` subject to `x ≤ 0` on `ℝ`: the dual function at `μ = 0` is `-f₀*(0) = 0`.
example : dualFunction Set.univ (fun _ : ℝ => (0 : ℝ))
    (fun (_ : Unit) x => ContinuousLinearMap.id ℝ ℝ x - 0) (fun _ => 0) = 0 := by
  rw [dualFunction_linear_eq_neg_sub_fenchelConj (fun _ : ℝ => (0 : ℝ))
    (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 0) (fun _ => 0)]
  simp [fenchelConj]

-- At `μ = 1` the same dual function is `-f₀*(-1) = -sup_x (-x) = -∞`.
example : dualFunction Set.univ (fun _ : ℝ => (0 : ℝ))
    (fun (_ : Unit) x => ContinuousLinearMap.id ℝ ℝ x - 0) (fun _ => 1) = ⊥ := by
  rw [dualFunction_linear_eq_neg_sub_fenchelConj (fun _ : ℝ => (0 : ℝ))
    (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 0) (fun _ => 1)]
  have htop : fenchelConj (fun _ : ℝ => ((0 : ℝ) : EReal))
      (-∑ _i : Unit, (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ) = ⊤ := by
    unfold fenchelConj
    refine iSup_eq_top.2 fun b hb => ?_
    induction b using EReal.rec with
    | bot => exact ⟨0, by simp⟩
    | top => exact absurd hb (lt_irrefl _)
    | coe r =>
      refine ⟨-(r + 1), ?_⟩
      have h : ((r : ℝ) : EReal) < ((r + 1 : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
      simpa using h
  rw [htop]
  simp

end MathlibExt.Analysis.Convex.DualViaConjugate
