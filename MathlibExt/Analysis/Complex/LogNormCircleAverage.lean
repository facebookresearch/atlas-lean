/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AnalyticOnNhd_log_norm_le_circleAverage_log_norm.lean`
and
`P2M/Sol/S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.MeasureTheory.Integral.CircleAverage

import Mathlib.Analysis.Meromorphic.Divisor

@[expose] public section

open Real MeasureTheory Metric

/-- **Jensen's inequality for the logarithm of an analytic function.** Let $c \in \mathbb{C}$, let
$R$ be any real number, and let $F : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of
the closed disc $|z - c| \le |R|$, with $F(c) \ne 0$; $F$ may vanish elsewhere in the disc. Then
$$\log |F(c)| \le \frac{1}{2\pi} \int_0^{2\pi} \log |F(c + R e^{i\theta})| \, d\theta.$$
The two sides differ by the zero-counting term of Jensen's formula, a nonnegative sum over the
zeros of $F$ in the disc. -/
public theorem AnalyticOnNhd.log_norm_le_circleAverage_log_norm
    {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R := by
  rw [AnalyticOnNhd.circleAverage_log_norm hF hc]
  refine le_add_of_nonneg_left (finsum_nonneg fun u ↦ ?_)
  by_cases hu : u ∈ Metric.closedBall c |R|
  · refine mul_nonneg ?_ ?_
    · have h0 : (0 : ℤ) ≤ MeromorphicOn.divisor F (Metric.closedBall c |R|) u := by
        simpa using (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF) u
      exact_mod_cast h0
    · rcases eq_or_ne u c with rfl | huc
      · simp
      · have hpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc.symm)
        rw [← Real.log_abs, abs_mul, abs_inv, abs_norm]
        refine Real.log_nonneg ?_
        rw [le_mul_inv_iff₀ hpos, one_mul]
        simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_closedBall.mp hu)
  · have hdiv : (MeromorphicOn.divisor F (Metric.closedBall c |R|)) u = 0 :=
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
    simp [hdiv]
