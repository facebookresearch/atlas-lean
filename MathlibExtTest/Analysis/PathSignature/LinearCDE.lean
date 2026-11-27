/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.LinearCDE
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.LinearCDE

/-- Non-vacuity: for `X_t = t` in `ℝ¹` and `A = id`, the equation is `y' = y`, and the signature
series `∑_k (t − s)^k / k! · y₀` converges to `y₀ e^{t − s}`. -/
example (s y₀ t : ℝ) :
    Filter.Tendsto (fun n => signatureSeries (fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
      (fun _ _ => 1) s y₀ n t) Filter.atTop (nhds (y₀ * Real.exp (t - s))) := by
  refine tendsto_signatureSeries (fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
    (fun _ => continuous_const) (M := 1) (fun _ _ => by simp) s y₀
    (fun t => y₀ * Real.exp (t - s)) (by simp) (fun t => ?_) t
  have h := (((hasDerivAt_id t).sub_const s).exp).const_mul y₀
  simpa using h

/-- The first two truncations: `y^{(1)}_t = y₀ + S¹_{s,t} A y₀`. -/
example (A : Fin 1 → ℝ →L[ℝ] ℝ) (v : Fin 1 → ℝ → ℝ) (s y₀ t : ℝ) :
    signatureSeries A v s y₀ 1 t = y₀ + signature v s t [0] • A 0 y₀ := by
  simp [signatureSeries, Finset.sum_range_succ, wordOp]

end MathlibExtTest.Analysis.PathSignature.LinearCDE
