/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KKT

/-- Boundary check: with no constraints, KKT sufficiency says a
stationary point of a convex differentiable objective is a
minimizer. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ}
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hf_diff : ∀ x : E, DifferentiableAt ℝ f x)
    (x : E) (hstat : fderiv ℝ f x = 0) (y : E) :
    f x ≤ f y :=
  kkt_sufficient (m := 0) (g := fun _ _ => (0 : ℝ)) (lam := fun _ => (0 : ℝ))
    hf_conv (fun i => i.elim0) (hf_diff x) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (by simpa using hstat) y (fun i => i.elim0)
