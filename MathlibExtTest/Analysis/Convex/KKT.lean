/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KKT

/-- Boundary check: with no constraints, KKT sufficiency says a
stationary point of a convex objective is a minimizer. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {gradf : E → E}
    (hf : ∀ x y, f x + @inner ℝ E _ (gradf x) (y - x) ≤ f y)
    (x : E) (hstat : gradf x = 0) (y : E) :
    f x ≤ f y :=
  kkt_sufficient (ι := Fin 0) (g := fun _ _ => (0 : ℝ))
    (gradg := fun _ _ => (0 : E)) hf (fun i => i.elim0) x (fun _ => 0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (by simpa using hstat) y (fun i => i.elim0)
