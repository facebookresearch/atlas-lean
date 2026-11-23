/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KKT

open MathlibExt.Analysis.Convex.KarushKuhnTucker

/-- With primal feasibility of `x`, the KKT conditions make `x` a
minimizer of `f` over the feasible set: `x` is feasible and no feasible
point has a smaller objective value. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {x : E} {lam : Fin m → ℝ}
    (hf_conv : ConvexOn ℝ Set.univ f) (hg_conv : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf_diff : DifferentiableAt ℝ f x) (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hx : ∀ i, g i x ≤ 0) (hlam : ∀ i, 0 ≤ lam i) (hcs : ∀ i, lam i * g i x = 0)
    (hstat : fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x = 0) :
    x ∈ {y | ∀ i, g i y ≤ 0} ∧ IsMinOn f {y | ∀ i, g i y ≤ 0} x :=
  ⟨hx, isMinOn_of_karush_kuhn_tucker_convex hf_conv hg_conv hf_diff hg_diff
    hlam hcs hstat⟩

/-- Boundary check: with no constraints, every point is feasible and a
stationary point of a convex differentiable objective is a global
minimizer. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    (x : E) (hf_diff : DifferentiableAt ℝ f x) (hstat : fderiv ℝ f x = 0) (y : E) :
    f x ≤ f y :=
  isMinOn_of_karush_kuhn_tucker_convex (m := 0) (g := fun _ _ => (0 : ℝ))
    (lam := fun _ => (0 : ℝ)) hf_conv (fun i => i.elim0) hf_diff (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (by simpa using hstat)
    (show ∀ i : Fin 0, (fun _ _ => (0 : ℝ)) i y ≤ 0 from fun i => i.elim0)
