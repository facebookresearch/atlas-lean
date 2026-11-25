/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.FirstOrderCondition
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Convex.Mul

namespace MathlibExt.Analysis.Convex.FirstOrderCondition

-- The square function lies above its tangent lines: `a² + 2a (x - a) ≤ x²`.
example (a x : ℝ) : a ^ 2 + 2 * a * (x - a) ≤ x ^ 2 := by
  have hconv : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) :=
    (show Even 2 by norm_num).convexOn_pow
  have hd : HasFDerivAt (fun y : ℝ => y ^ 2)
      ((2 * a) • ContinuousLinearMap.id ℝ ℝ) a := by
    simpa [pow_one] using (hasFDerivAt_id (𝕜 := ℝ) a).pow 2
  have := add_fderiv_le_of_convexOn hconv (Set.mem_univ a) (Set.mem_univ x) hd
  simpa [smul_eq_mul, mul_assoc] using this

-- The converse direction: tangent lines `y ↦ a² + 2a (y - a)` certify convexity of `y ↦ y²`.
example : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) := by
  refine convexOn_of_forall_add_le convex_univ
    (fun a => (2 * a) • ContinuousLinearMap.id ℝ ℝ) fun a _ x _ => ?_
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]
  nlinarith [sq_nonneg (x - a)]

-- A stationary point of a convex function is a global minimizer: `0` minimizes `y ↦ y²`.
example : IsMinOn (fun y : ℝ => y ^ 2) Set.univ 0 := by
  have hconv : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) :=
    (show Even 2 by norm_num).convexOn_pow
  have hd : HasFDerivAt (fun y : ℝ => y ^ 2) (0 : ℝ →L[ℝ] ℝ) 0 := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).pow 2
  exact isMinOn_of_hasFDerivAt_eq_zero hconv (Set.mem_univ _) hd

-- The optimality criterion on a constraint set: `1` minimizes `id` over `[1, ∞)`, and the
-- criterion detects that `1` does not minimize `-id` there.
example : IsMinOn (id : ℝ → ℝ) (Set.Ici 1) 1 := by
  rw [isMinOn_iff_forall_fderiv_nonneg (f' := ContinuousLinearMap.id ℝ ℝ)
    (convexOn_id (convex_Ici 1)) (Set.mem_Ici.2 le_rfl) (hasFDerivAt_id 1)]
  intro x hx
  simpa using hx

example : ¬ IsMinOn (-id : ℝ → ℝ) (Set.Ici 1) 1 := by
  rw [isMinOn_iff_forall_fderiv_nonneg (f' := -ContinuousLinearMap.id ℝ ℝ)
    (concaveOn_id (convex_Ici 1)).neg (Set.mem_Ici.2 le_rfl) (hasFDerivAt_id 1).neg]
  intro h
  have := h 2 (by norm_num)
  norm_num at this

end MathlibExt.Analysis.Convex.FirstOrderCondition
