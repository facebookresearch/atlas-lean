/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The second derivative of the squared norm

In a real inner product space, `D²(‖·‖²)(p)(u, v) = 2 ⟪u, v⟫` at every point `p`.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Second derivative of the squared norm.** Let $E$ be a real inner product space.
For all $p, u, v \in E$, the second Fréchet derivative of $x \mapsto \|x\|^2$ at $p$,
applied to $u$ and then to $v$, equals $2 \langle u, v \rangle$. -/
theorem fderiv_fderiv_norm_sq_apply (p u v : E) :
    fderiv ℝ (fderiv ℝ (fun x : E ↦ ‖x‖ ^ 2)) p u v = 2 * inner ℝ u v := by
  have hL : fderiv ℝ (fun x : E ↦ ‖x‖ ^ 2) =
      ⇑((2 : ℝ) • (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ)) := by
    rw [fderiv_norm_sq]; ext; simp
  rw [hL, ContinuousLinearMap.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rfl
