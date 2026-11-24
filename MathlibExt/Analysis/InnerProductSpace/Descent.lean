/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# One-step gradient descent identities

For a real inner product space, the squared distance after one gradient-descent
step expands into a cross term plus a squared gradient term. A projected step
whose projection inequality holds for every comparator in a feasible set `K`
(Hazan Thm 2.1 / Eq 3.2 shape) satisfies the same expansion as an upper bound
against comparators in `K`.
-/

@[expose] public section

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One-step gradient-descent identity: the squared distance of the update
`x - η • g` to a comparator `c` expands exactly. -/
theorem gradientDescentStep_sq_norm (x g c : E) (η : ℝ) :
    ‖x - η • g - c‖ ^ 2 = ‖x - c‖ ^ 2 - 2 * η * ⟪g, x - c⟫_ℝ + η ^ 2 * ‖g‖ ^ 2 := by
  have heq : x - η • g - c = (x - c) - η • g := by abel
  rw [heq, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [real_inner_comm g (x - c)]
  ring

/-- Projected one-step bound, set-scoped: if `c ∈ K` and `xn` is no farther
than the unprojected update `x - η • g` from every point of `K`, then its
squared distance to `c` is bounded by the one-step expansion.

The comparator set cannot be dropped: an ambient `∀ d` hypothesis would force
`xn = x - η • g` (take `d := x - η • g`), collapsing the projection to the
identity. -/
theorem projectedGradientDescentStep_sq_norm_le (x g : E) (η : ℝ) (K : Set E)
    (xn c : E) (hc : c ∈ K)
    (hproj : ∀ d ∈ K, ‖xn - d‖ ≤ ‖x - η • g - d‖) :
    ‖xn - c‖ ^ 2 ≤ ‖x - c‖ ^ 2 - 2 * η * ⟪g, x - c⟫_ℝ + η ^ 2 * ‖g‖ ^ 2 := by
  have h0 : (0 : ℝ) ≤ ‖xn - c‖ := norm_nonneg _
  have hle : ‖xn - c‖ ^ 2 ≤ ‖x - η • g - c‖ ^ 2 :=
    pow_le_pow_left₀ h0 (hproj c hc) 2
  rw [gradientDescentStep_sq_norm] at hle
  exact hle
