/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# One-step gradient descent distance identities

Let E be a real inner product space and x,g,c∈E,η∈ℝ. The update x−ηg has squared distance
‖x−c‖²−2η⟪g,x−c⟫+η²‖g‖² from c. If a projected update x⁺ is no farther from every comparator
in a set K, the same expression bounds ‖x⁺−c‖² for c∈K. Reference: Hazan, Theorem2.1 and
Equation3.2.
-/

@[expose] public section

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Squared-distance expansion for a gradient step.**

Let E be a real inner product space and x,g,c∈E,η∈ℝ. Then ‖x−ηg−c‖²=‖x−c‖²−2η⟪g,x−c⟫+η²‖g‖².
-/
theorem gradientDescentStep_sq_norm (x g c : E) (η : ℝ) :
    ‖x - η • g - c‖ ^ 2 = ‖x - c‖ ^ 2 - 2 * η * ⟪g, x - c⟫_ℝ + η ^ 2 * ‖g‖ ^ 2 := by
  have heq : x - η • g - c = (x - c) - η • g := by abel
  rw [heq, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [real_inner_comm g (x - c)]
  ring

/-- **Projected-step bound on a comparator set.**

Let E be a real inner product space, x,g,x⁺∈E,η∈ℝ,K⊆E and c∈K. If ‖x⁺−d‖≤‖x−ηg−d‖ for every
d∈K, then ‖x⁺−c‖²≤‖x−c‖²−2η⟪g,x−c⟫+η²‖g‖².
-/
theorem projectedGradientDescentStep_sq_norm_le (x g : E) (η : ℝ) (K : Set E)
    (xn c : E) (hc : c ∈ K)
    (hproj : ∀ d ∈ K, ‖xn - d‖ ≤ ‖x - η • g - d‖) :
    ‖xn - c‖ ^ 2 ≤ ‖x - c‖ ^ 2 - 2 * η * ⟪g, x - c⟫_ℝ + η ^ 2 * ‖g‖ ^ 2 := by
  have h0 : (0 : ℝ) ≤ ‖xn - c‖ := norm_nonneg _
  have hle : ‖xn - c‖ ^ 2 ≤ ‖x - η • g - c‖ ^ 2 :=
    pow_le_pow_left₀ h0 (hproj c hc) 2
  rw [gradientDescentStep_sq_norm] at hle
  exact hle
