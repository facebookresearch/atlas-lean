/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic

/-!
# Leftover hash lemma: collision core

For a probability mass function `p`, the collision probability
`sum_x p(x)^2` is at most the largest mass. This module proves
that counting core of the leftover hash lemma; the averaging
over a universal hash family built on it is not formalized
here.
-/

@[expose] public section

/-- Collision probability core of the leftover hash lemma
(QCI-29): for a probability mass function `p` bounded by `M`,
the collision probability `sum_x p(x)^2` is at most `M`, since
`p(x)^2 <= M * p(x)` termwise and the masses sum to 1. The
hash-family averaging on top of this is downstream. -/
theorem collision_le_of_le {X : Type*} [Fintype X] (p : X → ℝ)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) (M : ℝ)
    (hM : ∀ x, p x ≤ M) : ∑ x, p x ^ 2 ≤ M := by
  calc ∑ x, p x ^ 2 = ∑ x, p x * p x := by simp [pow_two]
    _ ≤ ∑ x, M * p x := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hM x) (h0 x)
    _ = M := by rw [← Finset.mul_sum, h1, mul_one]

/-- With `M` the largest mass (witnessed at `x0`): collision
probability is at most the max probability, i.e. `2 ^ (-H∞)`. -/
theorem collision_le_max' {X : Type*} [Fintype X]
    (p : X → ℝ) (h0 : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) (x0 : X) :
    ∑ x, p x ^ 2 ≤ (Finset.univ.image p).max'
      ⟨p x0, Finset.mem_image.mpr ⟨x0, Finset.mem_univ x0, rfl⟩⟩ := by
  apply collision_le_of_le p h0 h1 _
  intro x
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

end
