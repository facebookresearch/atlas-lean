/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Leftover hash lemma: collision probability of the source

For a probability mass function `p` on a finite type, the collision probability
`∑ x, p x ^ 2` is at most any upper bound on the masses, and in particular at most the
largest mass. Bounding every mass by `2 ^ (-k)`, as for a source of min-entropy at
least `k`, bounds its collision probability by `2 ^ (-k)`; this is the estimate on the
source in the proof of the leftover hash lemma. The leftover hash lemma itself, which
averages over a universal hash family, is not formalized here.
-/

@[expose] public section

namespace InformationTheory

/-- Collision probability bound used by the leftover hash lemma (QCI-29): for a
probability mass function `p` bounded by `M`, the collision probability `∑ x, p x ^ 2`
is at most `M`, since `p x ^ 2 ≤ M * p x` termwise and the masses sum to `1`. -/
theorem collision_le_of_le {X : Type*} [Fintype X] (p : X → ℝ)
    (h0 : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) (M : ℝ)
    (hM : ∀ x, p x ≤ M) : ∑ x, p x ^ 2 ≤ M := by
  calc ∑ x, p x ^ 2 = ∑ x, p x * p x := by simp [pow_two]
    _ ≤ ∑ x, M * p x := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hM x) (h0 x)
    _ = M := by rw [← Finset.mul_sum, h1, mul_one]

/-- The collision probability is at most the largest mass, the maximum of the image of
`p`. The point `x0` only shows that this image is nonempty; it need not attain the
maximum. -/
theorem collision_le_max' {X : Type*} [Fintype X]
    (p : X → ℝ) (h0 : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) (x0 : X) :
    ∑ x, p x ^ 2 ≤ (Finset.univ.image p).max'
      ⟨p x0, Finset.mem_image.mpr ⟨x0, Finset.mem_univ x0, rfl⟩⟩ := by
  apply collision_le_of_le p h0 h1 _
  intro x
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

end InformationTheory

end
