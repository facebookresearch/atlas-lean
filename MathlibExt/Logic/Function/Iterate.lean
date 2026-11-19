/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.Iterate

/-!
# Iterates that lower a depth by one

If a self-map `f` lowers a depth function `depth : α → ℕ` by exactly one at every point it
moves, then every point `y` reached from `x` by iterating `f` is reached after exactly
`depth x - depth y` steps (`Function.iterate_depth_sub_eq_of_iterate_eq`). For example, for the
parent map of a rooted forest, with roots as fixed points and the usual node depths, this is the
number of parent steps from a node to any of its ancestors.
-/

@[expose] public section

namespace Function

variable {α : Type*} {f : α → α} {depth : α → ℕ}

private theorem depth_iterate_le (hdepth : ∀ x, f x ≠ x → depth (f x) + 1 = depth x)
    (k : ℕ) (z : α) : depth (f^[k] z) ≤ depth z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have h1 : depth (f z) ≤ depth z := by
      by_cases h : f z = z
      · simp [h]
      · have hde := hdepth z h
        omega
    have heq : f^[k + 1] z = f^[k] (f z) := Function.iterate_add_apply f k 1 z
    rw [heq]
    exact Nat.le_trans (ih (f z)) h1

/-- If `depth` drops by exactly one along every step `x ↦ f x` with `f x ≠ x`, then a point `y`
reached from `x` by iterating `f` is reached after exactly `depth x - depth y` steps. -/
theorem iterate_depth_sub_eq_of_iterate_eq
    (hdepth : ∀ x, f x ≠ x → depth (f x) + 1 = depth x)
    {x y : α} {k : ℕ} (h : f^[k] x = y) :
    f^[depth x - depth y] x = y := by
  induction k generalizing x with
  | zero =>
    have hx : x = y := h
    subst hx
    simp
  | succ k ih =>
    have hstep : f^[k] (f x) = y := h
    by_cases hfx : f x = x
    · have hfix : f^[k] (f x) = x := by
        rw [hfx]
        exact Function.iterate_fixed hfx k
      rw [hfix] at hstep
      subst hstep
      simp
    · have hde := hdepth x hfx
      have hle : depth y ≤ depth (f x) := by
        rw [← hstep]
        exact depth_iterate_le hdepth k (f x)
      have hEq : depth x - depth y = (depth (f x) - depth y) + 1 := by
        omega
      rw [hEq]
      have hsplit : f^[(depth (f x) - depth y) + 1] x = f^[depth (f x) - depth y] (f x) :=
        Function.iterate_add_apply f (depth (f x) - depth y) 1 x
      rw [hsplit]
      exact ih hstep

end Function

end
