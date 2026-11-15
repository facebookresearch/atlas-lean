/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Binary lifting

Binary lifting jumps `k` steps up a rooted forest by
iterating the parent function: `up x k = parent^[k] x`.
Lifts add, roots are fixed, and with a depth function the
lift by the depth difference reaches any ancestor. The LCA
meeting procedure is not included here.
-/

@[expose] public section

/-- Binary lifting on a rooted forest (core of ALG-15b):
`parent` maps roots to themselves; `up x k = parent^[k] x`. -/
def up (parent : ℕ → ℕ) (x k : ℕ) : ℕ := parent^[k] x

/-- Lifts add. -/
theorem up_add (parent : ℕ → ℕ) (x a b : ℕ) :
    up parent x (a + b) = up parent (up parent x a) b := by
  unfold up
  rw [Nat.add_comm a b]
  exact Function.iterate_add_apply parent b a x

/-- Lifting a root does nothing. -/
theorem up_root (parent : ℕ → ℕ) (x k : ℕ) (hx : parent x = x) :
    up parent x k = x := by
  unfold up
  exact Function.iterate_fixed hx k

private theorem depth_iterate_le {parent depth : ℕ → ℕ}
    (hdepth : ∀ x, parent x ≠ x → depth (parent x) + 1 = depth x)
    (k : ℕ) (z : ℕ) : depth (parent^[k] z) ≤ depth z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have h1 : depth (parent z) ≤ depth z := by
      by_cases h : parent z = z
      · rw [h]
      · have hde := hdepth z h
        omega
    have heq : parent^[k + 1] z = parent^[k] (parent z) :=
      Function.iterate_add_apply parent k 1 z
    rw [heq]
    exact Nat.le_trans (ih (parent z)) h1

/-- With a depth function that drops by exactly one along
non-root parent edges, lifting by `depth x - depth y` reaches
any ancestor `y` that is reached by iterating `parent`. -/
theorem up_eq_of_iterate {parent depth : ℕ → ℕ}
    (hdepth : ∀ x, parent x ≠ x → depth (parent x) + 1 = depth x)
    {x y : ℕ} {k : ℕ} (h : parent^[k] x = y) :
    up parent x (depth x - depth y) = y := by
  unfold up
  induction k generalizing x with
  | zero =>
    have hx : x = y := h
    subst hx
    simp
  | succ k ih =>
    have hstep : parent^[k] (parent x) = y := h
    by_cases hpx : parent x = x
    · have hfix : parent^[k] (parent x) = x := by
        rw [hpx]
        exact Function.iterate_fixed hpx k
      rw [hfix] at hstep
      subst hstep
      simp
    · have hde := hdepth x hpx
      have hle : depth y ≤ depth (parent x) := by
        rw [← hstep]
        exact depth_iterate_le hdepth k (parent x)
      have hEq : depth x - depth y = (depth (parent x) - depth y) + 1 := by
        omega
      have hIH := ih hstep
      rw [hEq]
      have hsplit : parent^[(depth (parent x) - depth y) + 1] x =
          parent^[depth (parent x) - depth y] (parent x) :=
        Function.iterate_add_apply parent (depth (parent x) - depth y) 1 x
      rw [hsplit]
      exact hIH

end
