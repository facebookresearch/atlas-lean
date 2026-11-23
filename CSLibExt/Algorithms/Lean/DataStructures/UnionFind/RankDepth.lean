/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.Iterate

/-!
# Rank grows along union-find parent chains

For a parent map `p : α → α` (roots are its fixed points) and a rank function `r : α → ℕ` in
which every nonroot has rank below its parent's, walking `k` parent steps from `x` through
nonroots raises the rank by at least `k` (`rank_iterate`), so a find path that reaches a root
after `k` steps has depth `k` at most the root's rank (`find_depth_le_rank`).

Nothing here uses finiteness or a particular node type. The canonical `Batteries.UnionFind`
satisfies the rank hypothesis with `p = u.parent : ℕ → ℕ` and `r = u.rank` by
`Batteries.UnionFind.rank_lt`. These are structural bounds on parent chains, not running-time
bounds.
-/

@[expose] public section

namespace Batteries.UnionFind

/-- Rank increases along find paths in a union-find forest:
`p` is the parent function on `α` (roots are fixed points),
`r` assigns ranks. If every non-root has rank below its parent's
rank, then walking `k` parent steps from `x` (through non-roots)
raises the rank by at least `k`. This is the invariant that
makes `find` logarithmic once ranks are `O(log n)`. -/
theorem rank_iterate {α : Type*} {p : α → α} {r : α → ℕ}
    (hrank : ∀ z : α, p z ≠ z → r z < r (p z))
    (x : α) (k : ℕ)
    (hsteps : ∀ i < k, p (p^[i] x) ≠ p^[i] x) :
    r x + k ≤ r (p^[k] x) := by
  induction k generalizing x with
  | zero =>
    simp [Function.iterate_zero_apply]
  | succ k ih =>
    have h0 : p x ≠ x := by
      have h := hsteps 0 (by omega)
      rwa [Function.iterate_zero_apply] at h
    have hlt : r x < r (p x) := hrank x h0
    have hsteps' : ∀ i < k, p (p^[i] (p x)) ≠ p^[i] (p x) := by
      intro i hi
      have h := hsteps (i + 1) (by omega)
      rw [Function.iterate_succ_apply] at h
      exact h
    have ih' := ih (p x) hsteps'
    have heq : p^[k] (p x) = p^[k + 1] x := (Function.iterate_succ_apply p k x).symm
    rw [heq] at ih'
    omega

/-- Find-depth bound: if `k` parent steps from `x` reach a root
(a fixed point of `p`), walking only through non-roots, then
`k ≤ r root`: the depth of `x` is at most the root's rank. -/
theorem find_depth_le_rank {α : Type*} {p : α → α} {r : α → ℕ}
    (hrank : ∀ z : α, p z ≠ z → r z < r (p z))
    (x : α) (k : ℕ)
    (hsteps : ∀ i < k, p (p^[i] x) ≠ p^[i] x)
    (hroot : p (p^[k] x) = p^[k] x) :
    k ≤ r (p^[k] x) := by
  have _ := hroot
  have h := rank_iterate hrank x k hsteps
  omega

end Batteries.UnionFind
