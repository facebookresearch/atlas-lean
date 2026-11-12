/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Function.Iterate

@[expose] public section


/-- Rank increases along find paths in a union-find forest:
`p` is the parent function on `Fin n` (roots are fixed points),
`r` assigns ranks. If every non-root has rank below its parent's
rank, then walking `k` parent steps from `x` (through non-roots)
raises the rank by at least `k`. This is the invariant that
makes `find` logarithmic once ranks are `O(log n)`. -/
theorem rank_iterate {n : ℕ} {p : Fin n → Fin n} {r : Fin n → ℕ}
    (hrank : ∀ z : Fin n, p z ≠ z → r z < r (p z))
    (x : Fin n) (k : ℕ)
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
theorem find_depth_le_rank {n : ℕ} {p : Fin n → Fin n} {r : Fin n → ℕ}
    (hrank : ∀ z : Fin n, p z ≠ z → r z < r (p z))
    (x : Fin n) (k : ℕ)
    (hsteps : ∀ i < k, p (p^[i] x) ≠ p^[i] x)
    (hroot : p (p^[k] x) = p^[k] x) :
    k ≤ r (p^[k] x) := by
  have _ := hroot
  have h := rank_iterate hrank x k hsteps
  omega
