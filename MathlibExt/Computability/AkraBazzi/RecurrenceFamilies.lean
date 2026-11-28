/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.AkraBazzi.MasterTheorem

/-!
# Akra-Bazzi recurrence families and the constant shift

A constant shift of the solution of an Akra-Bazzi recurrence is again an
Akra-Bazzi recurrence, with the toll shifted by the same constant times
`1 - ∑ i, a i`. This lets a recurrence with a nonzero finite base be
normalized before the master theorem is applied.

## Cost model

The charged primitive is one recursive call, charged `a i` times per
branch, plus the declared per-call toll `g`. Rounding is free. No
machine-time claim is made.

## References

* Tom Leighton, Notes on better master theorems for divide-and-conquer
  recurrences, 1996.
-/

public section

open Filter Asymptotics Finset Real
open scoped Topology

namespace AkraBazziRecurrence

variable {α : Type*} [Fintype α] [Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}

/-- **Constant shift of a recurrence.** Adding `c` to `T` and `c * (1 - ∑ i, a i)`
to `g` preserves the recurrence relation. -/
noncomputable def shift (R : AkraBazziRecurrence T g a b r) (c : ℝ)
    (hT : ∀ n < R.n₀, 0 < T n + c) (hg : ∀ x ≥ 0, 0 ≤ g x + c * (1 - ∑ i, a i))
    (hgpoly : AkraBazziRecurrence.GrowsPolynomially
      (fun x => g x + c * (1 - ∑ i, a i))) :
    AkraBazziRecurrence (fun n => T n + c) (fun x => g x + c * (1 - ∑ i, a i))
      a b r where
  n₀ := R.n₀
  n₀_gt_zero := R.n₀_gt_zero
  a_pos := R.a_pos
  b_pos := R.b_pos
  b_lt_one := R.b_lt_one
  g_nonneg x hx := hg x hx
  g_grows_poly := hgpoly
  h_rec n hn := by
    rw [R.h_rec n hn]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  T_gt_zero' n hn := hT n hn
  r_lt_n := R.r_lt_n
  dist_r_b := R.dist_r_b

end AkraBazziRecurrence
