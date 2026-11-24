/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite sums of orthogonal star projections

A finite family of star projections with pairwise zero products has a
star-projection sum. This constructs the actual finite projection cutoffs
used with finite localizations; no projection-sum certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace IsStarProjection

universe u v

variable {R : Type u} [NonUnitalSemiring R] [StarRing R] {I : Type v}

/-- A literal finite sum of pairwise orthogonal star projections is a star projection. -/
theorem finset_sum_of_pairwise_mul_eq_zero (s : Finset I) (p : I → R)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horthogonal : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using IsStarProjection.zero R
  | @insert a s ha ih =>
      have hrest : IsStarProjection (∑ i ∈ s, p i) := ih
        (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => horthogonal i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij)
      have hsum : (∑ i ∈ s, p i) * p a = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        exact horthogonal i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
          (fun h => ha (h ▸ hi))
      rw [Finset.sum_insert ha]
      simpa only [add_comm] using hrest.add (hp a (Finset.mem_insert_self a s)) hsum

end IsStarProjection
