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

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Group.Commute.Defs

import Mathlib.Tactic.NoncommRing

/-!
# Unitary compression on a commuting projection corner

Compress a unitary to a commuting projection and act as the identity on its
complement. This algebraic construction is the strict data behind the
Fredholm-pair formula p*u*p+1-p; no C-star norm or compact ideal is required.
-/

@[expose] public section

namespace IsStarProjection

variable {D : Type*} [Ring D] [StarRing D] {p u : D}

/-- Let `D` be a unital star ring, `p` a star projection and `u` a unitary commuting with `p`. The
element `p*u + (1-p)`, acting by `u` on the projection corner and by the identity on its complement,
is unitary.
-/
theorem mul_add_one_sub_mem_unitary (hp : IsStarProjection p)
    (hu : u ∈ unitary D) (hcomm : Commute p u) :
    p * u + (1 - p) ∈ unitary D := by
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hps : Commute p (star u) := by
    change p * star u = star u * p
    have h := congrArg star hcomm.eq
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using h.symm
  have hstar : star (p * u + (1 - p)) = p * star u + (1 - p) := by
    rw [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      ← hps.eq]
  apply Unitary.mem_iff.mpr
  constructor
  · rw [hstar]
    have hcorner : (p * star u) * (p * u) = p := by
      rw [hps.symm.mul_mul_mul_comm p u, hpp,
        Unitary.star_mul_self_of_mem hu, mul_one]
    have hcross : (p * star u) * (1 - p) = 0 := by
      rw [mul_sub, mul_one, hps.symm.right_comm p, hpp, sub_self]
    have hcross' : (1 - p) * (p * u) = 0 := by
      rw [← mul_assoc, hp.one_sub_mul_self, zero_mul]
    rw [add_mul, mul_add, mul_add, hcorner, hcross, hcross',
      hp.one_sub.isIdempotentElem.eq]
    noncomm_ring
  · rw [hstar]
    have hcorner : (p * u) * (p * star u) = p := by
      rw [hcomm.symm.mul_mul_mul_comm p (star u), hpp,
        Unitary.mul_star_self_of_mem hu, mul_one]
    have hcross : (p * u) * (1 - p) = 0 := by
      rw [mul_sub, mul_one, hcomm.symm.right_comm p, hpp, sub_self]
    have hcross' : (1 - p) * (p * star u) = 0 := by
      rw [← mul_assoc, hp.one_sub_mul_self, zero_mul]
    rw [add_mul, mul_add, mul_add, hcorner, hcross, hcross',
      hp.one_sub.isIdempotentElem.eq]
    noncomm_ring

/-- Let `D` be a unital star ring, `p` a star projection and `u` a unitary commuting with `p`. The
two-sided compression formula `p*u*p + 1-p` is unitary.
-/
theorem mul_mul_add_one_sub_mem_unitary (hp : IsStarProjection p)
    (hu : u ∈ unitary D) (hcomm : Commute p u) :
    p * u * p + 1 - p ∈ unitary D := by
  have hcompression : p * u * p = p * u := by
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, hp.isIdempotentElem.eq]
  rw [hcompression, add_sub_assoc]
  exact hp.mul_add_one_sub_mem_unitary hu hcomm

end IsStarProjection
