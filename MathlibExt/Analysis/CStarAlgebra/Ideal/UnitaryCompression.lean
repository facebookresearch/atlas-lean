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

public import MathlibExt.Algebra.Star.UnitaryCompression
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient

/-!
# Essentially-unitary projection-corner compression

The class of p*u*p+1-p is unitary when the classes of p and u are respectively
a projection and a unitary, and those classes commute. The hypotheses are
literal ideal defects, not a supplied unitary output.
-/

@[expose] public section

noncomputable section

namespace ClosedStarIdeal

variable {D : Type*} [CStarAlgebra D]

/-- **Projection modulo a closed ideal.** Let `D` be a unital complex C*-algebra and `I ⊆ D` a closed
two-sided star ideal. If `p ∈ D` satisfies `p²-p ∈ I` and `p*-p ∈ I`, its class in `D/I` is a
self-adjoint idempotent. -/
theorem unitalQuotientMap_isStarProjection (I : ClosedStarIdeal D) (p : D)
    (hsquare : p * p - p ∈ I) (hstar : star p - p ∈ I) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    IsStarProjection (I.unitalQuotientMap p) := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  apply isStarProjection_iff'.2
  constructor
  · have h := (I.unitalQuotientMap_eq_zero_iff (p * p - p)).2 hsquare
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact h
  · have h := (I.unitalQuotientMap_eq_zero_iff (star p - p)).2 hstar
    rw [map_sub, map_star, sub_eq_zero] at h
    exact h

/-- **Unitary modulo a closed ideal.** Let `D` be a unital complex C*-algebra and `I ⊆ D` a closed
two-sided star ideal. If `u ∈ D` satisfies `u* u - 1 ∈ I` and `u u* - 1 ∈ I`, its class in `D/I` is
unitary. -/
theorem unitalQuotientMap_mem_unitary (I : ClosedStarIdeal D) (u : D)
    (hleft : star u * u - 1 ∈ I) (hright : u * star u - 1 ∈ I) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    I.unitalQuotientMap u ∈ unitary I.Quotient := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  apply Unitary.mem_iff.mpr
  constructor
  · have h := (I.unitalQuotientMap_eq_zero_iff (star u * u - 1)).2 hleft
    rw [map_sub, map_mul, map_star, map_one, sub_eq_zero] at h
    exact h
  · have h := (I.unitalQuotientMap_eq_zero_iff (u * star u - 1)).2 hright
    rw [map_sub, map_mul, map_star, map_one, sub_eq_zero] at h
    exact h

/-- **Unitary compression modulo an ideal.** Let `D` be a unital complex C*-algebra and `I ⊆ D` a closed
two-sided star ideal. If `p²-p`, `p*-p`, `u* u - 1`, `u u* - 1`, and `p u - u p` all belong to `I`,
the class of `p u p + 1 - p` in `D/I` is unitary. -/
theorem unitalQuotientMap_compression_mem_unitary (I : ClosedStarIdeal D)
    (p u : D) (hsquare : p * p - p ∈ I) (hstar : star p - p ∈ I)
    (hleft : star u * u - 1 ∈ I) (hright : u * star u - 1 ∈ I)
    (hcomm : p * u - u * p ∈ I) :
    let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
    I.unitalQuotientMap (p * u * p + 1 - p) ∈ unitary I.Quotient := by
  let _ : CStarAlgebra I.Quotient := I.unitalQuotientCStarAlgebra
  have hp := I.unitalQuotientMap_isStarProjection p hsquare hstar
  have hu := I.unitalQuotientMap_mem_unitary u hleft hright
  have hcomm' : Commute (I.unitalQuotientMap p) (I.unitalQuotientMap u) := by
    have h := (I.unitalQuotientMap_eq_zero_iff (p * u - u * p)).2 hcomm
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
    exact h
  rw [map_sub, map_add, map_mul, map_mul, map_one]
  exact hp.mul_mul_add_one_sub_mem_unitary hu hcomm'

end ClosedStarIdeal
