/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Comparing ideal and two-sided-ideal quotients

An ideal in a noncommutative ring gives an ordinary ideal quotient once it is
known to be two-sided.  It can also be bundled as a `TwoSidedIdeal`, whose
quotient is presented using its ring congruence.  This file gives the canonical
ring equivalence between those two presentations and records its action on
quotient classes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace Ideal

variable {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false in
private theorem toTwoSided_ringCon_eq_quotientRingCon
    (I : Ideal R) [I.IsTwoSided] :
    I.toTwoSided.ringCon = Ideal.Quotient.ringCon I := by
  ext x y
  rw [TwoSidedIdeal.rel_iff]
  change (x - y ∈ I.toTwoSided) ↔ _
  rw [Ideal.mem_toTwoSided]
  change (x - y ∈ I) ↔ I.quotientRel x y
  exact I.quotientRel_def.symm

/-- The ring-congruence quotient by the two-sided ideal associated to `I` is
canonically equivalent to the ordinary ideal quotient by `I`. -/
noncomputable def toTwoSidedQuotientEquiv
    (I : Ideal R) [I.IsTwoSided] :
    I.toTwoSided.ringCon.Quotient ≃+* R ⧸ I :=
  RingCon.congr
    (c := I.toTwoSided.ringCon)
    (d := Ideal.Quotient.ringCon I)
    (RingEquiv.refl _) (by
      rw [toTwoSided_ringCon_eq_quotientRingCon]
      rfl)

/-- `toTwoSidedQuotientEquiv` sends a ring-congruence quotient class to the
ordinary ideal quotient class of the same representative. -/
@[simp]
theorem toTwoSidedQuotientEquiv_mk
    (I : Ideal R) [I.IsTwoSided] (r : R) :
    toTwoSidedQuotientEquiv I (↑r) =
      Ideal.Quotient.mk I r := by
  exact RingCon.congr_mk (RingEquiv.refl _) _ r

end Ideal
