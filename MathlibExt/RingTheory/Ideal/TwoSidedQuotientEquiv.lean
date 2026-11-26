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
# Quotient presentations for a two-sided ideal

For an associative ring `R` and an ideal `I` satisfying `I.IsTwoSided`, the bundled two-sided
ideal defines a ring-congruence quotient `I.toTwoSided.ringCon.Quotient`. It is canonically
ring-isomorphic to the ideal quotient `R/I`.

The isomorphism sends the congruence class of a representative `r : R` to `Ideal.Quotient.mk I
r`, and its inverse preserves the same representative.

Reference: Dummit and Foote, *Abstract Algebra*, third edition, Section 7.3.
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

/-- Let `R` be an associative ring and `I : Ideal R` satisfy `I.IsTwoSided`. This is the ring
equivalence `I.toTwoSided.ringCon.Quotient ≃+* R/I`, identifying the ring-congruence and
ideal-quotient presentations. It sends the congruence class of `r : R` to its ideal quotient
class `r mod I`. -/
noncomputable def toTwoSidedQuotientEquiv
    (I : Ideal R) [I.IsTwoSided] :
    I.toTwoSided.ringCon.Quotient ≃+* R ⧸ I :=
  RingCon.congr
    (c := I.toTwoSided.ringCon)
    (d := Ideal.Quotient.ringCon I)
    (RingEquiv.refl _) (by
      rw [toTwoSided_ringCon_eq_quotientRingCon]
      rfl)

/-- For an associative ring `R`, a two-sided ideal `I`, and `r : R`, `toTwoSidedQuotientEquiv I`
sends the class of `r` in `I.toTwoSided.ringCon.Quotient` to `Ideal.Quotient.mk I r` in `R/I`. -/
@[simp]
theorem toTwoSidedQuotientEquiv_mk
    (I : Ideal R) [I.IsTwoSided] (r : R) :
    toTwoSidedQuotientEquiv I (↑r) =
      Ideal.Quotient.mk I r := by
  exact RingCon.congr_mk (RingEquiv.refl _) _ r

end Ideal
