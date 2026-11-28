/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ClassGroup.ExtendedHom

/-!
# Tests for the class group map on representatives over arbitrary fraction fields
-/

set_option autoImplicit false

@[expose] public section

namespace ClassGroupExtendedHomTest

open scoped nonZeroDivisors

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L]
  [IsFractionRing B L]

/-- The class of an invertible integral ideal goes to the class of its extension. -/
example (f : A →+* B) (hf : Function.Injective f) (b : Ideal A)
    (hb : IsUnit (b : FractionalIdeal A⁰ K)) (hb' : IsUnit ((b.map f : Ideal B) :
      FractionalIdeal B⁰ L)) :
    ClassGroup.map f hf (ClassGroup.mk K hb.unit) = ClassGroup.mk L hb'.unit := by
  rw [ClassGroup.map_mk K L]
  congr 1
  ext1
  rw [Units.coe_map, IsUnit.unit_spec, IsUnit.unit_spec]
  exact FractionalIdeal.extended_coeIdeal_eq_map _ _ _

/-- With the fraction fields `FractionRing A` and `FractionRing B`, `ClassGroup.map_mk` agrees
with Mathlib's `ClassGroup.map_quotientMk`. -/
example (f : A →+* B) (hf : Function.Injective f)
    (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    ClassGroup.map f hf (ClassGroup.mk (FractionRing A) I) = ClassGroup.mk (FractionRing B)
      (Units.map (FractionalIdeal.extendedHom' (FractionRing B)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)).toMonoidHom I) :=
  ClassGroup.map_mk _ _ f hf I

/-- The canonical isomorphism of fractional ideals is extension along the identity. -/
example (I : FractionalIdeal A⁰ K) :
    FractionalIdeal.canonicalEquiv A⁰ K (FractionRing A) I =
      I.extended (FractionRing A) (f := RingHom.id A) (M := A⁰) (N := A⁰)
        (show A⁰ ≤ A⁰.comap (RingHom.id A) from fun _ hy => hy) :=
  FractionalIdeal.canonicalEquiv_eq_extended K (FractionRing A) I

#check @ClassGroup.map_mk
#check @FractionalIdeal.canonicalEquiv_eq_extended

end ClassGroupExtendedHomTest
