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

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Nonunital star-algebra homomorphisms from linear maps

A linear map that preserves multiplication and the involution gives a
nonunital star-algebra homomorphism with the same values. The coefficient
semiring and source and target semirings retain their independent universes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace NonUnitalStarAlgHom

universe uR uA uB

section LinearConstructor

variable {R : Type uR} [CommSemiring R]
    {A : Type uA} [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    {B : Type uB} [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- Let `R` be a commutative semiring and let `A`, `B` be possibly nonunital, nonassociative semirings
with `R`-module structures and star operations. Let `f : A →ₗ[R] B` preserve multiplication and
star. These two preservation laws give a nonunital star homomorphism with the same values as `f`.
-/
def ofLinearMap (f : A →ₗ[R] B)
    (hmul : ∀ a b, f (a * b) = f a * f b)
    (hstar : ∀ a, f (star a) = star (f a)) : A →⋆ₙₐ[R] B where
  toNonUnitalAlgHom :=
    { f.toAddMonoidHom with
      toFun := f
      map_mul' := hmul
      map_smul' := fun r a => by
        simpa only [MonoidHom.id_apply] using f.map_smul r a }
  map_star' := hstar

/-- Let `R` be a commutative semiring and let `A`, `B` be possibly nonunital, nonassociative semirings
with `R`-module structures and star operations. Let `f : A →ₗ[R] B` preserve multiplication and
star. For every `a ∈ A`, the resulting nonunital star homomorphism has value `f a`.
-/
@[simp]
theorem ofLinearMap_apply (f : A →ₗ[R] B)
    (hmul : ∀ a b, f (a * b) = f a * f b)
    (hstar : ∀ a, f (star a) = star (f a)) (a : A) :
    ofLinearMap f hmul hstar a = f a := rfl

end LinearConstructor

end NonUnitalStarAlgHom

end
