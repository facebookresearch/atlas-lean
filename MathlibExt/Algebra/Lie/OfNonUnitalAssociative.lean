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

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Tactic.Abel

/-!
# Commutator Lie algebras of nonunital associative algebras

The bracket is the original multiplication commutator on the original carrier.
The constructors are reducible non-instances, following Mathlib's convention
for associative rings, so no unrelated existing Lie bracket is replaced.
Nonunital algebra maps retain their actual underlying linear maps.

This is the carrier/map input needed for the stable matrix Lie algebra in
Loday--Quillen, *Cyclic homology and the Lie algebra homology of matrices*,
Comment. Math. Helv. 59 (1984), Section 6. No unit is assigned to a stable
matrix algebra and no cyclic/primitive-homology theorem is asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

universe u v w z

namespace LieRing

variable {A : Type v} [NonUnitalRing A]

/-- A nonunital associative ring carries its actual multiplication commutator bracket. -/
@[instance_reducible]
def ofNonUnitalAssociativeRing : LieRing A where
  bracket x y := x * y - y * x
  add_lie x y z := by
    change (x + y) * z - z * (x + y) = (x * z - z * x) + (y * z - z * y)
    simp only [add_mul, mul_add]
    abel
  lie_add x y z := by
    change x * (y + z) - (y + z) * x = (x * y - y * x) + (x * z - z * x)
    simp only [add_mul, mul_add]
    abel
  lie_self x := sub_self (x * x)
  leibniz_lie x y z := by
    change x * (y * z - z * y) - (y * z - z * y) * x =
      (x * y - y * x) * z - z * (x * y - y * x) +
        (y * (x * z - z * x) - (x * z - z * x) * y)
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

end LieRing

attribute [local instance 100] LieRing.ofNonUnitalAssociativeRing

namespace LieRing

variable {A : Type v} [NonUnitalRing A]

/-- The chosen nonunital associative Lie bracket is the original commutator. -/
theorem of_nonunital_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x := rfl

end LieRing

namespace LieAlgebra

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The existing scalar action makes the nonunital multiplication commutator k-bilinear. -/
@[instance_reducible]
def ofNonUnitalAssociativeAlgebra : LieAlgebra k A where
  lie_smul r x y := by
    change x * (r • y) - (r • y) * x = r • (x * y - y * x)
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]

end LieAlgebra

attribute [local instance 100] LieAlgebra.ofNonUnitalAssociativeAlgebra

namespace NonUnitalAlgHom

variable {k : Type u} [CommRing k]
variable {A : Type v} {B : Type w} {C : Type z}
  [NonUnitalRing A] [NonUnitalRing B] [NonUnitalRing C]
  [Module k A] [Module k B] [Module k C]
  [IsScalarTower k A A] [IsScalarTower k B B] [IsScalarTower k C C]
  [SMulCommClass k A A] [SMulCommClass k B B] [SMulCommClass k C C]

/-- A genuine nonunital algebra map preserves the original commutator Lie brackets. -/
def toLieHom (f : A →ₙₐ[k] B) : A →ₗ⁅k⁆ B :=
  { (f : A →ₗ[k] B) with
    map_lie' := by
      intro x y
      change f (x * y - y * x) = f x * f y - f y * f x
      simp only [map_sub, map_mul] }

/-- The Lie map is exactly the original function. -/
@[simp]
theorem toLieHom_apply (f : A →ₙₐ[k] B) (x : A) : f.toLieHom x = f x := rfl

/-- No scalar or carrier map is changed by the conversion. -/
@[simp]
theorem toLieHom_toLinearMap (f : A →ₙₐ[k] B) :
    f.toLieHom.toLinearMap = (f : A →ₗ[k] B) := rfl

/-- The actual nonunital identity becomes the native Lie identity. -/
@[simp]
theorem toLieHom_id : (NonUnitalAlgHom.id k A).toLieHom = (LieHom.id : A →ₗ⁅k⁆ A) := by
  ext x
  rfl

/-- Conversion commutes with actual nonunital composition. -/
@[simp]
theorem toLieHom_comp (g : B →ₙₐ[k] C) (f : A →ₙₐ[k] B) :
    (g.comp f).toLieHom = g.toLieHom.comp f.toLieHom := by
  ext x
  rfl

end NonUnitalAlgHom
