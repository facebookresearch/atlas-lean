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

A nonunital associative ring A has commutator bracket [x,y]=xy−yx. Distributivity makes the
bracket additive in both variables, and associativity gives [x,[y,z]]=[[x,y],z]+[y,[x,z]]. Thus
it defines a Lie ring on the same additive group. If k is commutative and A is a k-module with
(r•x)y=r•(xy)=x(r•y), this bracket is k-bilinear and gives a Lie algebra over k.

A k-linear multiplicative map between such nonunital algebras is a Lie morphism with the same
underlying function and linear map. Conversion preserves identities and composition, with
independent universes for k and the algebra carriers. This commutator construction applies to
the nonunital matrix algebras considered in Loday–Quillen, “Cyclic homology and the Lie algebra
homology of matrices”, Comment. Math. Helv. 59 (1984), Section 6.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

universe u v w z

namespace LieRing

variable {A : Type v} [NonUnitalRing A]

/-- Let A be a nonunital associative ring. The bracket [x,y]=xy−yx defines a Lie ring on its
additive group: it is additive in each variable, satisfies [x,x]=0, and obeys
[x,[y,z]]=[[x,y],z]+[y,[x,z]]. The construction uses ring distributivity and associativity and
supplies no multiplicative unit. -/
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

/-- For a nonunital associative ring A equipped with its commutator Lie-ring structure and x,y∈A,
the chosen bracket satisfies [x,y]=xy−yx. This equality identifies the Lie operation with the
two products in the same nonunital ring. -/
theorem of_nonunital_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x := rfl

end LieRing

namespace LieAlgebra

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Let k be a commutative ring and A a nonunital associative ring with a k-module structure
satisfying (r•x)y=r•(xy)=x(r•y). The commutator Lie ring of A is a Lie algebra over k: in
particular [x,r•y]=r•[x,y], and additivity together with skew symmetry gives bilinearity in both
variables. The scalar ring and algebra carrier may lie in independent universes. -/
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

/-- Let k be a commutative ring and A,B nonunital associative rings with k-module structures such
that (r•x)y=r•(xy)=x(r•y) in each ring. Their commutator brackets are [x,y]=xy−yx. A k-linear
multiplicative map f:A→B defines this k-linear Lie morphism on the same carriers, because
f(xy−yx)=f(x)f(y)−f(y)f(x). Its underlying linear map is the linear map of f. The universes of
k,A,B are independent. -/
def toLieHom (f : A →ₙₐ[k] B) : A →ₗ⁅k⁆ B :=
  { (f : A →ₗ[k] B) with
    map_lie' := by
      intro x y
      change f (x * y - y * x) = f x * f y - f y * f x
      simp only [map_sub, map_mul] }

/-- Let k be a commutative ring and A,B nonunital associative rings with k-module structures such
that (r•x)y=r•(xy)=x(r•y) in each ring. Their commutator brackets are [x,y]=xy−yx. For a
nonunital k-algebra morphism f:A→B and x∈A, the induced Lie morphism sends x to f(x). The
equality identifies the map on the given algebra carriers. -/
@[simp]
theorem toLieHom_apply (f : A →ₙₐ[k] B) (x : A) : f.toLieHom x = f x := rfl

/-- Let k be a commutative ring and A,B nonunital associative rings with k-module structures such
that (r•x)y=r•(xy)=x(r•y) in each ring. Their commutator brackets are [x,y]=xy−yx. For a
nonunital k-algebra morphism f:A→B, the underlying k-linear map of its induced Lie morphism
equals the k-linear map of f. The conversion uses the same scalar actions and additive maps. -/
@[simp]
theorem toLieHom_toLinearMap (f : A →ₙₐ[k] B) :
    f.toLieHom.toLinearMap = (f : A →ₗ[k] B) := rfl

/-- Let k be commutative and A a nonunital associative ring with a k-module structure satisfying
(r•x)y=r•(xy)=x(r•y). Converting the nonunital k-algebra identity A→A to a Lie morphism gives
the identity of the commutator Lie algebra A. -/
@[simp]
theorem toLieHom_id : (NonUnitalAlgHom.id k A).toLieHom = (LieHom.id : A →ₗ⁅k⁆ A) := by
  ext x
  rfl

/-- Let k be commutative and A,B,C nonunital associative k-algebras whose scalar actions satisfy
(r•x)y=r•(xy)=x(r•y). For nonunital algebra maps f:A→B and g:B→C, the Lie morphism induced by
g∘f equals the composite of the Lie morphisms induced by f and g. All four scalar and carrier
universes are independent. -/
@[simp]
theorem toLieHom_comp (g : B →ₙₐ[k] C) (f : A →ₙₐ[k] B) :
    (g.comp f).toLieHom = g.toLieHom.comp f.toLieHom := by
  ext x
  rfl

end NonUnitalAlgHom
