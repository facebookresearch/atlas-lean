/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Portions of this file are adapted from:

`Mathlib/Algebra/Category/Ring/Adjunctions.lean` (Mathlib):
Copyright (c) 2019 Kim Morrison. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kim Morrison, Johannes Hölzl, Andrew Yang
Polynomial free/forget unit, counit and adjunction constructions.
-/
-- Adapter: @toskua
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.CategoryTheory.Adjunction.Basic

/- The free-object presentation follows the native CommRingCat.free API of
Kim Morrison, Johannes Hölzl and Andrew Yang. The adjunction over k
uses the native polynomial variable and evaluation maps. -/

/-!
# Polynomial free/forget adjunction for commutative algebras

Fix a commutative ring `k` in universe `u` and carrier height
`T=max(u,v)`. The free functor `Type T → CommAlgCat_T(k)` sends
`X` to `MvPolynomial X k` and a function `f : X → Y` to variable
renaming. Renaming sends `X(x)` to `X(f(x))` and fixes every
constant polynomial `C(c)` for `c : k`.

The adjunction with the carrier-forgetful functor identifies
`k`-algebra maps `MvPolynomial X k → A` with functions `X → A`.
The unit includes each `x` as its formal variable; the counit evaluates
variables labelled by elements of `A` at those elements, and coefficients
through `algebraMap k A`. The variable types are arbitrary and the
ring and carrier-height parameters are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. The free commutative algebra functor has object
`X ↦ MvPolynomial X k` and maps given by variable renaming. -/
def free : Type (max u v) ⥤ CommAlgCat.{max u v} k where
  obj X := CommAlgCat.of k (MvPolynomial X k)
  map f := CommAlgCat.ofHom (MvPolynomial.rename (R := k) f)
  map_id X := by
    apply CommAlgCat.hom_ext
    change (MvPolynomial.rename (R := k) (id : X → X) : MvPolynomial X k →ₐ[k] _) = AlgHom.id k _
    exact MvPolynomial.rename_id
  map_comp f g := by
    apply CommAlgCat.hom_ext
    change MvPolynomial.rename (R := k) (g ∘ f) =
      (MvPolynomial.rename (R := k) g).comp (MvPolynomial.rename (R := k) f)
    exact (MvPolynomial.rename_comp_rename f g).symm

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. For `X : Type T`, the underlying carrier of its free
commutative algebra is `MvPolynomial X k`. -/
@[simp]
theorem free_obj_carrier (X : Type (max u v)) :
    ↥((free.{u, v} k).obj X) = MvPolynomial X k := rfl

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `X,Y : Type T` and `f : X → Y`. The free-algebra
map on `f` is the `k`-algebra homomorphism
`MvPolynomial.rename(f) : MvPolynomial X k → MvPolynomial Y k`. -/
@[simp]
theorem free_map_hom {X Y : Type (max u v)} (f : X ⟶ Y) :
    ((free.{u, v} k).map f).hom = MvPolynomial.rename (R := k) f := rfl

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `X,Y : Type T` and `f : X → Y`. For `x : X`, the
free-algebra map sends the variable
polynomial `X(x)` to the variable polynomial `X(f(x))`. -/
theorem free_map_X {X Y : Type (max u v)} (f : X ⟶ Y) (x : X) :
    ((free.{u, v} k).map f).hom (MvPolynomial.X x) = MvPolynomial.X (f x) :=
  MvPolynomial.rename_X f x

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `X,Y : Type T` and `f : X → Y`. For each `c : k`,
the induced map
`MvPolynomial X k → MvPolynomial Y k` sends the source constant
polynomial `C(c)` to the target constant polynomial `C(c)`. -/
theorem free_map_C {X Y : Type (max u v)} (f : X ⟶ Y) (c : k) :
    ((free.{u, v} k).map f).hom (MvPolynomial.C c) = MvPolynomial.C c :=
  MvPolynomial.rename_C f c

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. The natural unit of free algebra followed by carrier
forgetting has component `X → MvPolynomial X k`, sending
`x` to its formal variable `X(x)`. -/
def freeUnit :
    𝟭 (Type (max u v)) ⟶ free.{u, v} k ⋙ forget (CommAlgCat.{max u v} k) where
  app X := TypeCat.ofHom (fun x : X => (MvPolynomial.X x : MvPolynomial X k))
  naturality {X Y} f := by
    apply ConcreteCategory.ext_apply
    intro x
    change MvPolynomial.X (f x) = MvPolynomial.rename (R := k) f (MvPolynomial.X x)
    exact (MvPolynomial.rename_X f x).symm

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. For `X : Type T` and `x : X`, the adjunction unit has
value `η_X(x)=MvPolynomial.X(x)`. -/
theorem freeUnit_app_apply (X : Type (max u v)) (x : X) :
    (freeUnit.{u, v} k).app X x = MvPolynomial.X x := rfl

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `A` be a commutative `k`-algebra with carrier in
`T`. The natural counit is the `k`-algebra evaluation map
`MvPolynomial A k → A`, taking each variable labelled by `a : A`
to `a` and each coefficient to its image in `A`. -/
def freeCounit :
    forget (CommAlgCat.{max u v} k) ⋙ free.{u, v} k ⟶ 𝟭 (CommAlgCat.{max u v} k) where
  app A := CommAlgCat.ofHom (MvPolynomial.aeval (R := k) (fun a : A => a))
  naturality {A B} f := by
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro a
    change (MvPolynomial.aeval (R := k) (fun b : B => b))
        (MvPolynomial.rename (R := k) f.hom (MvPolynomial.X a)) =
      f.hom ((MvPolynomial.aeval (R := k) (fun a : A => a)) (MvPolynomial.X a))
    simp only [MvPolynomial.rename_X, MvPolynomial.aeval_X]

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `A` be a commutative `k`-algebra with carrier in
`T`. The counit at `A` is `MvPolynomial.aeval(id_A)`, the
`k`-algebra homomorphism extending the identity function on the
variable set underlying `A`. -/
@[simp]
theorem freeCounit_app_hom (A : CommAlgCat.{max u v} k) :
    ((freeCounit.{u, v} k).app A).hom = MvPolynomial.aeval (R := k) (fun a : A => a) := rfl

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `A` be a commutative `k`-algebra with carrier in
`T`. For `a : A`, the counit evaluates the formal variable
`X(a)` at the element `a`. -/
theorem freeCounit_app_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((freeCounit.{u, v} k).app A).hom (MvPolynomial.X a) = a :=
  MvPolynomial.aeval_X (fun a : A => a) a

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `A` be a commutative `k`-algebra with carrier in
`T`. For `c : k`, the counit sends the constant polynomial
`C(c)` to `algebraMap k A(c)`. -/
theorem freeCounit_app_C (A : CommAlgCat.{max u v} k) (c : k) :
    ((freeCounit.{u, v} k).app A).hom (MvPolynomial.C c) = algebraMap k A c :=
  MvPolynomial.aeval_C (fun a : A => a) c

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. The polynomial free functor is left adjoint to
carrier
forgetting, with natural correspondence between `k`-algebra maps
`MvPolynomial X k → A` and functions `X → A`. -/
def freeForgetAdjunction : free.{u, v} k ⊣ forget (CommAlgCat.{max u v} k) where
  unit := freeUnit.{u, v} k
  counit := freeCounit.{u, v} k
  left_triangle_components X := by
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro x
    change (MvPolynomial.aeval (R := k) (fun p : MvPolynomial X k => p))
        (MvPolynomial.rename (R := k) (fun x : X => (MvPolynomial.X x : MvPolynomial X k))
          (MvPolynomial.X x)) = MvPolynomial.X x
    simp only [MvPolynomial.rename_X, MvPolynomial.aeval_X]
  right_triangle_components A := by
    apply ConcreteCategory.ext_apply
    intro a
    change (MvPolynomial.aeval (R := k) (fun a : A => a)) (MvPolynomial.X a) = a
    exact MvPolynomial.aeval_X (fun a : A => a) a

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. The unit of the polynomial free/forget adjunction is
its natural generator inclusion `x ↦ X(x)`. -/
@[simp]
theorem freeForgetAdjunction_unit :
    (freeForgetAdjunction.{u, v} k).unit = freeUnit.{u, v} k := rfl

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. The counit of the polynomial free/forget adjunction
is
its natural evaluation map `MvPolynomial A k → A`. -/
@[simp]
theorem freeForgetAdjunction_counit :
    (freeForgetAdjunction.{u, v} k).counit = freeCounit.{u, v} k := rfl

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `A` be a commutative `k`-algebra with carrier in
`T`. For `X : Type T` and a `k`-algebra map
`f : MvPolynomial X k → A`, the associated function on variables
has value `x ↦ f(X(x))`. -/
@[simp]
theorem freeForgetAdjunction_homEquiv_apply
    (X : Type (max u v)) (A : CommAlgCat.{max u v} k)
    (f : (free.{u, v} k).obj X ⟶ A) (x : X) :
    ((freeForgetAdjunction.{u, v} k).homEquiv X A f) x = f.hom (MvPolynomial.X x) := rfl

/-- Let `k` be a commutative ring in universe `u` and
`T=max(u,v)`. The polynomial free functor sends types in `T` to
commutative `k`-algebras with carriers in `T`. Let `A` be a commutative `k`-algebra with carrier in
`T`. For `X : Type T` and a function `g : X → A`, the inverse
adjunction correspondence is the algebra evaluation map
`MvPolynomial.aeval(g)`, extending the specified variable values. -/
theorem freeForgetAdjunction_homEquiv_symm_hom
    (X : Type (max u v)) (A : CommAlgCat.{max u v} k)
    (g : X ⟶ (forget (CommAlgCat.{max u v} k)).obj A) :
    (((freeForgetAdjunction.{u, v} k).homEquiv X A).symm g).hom =
        MvPolynomial.aeval (R := k) g := by
  apply MvPolynomial.algHom_ext
  intro x
  change (MvPolynomial.aeval (R := k) (fun a : A => a))
      (MvPolynomial.rename (R := k) g (MvPolynomial.X x)) =
    MvPolynomial.aeval (R := k) g (MvPolynomial.X x)
  simp only [MvPolynomial.rename_X, MvPolynomial.aeval_X]

instance : (free.{u, v} k).IsLeftAdjoint :=
  ⟨forget (CommAlgCat.{max u v} k), ⟨freeForgetAdjunction.{u, v} k⟩⟩

instance : (forget (CommAlgCat.{max u v} k)).IsRightAdjoint :=
  ⟨free.{u, v} k, ⟨freeForgetAdjunction.{u, v} k⟩⟩

end CommAlgCat

end
