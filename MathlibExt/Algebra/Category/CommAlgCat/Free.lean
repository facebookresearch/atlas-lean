/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The literal polynomial free/forget adjunction for commutative algebras

The free object on X is MvPolynomial X k. Maps rename the actual variable
index, the unit sends x to X x, and the counit evaluates each generator at
its corresponding algebra element. Native polynomial evaluation proves both
triangle identities.

The base ring and carrier-size parameter are independent. We use the stable
carrier universe max u v, so polynomial formation remains in one category.
The variable index is an arbitrary type.

The free-object presentation follows the native CommRingCat.free API of
Kim Morrison, Johannes Hölzl and Andrew Yang. The adjunction over k
uses the native polynomial variable and evaluation maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- The actual free commutative k-algebra functor, using literal multivariable polynomials. -/
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

/-- The free carrier is the literal polynomial ring on the displayed variable type. -/
@[simp]
theorem free_obj_carrier (X : Type (max u v)) :
    ↥((free.{u, v} k).obj X) = MvPolynomial X k := rfl

/-- The free morphism is the actual native variable-renaming algebra map. -/
@[simp]
theorem free_map_hom {X Y : Type (max u v)} (f : X ⟶ Y) :
    ((free.{u, v} k).map f).hom = MvPolynomial.rename (R := k) f := rfl

/-- Renaming sends each actual variable generator to its renamed generator. -/
theorem free_map_X {X Y : Type (max u v)} (f : X ⟶ Y) (x : X) :
    ((free.{u, v} k).map f).hom (MvPolynomial.X x) = MvPolynomial.X (f x) :=
  MvPolynomial.rename_X f x

/-- Renaming preserves each base coefficient. -/
theorem free_map_C {X Y : Type (max u v)} (f : X ⟶ Y) (c : k) :
    ((free.{u, v} k).map f).hom (MvPolynomial.C c) = MvPolynomial.C c :=
  MvPolynomial.rename_C f c

/-- The actual unit of the polynomial free/forget pair. -/
def freeUnit :
    𝟭 (Type (max u v)) ⟶ free.{u, v} k ⋙ forget (CommAlgCat.{max u v} k) where
  app X := TypeCat.ofHom (fun x : X => (MvPolynomial.X x : MvPolynomial X k))
  naturality {X Y} f := by
    apply ConcreteCategory.ext_apply
    intro x
    change MvPolynomial.X (f x) = MvPolynomial.rename (R := k) f (MvPolynomial.X x)
    exact (MvPolynomial.rename_X f x).symm

/-- The unit includes each element as its own formal variable. -/
theorem freeUnit_app_apply (X : Type (max u v)) (x : X) :
    (freeUnit.{u, v} k).app X x = MvPolynomial.X x := rfl

/-- The actual counit evaluates a polynomial in algebra elements at those elements. -/
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

/-- The counit is the actual native algebra evaluation map. -/
@[simp]
theorem freeCounit_app_hom (A : CommAlgCat.{max u v} k) :
    ((freeCounit.{u, v} k).app A).hom = MvPolynomial.aeval (R := k) (fun a : A => a) := rfl

/-- The counit evaluates the generator labelled by a at a. -/
theorem freeCounit_app_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((freeCounit.{u, v} k).app A).hom (MvPolynomial.X a) = a :=
  MvPolynomial.aeval_X (fun a : A => a) a

/-- Evaluation retains the actual k-algebra coefficient map. -/
theorem freeCounit_app_C (A : CommAlgCat.{max u v} k) (c : k) :
    ((freeCounit.{u, v} k).app A).hom (MvPolynomial.C c) = algebraMap k A c :=
  MvPolynomial.aeval_C (fun a : A => a) c

/-- The polynomial functor is left adjoint to the concrete forgetful functor. -/
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

/-- The adjunction's unit is the constructed generator inclusion. -/
@[simp]
theorem freeForgetAdjunction_unit :
    (freeForgetAdjunction.{u, v} k).unit = freeUnit.{u, v} k := rfl

/-- The adjunction's counit is the constructed evaluation. -/
@[simp]
theorem freeForgetAdjunction_counit :
    (freeForgetAdjunction.{u, v} k).counit = freeCounit.{u, v} k := rfl

/-- The universal correspondence reads an algebra map on the actual variable generators. -/
@[simp]
theorem freeForgetAdjunction_homEquiv_apply
    (X : Type (max u v)) (A : CommAlgCat.{max u v} k)
    (f : (free.{u, v} k).obj X ⟶ A) (x : X) :
    ((freeForgetAdjunction.{u, v} k).homEquiv X A f) x = f.hom (MvPolynomial.X x) := rfl

/-- The inverse universal map is the actual evaluation extending the supplied variable function. -/
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
