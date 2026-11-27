/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Module.NatInt

/-!
# Integer bilinear composition of additive tensor maps

Let A,B,C,D be additive commutative groups, with integer-module structures on A,B,D. A
biadditive map A×B→D is ℤ-bilinear. For additive g:A⊗_ℤB→C and f:C→D, the curried bilinear
composite is (x,y)↦f(g(x⊗y)). All group universes may be independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v w z
open scoped TensorProduct

namespace AddMonoidHom
variable {A : Type u} {B : Type v} {C : Type w} {D : Type z}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable [Module ℤ A] [Module ℤ B] [Module ℤ D]

/-- **Biadditive map as an integer-bilinear map.**

Let A,B,D be additive commutative groups with their ℤ-module structures. For biadditive
h:A×B→D, toIntBilinear h:A→ₗ[ℤ](B→ₗ[ℤ]D) has value h(x,y).
-/
def toIntBilinear (h : A →+ B →+ D) :
    A →ₗ[ℤ] B →ₗ[ℤ] D := by
  let k : A →+ (B →ₗ[ℤ] D) :=
    { toFun := fun x =>
        { toFun := h x
          map_add' := (h x).map_add
          map_smul' := fun r y => by
            simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul (h x) ℤ ℤ r y }
      map_zero' := by
        ext y
        exact congrArg (fun a : B →+ D => a y) h.map_zero
      map_add' := by
        intro x z
        ext y
        exact congrArg (fun a : B →+ D => a y) (h.map_add x z) }
  exact
    { toFun := k
      map_add' := k.map_add
      map_smul' := fun r x => by
        simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul k ℤ ℤ r x }

/-- **Value of integer bilinear conversion.**

For additive commutative groups A,B,D with ℤ-actions and biadditive h, toIntBilinear h x
y=h(x,y).
-/
theorem toIntBilinear_apply (h : A →+ B →+ D) (x : A) (y : B) :
    toIntBilinear h x y = h x y := rfl

/-- **Integer bilinear map from two additive laws.**

Let A,B,D be additive commutative groups with ℤ-actions. If f:A×B→D is additive in each
variable, intBilinearOfAdd f hLeft hRight is the ℤ-bilinear map with those values.
-/
def intBilinearOfAdd (f : A → B → D)
    (hLeft : ∀ x z y, f (x + z) y = f x y + f z y)
    (hRight : ∀ x y z, f x (y + z) = f x y + f x z) :
    A →ₗ[ℤ] B →ₗ[ℤ] D :=
  toIntBilinear <|
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (f x) (hRight x))
      (fun x z => AddMonoidHom.ext fun y => hLeft x z y)

/-- **Value of the bilinear map constructed from additive laws.**

For additive commutative groups A,B,D and separately additive f:A×B→D, intBilinearOfAdd f
hLeft hRight x y=f(x,y).
-/
theorem intBilinearOfAdd_apply (f : A → B → D)
    (hLeft : ∀ x z y, f (x + z) y = f x y + f z y)
    (hRight : ∀ x y z, f x (y + z) = f x y + f x z) (x : A) (y : B) :
    intBilinearOfAdd f hLeft hRight x y = f x y := rfl

/-- **Curried integer-bilinear composite through a tensor.**

Let A,B,C,D be additive commutative groups, g:A⊗_ℤB→C and f:C→D additive. The ℤ-bilinear map
compIntTensorBilinear f g sends (x,y) to f(g(x⊗y)).
-/
def compIntTensorBilinear (f : C →+ D) (g : A ⊗[ℤ] B →+ C) :
    A →ₗ[ℤ] B →ₗ[ℤ] D := by
  let h : A →+ B →+ D :=
    { toFun := fun x =>
        { toFun := fun y => f (g (x ⊗ₜ[ℤ] y))
          map_zero' := by simp only [TensorProduct.tmul_zero, map_zero]
          map_add' := by intro y z; simp only [TensorProduct.tmul_add, map_add] }
      map_zero' := by
        ext y
        change f (g ((0 : A) ⊗ₜ[ℤ] y)) = 0
        simp only [TensorProduct.zero_tmul, map_zero]
      map_add' := by
        intro x z
        ext y
        change f (g ((x + z) ⊗ₜ[ℤ] y)) = f (g (x ⊗ₜ[ℤ] y)) + f (g (z ⊗ₜ[ℤ] y))
        simp only [TensorProduct.add_tmul, map_add] }
  exact toIntBilinear h

/-- **Value of the additive tensor composite.**

For additive commutative groups A,B,C,D, additive g:A⊗_ℤB→C and f:C→D, compIntTensorBilinear f
g x y=f(g(x⊗_ℤy)).
-/
theorem compIntTensorBilinear_apply (f : C →+ D) (g : A ⊗[ℤ] B →+ C) (x : A) (y : B) :
    compIntTensorBilinear f g x y = f (g (x ⊗ₜ[ℤ] y)) := rfl

end AddMonoidHom
