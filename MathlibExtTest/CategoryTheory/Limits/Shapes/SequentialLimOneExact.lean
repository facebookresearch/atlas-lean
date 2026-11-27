/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module


public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOneExact
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Inverse-limit and lim¹ exact-sequence clients

The clients use the connecting morphism of a short exact row, its exactness
properties and the explicit product-epimorphism hypothesis. They retain the
chosen limits required by each comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits.SequentialLimOneExactTest

universe v u

section Generic

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCountableProducts C]

variable {A B D : ℕᵒᵖ ⥤ C}

example : (sequentialProductFunctor (C := C)).obj A = sequentialProduct A :=
  sequentialProductFunctor_obj A

example (f : A ⟶ B) :
    (sequentialProductFunctor (C := C)).map f = sequentialProductMap f :=
  sequentialProductFunctor_map f

variable (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)
  (hPg : Epi (sequentialProductMap S.g))

local instance : HasLimit S.X₁ :=
  hasLimit_of_sequential_product_and_kernel S.X₁
local instance : HasLimit S.X₂ :=
  hasLimit_of_sequential_product_and_kernel S.X₂
local instance : HasLimit S.X₃ :=
  hasLimit_of_sequential_product_and_kernel S.X₃

example : (sequentialProductShortComplex S).f = sequentialProductMap S.f :=
  sequentialProductShortComplex_f S

example : (sequentialProductShortComplex S).g = sequentialProductMap S.g :=
  sequentialProductShortComplex_g S

example : (sequentialProductShortComplex S).ShortExact :=
  sequentialProductShortComplex_shortExact_of_epi S hS hPg

example : (sequentialLimOneExactSequenceOfProductEpi S hS hPg).Exact :=
  sequentialLimOneExactSequenceOfProductEpi_exact S hS hPg

example : (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 0 1 =
    limMap S.f :=
  sequentialLimOneExactSequenceOfProductEpi_map_zero_one S hS hPg

example : (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 1 2 =
    limMap S.g :=
  sequentialLimOneExactSequenceOfProductEpi_map_one_two S hS hPg

example : (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 2 3 =
    sequentialLimOneConnectingOfProductEpi S hS hPg :=
  sequentialLimOneExactSequenceOfProductEpi_map_two_three S hS hPg

example : (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 3 4 =
    sequentialLimOneMap S.f :=
  sequentialLimOneExactSequenceOfProductEpi_map_three_four S hS hPg

example : (sequentialLimOneExactSequenceOfProductEpi S hS hPg).map' 4 5 =
    sequentialLimOneMap S.g :=
  sequentialLimOneExactSequenceOfProductEpi_map_four_five S hS hPg

example : Mono (limMap S.f) :=
  mono_limMap_f_of_product_epi S hS hPg

example : Epi (sequentialLimOneMap S.g) :=
  epi_sequentialLimOneMap_g_of_product_epi S hS hPg

variable {T : ShortComplex (ℕᵒᵖ ⥤ C)} (hT : T.ShortExact)
  (hPgT : Epi (sequentialProductMap T.g)) (φ : S ⟶ T)

local instance : HasLimit T.X₃ :=
  hasLimit_of_sequential_product_and_kernel T.X₃

example : limMap φ.τ₃ ≫
    sequentialLimOneConnectingOfProductEpi T hT hPgT =
      sequentialLimOneConnectingOfProductEpi S hS hPg ≫
        sequentialLimOneMap φ.τ₁ :=
  sequentialLimOneConnectingOfProductEpi_naturality
    hS hT hPg hPgT φ

end Generic

section ExactProducts

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCountableProducts C] [CountableAB4Star C]

variable (S : ShortComplex (ℕᵒᵖ ⥤ C)) (hS : S.ShortExact)

local instance : HasLimit S.X₁ :=
  hasLimit_of_sequential_product_and_kernel S.X₁
local instance : HasLimit S.X₂ :=
  hasLimit_of_sequential_product_and_kernel S.X₂
local instance : HasLimit S.X₃ :=
  hasLimit_of_sequential_product_and_kernel S.X₃

example : (sequentialProductShortComplex S).ShortExact :=
  sequentialProductShortComplex_shortExact S hS

example : (sequentialLimOneExactSequence S hS).Exact :=
  sequentialLimOneExactSequence_exact S hS

example : Mono (limMap S.f) := mono_limMap_f S hS

example : Epi (sequentialLimOneMap S.g) :=
  epi_sequentialLimOneMap_g S hS

variable {T : ShortComplex (ℕᵒᵖ ⥤ C)} (hT : T.ShortExact) (φ : S ⟶ T)

local instance : HasLimit T.X₃ :=
  hasLimit_of_sequential_product_and_kernel T.X₃

example : limMap φ.τ₃ ≫ sequentialLimOneConnecting T hT =
    sequentialLimOneConnecting S hS ≫ sequentialLimOneMap φ.τ₁ :=
  sequentialLimOneConnecting_naturality hS hT φ

end ExactProducts

section Specializations

section Ab

variable (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
  (hS : S.ShortExact)

local instance : HasLimit (S.X₁ : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  @hasLimit_of_sequential_product_and_kernel
    AddCommGrpCat.{u} _ _ _ _ S.X₁
local instance : HasLimit (S.X₂ : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  @hasLimit_of_sequential_product_and_kernel
    AddCommGrpCat.{u} _ _ _ _ S.X₂
local instance : HasLimit (S.X₃ : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  @hasLimit_of_sequential_product_and_kernel
    AddCommGrpCat.{u} _ _ _ _ S.X₃

example : (sequentialLimOneExactSequence S hS).Exact :=
  sequentialLimOneExactSequence_exact S hS

end Ab

section Modules

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{u} R))
  (hS : S.ShortExact)

local instance : HasLimit (S.X₁ : ℕᵒᵖ ⥤ ModuleCat.{u} R) :=
  @hasLimit_of_sequential_product_and_kernel
    (ModuleCat.{u} R) _ _ _ _ S.X₁
local instance : HasLimit (S.X₂ : ℕᵒᵖ ⥤ ModuleCat.{u} R) :=
  @hasLimit_of_sequential_product_and_kernel
    (ModuleCat.{u} R) _ _ _ _ S.X₂
local instance : HasLimit (S.X₃ : ℕᵒᵖ ⥤ ModuleCat.{u} R) :=
  @hasLimit_of_sequential_product_and_kernel
    (ModuleCat.{u} R) _ _ _ _ S.X₃

example : (sequentialLimOneExactSequence S hS).Exact :=
  sequentialLimOneExactSequence_exact S hS

end Modules

end Specializations

section Fixtures

private noncomputable def zeroGroup : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} (Fin 0 → ℤ))

private theorem zeroGroup_isZero : IsZero zeroGroup.{u} := by
  rw [IsZero.iff_id_eq_zero]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply ULift.ext
  funext i
  exact Fin.elim0 i

private noncomputable def zeroTower : ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const ℕᵒᵖ).obj zeroGroup.{u}

private theorem zeroTower_isZero : IsZero zeroTower.{u} :=
  Functor.isZero _ (fun _ => zeroGroup_isZero)

private noncomputable abbrev splitRow
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (𝟙 A) (0 : A ⟶ zeroTower.{u}) (by simp)

private theorem splitRow_shortExact
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : (splitRow A).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance
    (zeroTower_isZero.epi _)
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofId _ rfl

private noncomputable abbrev zeroRow :
    ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  splitRow zeroTower.{u}

example (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : True := by
  let S := splitRow A
  have hS : S.ShortExact := splitRow_shortExact A
  let _ : HasLimit S.X₁ := hasLimit_of_sequential_product_and_kernel S.X₁
  let _ : HasLimit S.X₂ := hasLimit_of_sequential_product_and_kernel S.X₂
  let _ : HasLimit S.X₃ := hasLimit_of_sequential_product_and_kernel S.X₃
  have : (sequentialLimOneExactSequence S hS).Exact :=
    sequentialLimOneExactSequence_exact S hS
  trivial

example : True := by
  let S := zeroRow.{u}
  have hS : S.ShortExact := splitRow_shortExact zeroTower.{u}
  let _ : HasLimit S.X₁ := hasLimit_of_sequential_product_and_kernel S.X₁
  let _ : HasLimit S.X₂ := hasLimit_of_sequential_product_and_kernel S.X₂
  let _ : HasLimit S.X₃ := hasLimit_of_sequential_product_and_kernel S.X₃
  have : (sequentialLimOneExactSequence S hS).Exact :=
    sequentialLimOneExactSequence_exact S hS
  trivial

end Fixtures

section Sign

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCountableProducts C]

example (A : ℕᵒᵖ ⥤ C) :
    sequentialDifference A ≫ Pi.π (fun n : ℕ => A.obj (op n)) 0 =
      Pi.π (fun n : ℕ => A.obj (op n)) 0 -
        Pi.π (fun n : ℕ => A.obj (op n)) 1 ≫
          A.map (homOfLE (Nat.le_succ 0)).op :=
  sequentialDifference_π A 0

end Sign

end CategoryTheory.Limits.SequentialLimOneExactTest

end

#print axioms CategoryTheory.Limits.sequentialLimOneExactSequence_exact
