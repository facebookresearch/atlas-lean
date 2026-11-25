/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.ExactCategoryFunctor

/-!
# Tests for the exact-category Waldhausen-exact adapter

These clients pin the explicit mixed-universe adapter, consume each of its
four fields, and verify identity and source-first composition by proof
irrelevance.  Type-zero and Type-one clients exercise the universe boundary.

The standard Waldhausen structures and the resulting exactness proof remain
explicit: no global instance, Stage map, App2 theorem, or approximation
consequence is added.  Stage comparison is deferred because the approved
generic Stage-map packet is not present on this base.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace MathlibExtTest.CategoryTheory.Waldhausen.ExactCategoryFunctorTests

section General

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

example : F.IsWaldhausenExact :=
  Functor.IsWaldhausenExact.ofExactCategory F

example {X : C} (hX : IsZero X) : IsZero (F.obj X) :=
  (Functor.IsWaldhausenExact.ofExactCategory F).map_isZero hX

example {X Y : C} (f : X ⟶ Y) (hf : IsCofibration f) :
    IsCofibration (F.map f) :=
  (Functor.IsWaldhausenExact.ofExactCategory F).map_cofibration f hf

example {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    IsWeakEquivalence (F.map f) :=
  (Functor.IsWaldhausenExact.ofExactCategory F).map_weakEquivalence f hf

example {X Y X' P : C} (i : X ⟶ Y) (f : X ⟶ X')
    (inl : X' ⟶ P) (inr : Y ⟶ P)
    (hi : IsCofibration i) (hpo : IsPushout f i inl inr) :
    IsPushout (F.map f) (F.map i) (F.map inl) (F.map inr) :=
  (Functor.IsWaldhausenExact.ofExactCategory F).map_pushout
    i f inl inr hi hpo

end General

section IdentityAndComposition

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D
local instance : WaldhausenCategoryWithoutGluing E :=
  ExactCategory.waldhausenCategory E

example :
    Functor.IsWaldhausenExact.ofExactCategory (𝟭 C) =
      Functor.IsWaldhausenExact.id :=
  Subsingleton.elim _ _

example (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [F.IsExact] [G.Additive] [G.IsExact] :
    Functor.IsWaldhausenExact.ofExactCategory (F ⋙ G) =
      (Functor.IsWaldhausenExact.ofExactCategory F).comp
        (Functor.IsWaldhausenExact.ofExactCategory G) :=
  Subsingleton.elim _ _

end IdentityAndComposition

section TypeZero

variable {C₀ D₀ : Type 0} [Category.{0} C₀] [Category.{0} D₀]
  [Preadditive C₀] [Preadditive D₀]
  [HasZeroObject C₀] [HasZeroObject D₀]
  [HasBinaryBiproducts C₀] [HasBinaryBiproducts D₀]
  [ExactCategory C₀] [ExactCategory D₀]
variable (F₀ : C₀ ⥤ D₀) [F₀.Additive] [F₀.IsExact]

example :
    letI : WaldhausenCategoryWithoutGluing C₀ := ExactCategory.waldhausenCategory C₀
    letI : WaldhausenCategoryWithoutGluing D₀ := ExactCategory.waldhausenCategory D₀
    F₀.IsWaldhausenExact :=
  Functor.IsWaldhausenExact.ofExactCategory F₀

end TypeZero

section TypeOne

variable {C₁ D₁ : Type 1} [Category.{1} C₁] [Category.{1} D₁]
  [Preadditive C₁] [Preadditive D₁]
  [HasZeroObject C₁] [HasZeroObject D₁]
  [HasBinaryBiproducts C₁] [HasBinaryBiproducts D₁]
  [ExactCategory C₁] [ExactCategory D₁]
variable (F₁ : C₁ ⥤ D₁) [F₁.Additive] [F₁.IsExact]

example :
    letI : WaldhausenCategoryWithoutGluing C₁ := ExactCategory.waldhausenCategory C₁
    letI : WaldhausenCategoryWithoutGluing D₁ := ExactCategory.waldhausenCategory D₁
    F₁.IsWaldhausenExact :=
  Functor.IsWaldhausenExact.ofExactCategory F₁

end TypeOne

section NegativeInference

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing C

variable (F : C ⥤ D) [F.Additive]

#guard_msgs (error, substring := true) in
#synth F.IsExact

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

#guard_msgs (error, substring := true) in
#synth F.IsWaldhausenExact

variable (G : C ⥤ D) [G.Additive] [G.IsExact]

#guard_msgs (error, substring := true) in
#synth G.IsWaldhausenExact

end NegativeInference

#print axioms CategoryTheory.Functor.IsWaldhausenExact.ofExactCategory

end MathlibExtTest.CategoryTheory.Waldhausen.ExactCategoryFunctorTests
