/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductCoherence

/-! # Tests for zero coherence of core left-biproduct translation -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductCoherence

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check coreLeftBiprodZeroIso
#check coreLeftBiprodZeroIso_hom_app
#check coreLeftBiprodZeroIso_hom_app_iso_hom

example : coreLeftBiprodFunctor (0 : C) ≅ 𝟭 (Core C) :=
  coreLeftBiprodZeroIso

example (X : Core C) :
    ((coreLeftBiprodZeroIso (C := C)).hom.app X).iso.hom =
      (biprod.snd : (0 : C) ⊞ X.of ⟶ X.of) :=
  coreLeftBiprodZeroIso_hom_app_iso_hom X

/-- Boundary case: naturality at an identity core morphism. -/
example (X : Core C) :
    (coreLeftBiprodFunctor (0 : C)).map (𝟙 X) ≫
        (coreLeftBiprodZeroIso (C := C)).hom.app X =
      (coreLeftBiprodZeroIso (C := C)).hom.app X ≫
        (𝟭 (Core C)).map (𝟙 X) :=
  (coreLeftBiprodZeroIso (C := C)).hom.naturality (𝟙 X)

/-- Boundary case: modules over the zero ring form a zero category. -/
example :
    coreLeftBiprodFunctor (0 : ModuleCat (ZMod 1)) ≅
      𝟭 (Core (ModuleCat (ZMod 1))) :=
  coreLeftBiprodZeroIso

/-- The source at zero remains the chosen biproduct; no definitional
identity-functor equality is asserted. -/
example (X : Core C) :
    ((coreLeftBiprodFunctor (0 : C)).obj X).of =
      ((0 : C) ⊞ X.of : C) :=
  coreLeftBiprodFunctor_obj_of (0 : C) X

#print axioms coreLeftBiprodZeroIso
#print axioms coreLeftBiprodZeroIso_hom_app
#print axioms coreLeftBiprodZeroIso_hom_app_iso_hom

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductCoherence

end
