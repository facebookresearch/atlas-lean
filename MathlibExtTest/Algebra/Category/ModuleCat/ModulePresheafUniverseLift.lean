/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Data.ZMod.Basic

/-! # Tests for the universe lift of module presheaves

Lifted restriction maps are the source restriction maps after `ULift.down`; they compose like the
source maps and are semilinear along the restriction maps of the ring presheaf. Lifted morphisms
are natural, and the lift is functorial and additive. The concrete checks use the nonconstant
inverse system of rings `ℤ/2ⁿ⁺¹ → ℤ/2ⁿ`, whose restriction maps are not the identity.
-/

open CategoryTheory Opposite MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift

namespace MathlibExtTest.Algebra.Category.ModuleCat.ModulePresheafUniverseLift

universe u v w

section General

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{0})

/-- Lifted restriction maps are the restriction maps of the source presheaf. -/
example (M : PresheafOfModules.{0} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ULift.{w} (M.obj X)) :
    ULift.down (((obj R M).map f).hom x) = (M.map f).hom x.down := rfl

/-- Lifted restriction maps compose like the source restriction maps. -/
example (M : PresheafOfModules.{0} R) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : ULift.{w} (M.obj X)) :
    ULift.down (((obj R M).map (f ≫ g)).hom x) = (M.map g).hom ((M.map f).hom x.down) := by
  rw [PresheafOfModules.map_comp]
  rfl

/-- Lifted restriction maps are semilinear along the restriction maps of the ring presheaf. -/
example (M : PresheafOfModules.{0} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X)
    (x : ULift.{w} (M.obj X)) :
    ULift.down (((obj R M).map f).hom (r • x)) = (R.map f).hom r • (M.map f).hom x.down :=
  PresheafOfModules.map_smul M f r x.down

/-- Lifted restriction maps preserve addition. -/
example (M : PresheafOfModules.{0} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x y : ULift.{w} (M.obj X)) :
    ULift.down (((obj R M).map f).hom (x + y)) =
      (M.map f).hom x.down + (M.map f).hom y.down :=
  map_add (M.map f).hom x.down y.down

/-- Lifted morphisms commute with the lifted restriction maps. -/
example {M N : PresheafOfModules.{0} R} (φ : M ⟶ N) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (x : ULift.{w} (M.obj X)) :
    ULift.down (((map R φ).app Y).hom (((obj R M).map g).hom x)) =
      (N.map g).hom ((φ.app X).hom x.down) :=
  ConcreteCategory.congr_hom (φ.naturality g) x.down

/-- The lift is functorial on components. -/
example {M N P : PresheafOfModules.{0} R} (φ : M ⟶ N) (ψ : N ⟶ P) (X : Cᵒᵖ)
    (x : ULift.{w} (M.obj X)) :
    ULift.down ((((functor R).map (φ ≫ ψ)).app X).hom x) =
      (ψ.app X).hom ((φ.app X).hom x.down) := rfl

/-- The lift of a sum of morphisms is computed componentwise after `ULift.down`. -/
example {M N : PresheafOfModules.{0} R} (φ ψ : M ⟶ N) (X : Cᵒᵖ) (x : ULift.{w} (M.obj X)) :
    ULift.down ((((functor R).map (φ + ψ)).app X).hom x) =
      (φ.app X).hom x.down + (ψ.app X).hom x.down := rfl

/-- The `Additive` instance of the lift. -/
example {M N : PresheafOfModules.{0} R} (φ ψ : M ⟶ N) :
    (functor R : PresheafOfModules.{0} R ⥤ PresheafOfModules.{w} R).map (φ + ψ) =
      (functor R).map φ + (functor R).map ψ :=
  Functor.map_add _

end General

section TwoAdic

/-- The nonconstant inverse system of rings `ℤ/2ⁿ⁺¹ → ℤ/2ⁿ`. -/
noncomputable abbrev twoAdic : ℕᵒᵖ ⥤ RingCat.{0} :=
  Functor.ofOpSequence (X := fun n => RingCat.of (ZMod (2 ^ n)))
    (fun n => RingCat.ofHom (ZMod.castHom (pow_dvd_pow 2 n.le_succ) (ZMod (2 ^ n))))

/-- In the lift of the unit presheaf, restriction from `ℤ/4` to `ℤ/2` is reduction mod 2. -/
example : ULift.down (((obj twoAdic (PresheafOfModules.unit twoAdic)).map
    (homOfLE (show 1 ≤ 2 by omega)).op).hom (ULift.up.{1} (3 : ZMod (2 ^ 2)))) =
      (1 : ZMod (2 ^ 1)) := by
  change ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ 1)) (ZMod (2 ^ 1)) (3 : ZMod (2 ^ 2)) = 1
  decide +kernel

/-- The lifted restriction from `ℤ/8` to `ℤ/2` is the composite reduction. -/
example : ULift.down (((obj twoAdic (PresheafOfModules.unit twoAdic)).map
    (homOfLE (show 1 ≤ 3 by omega)).op).hom (ULift.up.{1} (6 : ZMod (2 ^ 3)))) =
      (0 : ZMod (2 ^ 1)) := by
  change ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ 1)) (ZMod (2 ^ 1))
    (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ 2)) (ZMod (2 ^ 2)) (6 : ZMod (2 ^ 3))) = 0
  decide +kernel

/-- The ring action is transported along the restriction: `3 • 3 = 9` in `ℤ/8` restricts to
`1 • 1 = 1` in `ℤ/2`. -/
example : ULift.down (((obj twoAdic (PresheafOfModules.unit twoAdic)).map
    (homOfLE (show 1 ≤ 3 by omega)).op).hom
      ((3 : ZMod (2 ^ 3)) • ULift.up.{1} (3 : ZMod (2 ^ 3)))) = (1 : ZMod (2 ^ 1)) := by
  change ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ 1)) (ZMod (2 ^ 1))
    (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ 2)) (ZMod (2 ^ 2))
      ((3 : ZMod (2 ^ 3)) * (3 : ZMod (2 ^ 3)))) = 1
  decide +kernel

end TwoAdic

end MathlibExtTest.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
