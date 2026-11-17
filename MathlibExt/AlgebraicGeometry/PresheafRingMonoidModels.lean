/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RingedComplexCoefficientModels
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# The original ring-sheaf presheaf as a normalized native monoid object

The underlying presheaf is the actual complex module of every original
ring-sheaf section, with its original restriction. A monoid source fixes
unit and multiplication on every section and pure tensor. Thus the
native Bimod carriers retain the full original ring actions.

Source: DK arXiv:1311.2374v2, Sections 4.10/5.2/8.2; native monoid,
presheaf and module tensor APIs: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PresheafRingMonoidModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open RingedComplexCoefficientModels

variable (X : TopCat.{0}) (R : TopCat.Sheaf RingCat.{0} X)
  [ComplexRingSheafSource X R]

local instance sectionAlgebra (U : (Opens X)ᵒᵖ) : Algebra ℂ (R.obj.obj U) :=
  ComplexRingSheafSource.algebra (X := X) (R := R) U.unop

abbrev CoefficientPresheaf := (Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ

/-- Every original ring restriction is linear over its prescribed complex constants. -/
def ringModulePresheaf : CoefficientPresheaf X where
  obj U := ModuleCat.of ℂ (R.obj.obj U)
  map {U V} f := ModuleCat.ofHom
    (X := ModuleCat.of ℂ (R.obj.obj U)) (Y := ModuleCat.of ℂ (R.obj.obj V))
    { toFun := (R.obj.map f).hom
      map_add' := (R.obj.map f).hom.map_add
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [map_mul]
        have hn := ComplexRingSheafSource.natural (X := X) (R := R) f.unop.le c
        change (R.obj.map f).hom (algebraMap ℂ (R.obj.obj U) c) =
          algebraMap ℂ (R.obj.obj V) c at hn
        exact congrArg (fun b => b * (R.obj.map f).hom a) hn }
  map_id U := by
    ext a
    change (R.obj.map (𝟙 U)).hom a = a
    rw [R.obj.map_id]
    rfl
  map_comp f g := by
    ext a
    change (R.obj.map (f ≫ g)).hom a = (R.obj.map g).hom ((R.obj.map f).hom a)
    rw [R.obj.map_comp]
    rfl

/-- Pointwise native monoid construction on this exact ring presheaf. -/
structure RingMonoidSource where
  [monoid : MonObj (ringModulePresheaf X R)]
  unitValue : ∀ (U : (Opens X)ᵒᵖ) (c : ℂ),
    (η[ringModulePresheaf X R]).app U c = algebraMap ℂ (R.obj.obj U) c
  multiplyValue : ∀ (U : (Opens X)ᵒᵖ) (a b : R.obj.obj U),
    (μ[ringModulePresheaf X R]).app U (a ⊗ₜ[ℂ] b) = a * b

/-- The ring monoid has the actual original section presheaf as carrier. -/
def ringMonoid (S : RingMonoidSource X R) : Mon (CoefficientPresheaf X) :=
  letI := S.monoid
  Mon.mk (ringModulePresheaf X R)

/-- The coefficient unit used by ordinary complex sheaf modules. -/
def coefficientUnit : Mon (CoefficientPresheaf X) := Mon.trivial (CoefficientPresheaf X)

end MathlibExt.AlgebraicGeometry.PresheafRingMonoidModels
