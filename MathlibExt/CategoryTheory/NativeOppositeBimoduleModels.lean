/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
# Original opposite ring and bimodule action normalization

The opposite ring retains the carrier/unit and reverses multiplication
by the original braiding. The bimodule conversion retains every original
object and map, and exchanges both actions using those same carrier and
braiding maps. This expresses right D modules as left opposite modules
without a top-form twist. The actual r-conversion is separate.

Source: native Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Monoidal/Mon and Bimod, Apache 2.0; DK1311.2374v2 Sections 2.5, 8.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeOppositeBimoduleModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

structure OppositeMonoidSource (R Rop : Mon C) where
  carrier : Rop.X ≅ R.X
  unit : η[Rop.X] ≫ carrier.hom = η[R.X]
  multiplication : μ[Rop.X] ≫ carrier.hom =
    (carrier.hom ⊗ₘ carrier.hom) ≫ (β_ R.X R.X).hom ≫ μ[R.X]

variable (R S Rop Sop : Mon C)
  (RO : OppositeMonoidSource R Rop) (SO : OppositeMonoidSource S Sop)

structure OppositeBimoduleSource where
  functor : Bimod R S ⥤ Bimod Sop Rop
  underlying : functor ⋙ Bimod.forget (B := Rop) Sop ≅ Bimod.forget (B := S) R
  leftAction : ∀ M : Bimod R S,
    (functor.obj M).actLeft ≫ underlying.hom.app M =
      (SO.carrier.hom ⊗ₘ underlying.hom.app M) ≫ (β_ S.X M.X).hom ≫ M.actRight
  rightAction : ∀ M : Bimod R S,
    (functor.obj M).actRight ≫ underlying.hom.app M =
      (underlying.hom.app M ⊗ₘ RO.carrier.hom) ≫ (β_ M.X R.X).hom ≫ M.actLeft

end MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
