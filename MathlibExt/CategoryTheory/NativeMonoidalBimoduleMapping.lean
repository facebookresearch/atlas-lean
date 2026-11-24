/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Full source normalization for monoidal mapping of native bimodules

The underlying object and every map are those of the original monoidal
functor. Both module actions are its original tensor comparison followed
by its map of the original action. This is the construction interface
used to apply beta to ordinary differential modules, retaining all ring
operators and the commuting outer action.

Source: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Monoidal/Functor and Bimod, Apache 2.0; DK1311.2374v2 Section 4.10.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe uC uD vC vD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (R S : Mon C)

def mappedRing (R : Mon C) : Mon D := F.mapMon.obj R

/-- Construction data fixes both actions and all underlying morphisms. -/
structure BimoduleMappingSource where
  functor : Bimod R S ⥤ Bimod (mappedRing F R) (mappedRing F S)
  underlying : functor ⋙ Bimod.forget (B := mappedRing F S) (mappedRing F R) ≅
    Bimod.forget (B := S) R ⋙ F
  leftAction : ∀ M : Bimod R S,
    (functor.obj M).actLeft ≫ underlying.hom.app M =
      ((mappedRing F R).X ◁ underlying.hom.app M) ≫
        Functor.LaxMonoidal.μ F R.X M.X ≫ F.map M.actLeft
  rightAction : ∀ M : Bimod R S,
    (functor.obj M).actRight ≫ underlying.hom.app M =
      (underlying.hom.app M ▷ (mappedRing F S).X) ≫
        Functor.LaxMonoidal.μ F M.X S.X ≫ F.map M.actRight

end MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
