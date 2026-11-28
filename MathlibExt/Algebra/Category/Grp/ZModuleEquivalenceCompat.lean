/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

-- BACKPORT: Selected definitions from Mathlib PR #42860 head
`4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
-- path `Mathlib/Algebra/Category/Grp/ZModuleEquivalence.lean`,
-- blob `928458bb9acc91aebac4211cfefb0dc1efa8b298`, authors Junyan Xu.
-- See `BACKPORTS.md` for copied surface, adaptations, and upgrade-removal steps.

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# Equivalence of integer modules and abelian groups

For a fixed universe, forgetting the integer action gives an equivalence
from `ModuleCat ℤ` to `Ab`. The inverse equips every abelian group with
its unique integer module action; the underlying additive maps are unchanged.
-/

public section

open CategoryTheory

universe u

namespace ModuleCat

/-- The forgetful functor from integer modules in universe `u` to
abelian groups in that universe is an equivalence
`ModuleCat.{u} ℤ ≌ Ab.{u}`. Its inverse supplies the unique integer
module structure on each abelian group. -/
@[implicit_reducible, expose, simps functor inverse]
def intEquivalence : ModuleCat.{u} ℤ ≌ Ab.{u} where
  functor := forget₂ ..
  inverse.obj G := of ℤ G
  inverse.map f := ofHom f.hom.toIntLinearMap
  unitIso := NatIso.ofComponents
    (fun G ↦ (AddEquiv.toIntLinearEquiv { __ := Equiv.refl G, map_add' _ _ := rfl }).toModuleIso)
    fun _ ↦ rfl
  counitIso := .refl _

end ModuleCat

end
