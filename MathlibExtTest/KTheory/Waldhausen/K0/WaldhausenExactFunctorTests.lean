/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Waldhausen.K0.WaldhausenExactFunctor

/-!
# Tests for Waldhausen-exact functoriality of Waldhausen K0

The public generator, identity, and composition laws are consumed here.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace MathlibExtTest.KTheory.Waldhausen.K0.WaldhausenExactFunctorTests

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategory C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategory D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [WaldhausenCategory E]

example (F : C ⥤ D) (hF : F.IsWaldhausenExact) (X : C) :
    WaldhausenKTheory.K0.mapOfWaldhausenExact F hF
        (WaldhausenKTheory.K0.mk X) =
      WaldhausenKTheory.K0.mk (F.obj X) := by
  simp

example :
    WaldhausenKTheory.K0.mapOfWaldhausenExact
        (Functor.id C) Functor.IsWaldhausenExact.id =
      AddMonoidHom.id (WaldhausenKTheory.K0 C) := by
  simp

example (F : C ⥤ D) (G : D ⥤ E)
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    WaldhausenKTheory.K0.mapOfWaldhausenExact (F ⋙ G) (hF.comp hG) =
      (WaldhausenKTheory.K0.mapOfWaldhausenExact G hG).comp
        (WaldhausenKTheory.K0.mapOfWaldhausenExact F hF) :=
  WaldhausenKTheory.K0.mapOfWaldhausenExact_comp F G hF hG

end MathlibExtTest.KTheory.Waldhausen.K0.WaldhausenExactFunctorTests
