/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped MonoidalClosed

set_option autoImplicit false

noncomputable section

universe uC uV vV

namespace MathlibExtTest.CoYonedaBalanceTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  (F : EnrichedFunctor V C V) (c a b : C)

-- The genuine cocone relation is available with a plain index and no colimit.
example :
    ((α_ (b ⟶[V] c) (a ⟶[V] b) (F.obj a)).inv ≫
        (((β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫ eComp V a b c) ⊗ₘ
          𝟙 (F.obj a))) ≫
        (β_ (a ⟶[V] c) (F.obj a)).hom ≫
        MonoidalClosed.uncurry (F.map a c) =
      (b ⟶[V] c) ◁
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b)) ≫
        (β_ (b ⟶[V] c) (F.obj b)).hom ≫
          MonoidalClosed.uncurry (F.map b c) :=
  Enriched.weightedCoend.coyonedaCondition F c a b

-- A consumer may pull the full relation back along an arbitrary V-hom map.
example {P : V} (t : P ⟶ (a ⟶[V] b)) :
    ((b ⟶[V] c) ◁ (t ⊗ₘ 𝟙 (F.obj a))) ≫
      (((α_ (b ⟶[V] c) (a ⟶[V] b) (F.obj a)).inv ≫
          (((β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫ eComp V a b c) ⊗ₘ
            𝟙 (F.obj a))) ≫
          (β_ (a ⟶[V] c) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a c)) =
      ((b ⟶[V] c) ◁ (t ⊗ₘ 𝟙 (F.obj a))) ≫
        ((b ⟶[V] c) ◁
            ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
              MonoidalClosed.uncurry (F.map a b)) ≫
          (β_ (b ⟶[V] c) (F.obj b)).hom ≫
            MonoidalClosed.uncurry (F.map b c)) :=
  congrArg (fun v => ((b ⟶[V] c) ◁ (t ⊗ₘ 𝟙 (F.obj a))) ≫ v)
    (Enriched.weightedCoend.coyonedaCondition F c a b)

end MathlibExtTest.CoYonedaBalanceTests
