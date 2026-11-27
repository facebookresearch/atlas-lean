/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendPoint

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uA

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.Enriched

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
  [HasCoproduct (weightedCoend.relations W F)]
  [HasCoproduct (weightedCoend.objects W F)]
  [HasCoequalizer (weightedCoend.leftMap W F) (weightedCoend.rightMap W F)]

-- Both full relation faces are checked at an arbitrary point, without an
-- ordinary category or enriched-ordinary comparison on the source A.
example (a b : A) (e : (𝟙_ V) ⟶ (a ⟶[V] b)) :
    (((ρ_ (W.obj (op b))).inv ≫ W.obj (op b) ◁ e ≫
        MonoidalClosed.uncurry (W.map (op b) (op a))) ⊗ₘ 𝟙 (F.obj a)) ≫
        weightedCoend.ι W F a =
      (𝟙 (W.obj (op b)) ⊗ₘ ((ρ_ (F.obj a)).inv ≫ F.obj a ◁ e ≫
        MonoidalClosed.uncurry (F.map a b))) ≫ weightedCoend.ι W F b :=
  CategoryTheory.Enriched.weightedCoend.condition_unitPoint W F a b e

end CategoryTheory.Enriched
