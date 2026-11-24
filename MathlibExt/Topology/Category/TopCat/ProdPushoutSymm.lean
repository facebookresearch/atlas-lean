/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace TopCat

/-!
# Fixed-right product-pushout symmetry adapter

Transports a supplied fixed-left product pushout square to the fixed-right
orientation via the four corner braidings. States no preservation result.
-/

/-- Fixed-right pushout square from a fixed-left pushout square. -/
theorem isPushout_prod_map_fixedRight_of_fixedLeft
    {Z X Y X' Y' : TopCat.{u}}
    {f : X ⟶ Y} {g : X ⟶ X'} {inl : Y ⟶ Y'} {inr : X' ⟶ Y'}
    (hL : IsPushout
      (prod.map (𝟙 Z) f) (prod.map (𝟙 Z) g)
      (prod.map (𝟙 Z) inl) (prod.map (𝟙 Z) inr)) :
    IsPushout
      (prod.map f (𝟙 Z)) (prod.map g (𝟙 Z))
      (prod.map inl (𝟙 Z)) (prod.map inr (𝟙 Z)) :=
  hL.of_iso
    (prod.braiding Z X) (prod.braiding Z Y)
    (prod.braiding Z X') (prod.braiding Z Y')
    (braid_natural (𝟙 Z) f) (braid_natural (𝟙 Z) g)
    (braid_natural (𝟙 Z) inl) (braid_natural (𝟙 Z) inr)

end TopCat
