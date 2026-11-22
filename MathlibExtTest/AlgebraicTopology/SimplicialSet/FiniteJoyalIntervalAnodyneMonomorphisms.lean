/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneMonomorphisms
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Public use of auxiliary anodyne monicity

The monicity theorem supplies actual cancellation and injectivity in every
simplicial degree from an auxiliary anodyne membership witness.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite SSet.joyalInterval

universe u

namespace AuxiliaryAnodyneMonomorphismTest

variable {X Y Z : SSet.{u}} {f : X ⟶ Y}

/-- Auxiliary anodyne membership supplies the monomorphism for cancellation. -/
lemma cancel (hf : auxiliaryAnodyneExtensions f) (a b : Z ⟶ X)
    (h : a ≫ f = b ≫ f) : a = b := by
  have : Mono f := auxiliaryAnodyneExtensions.mono hf
  exact (cancel_mono f).1 h

/-- Every component of the actual simplicial map is injective. -/
lemma injective_components (hf : auxiliaryAnodyneExtensions f) (n : SimplexCategory) :
    Function.Injective (f.app (op n)) := by
  have : Mono f := auxiliaryAnodyneExtensions.mono hf
  exact injective_of_mono (f.app (op n))

end AuxiliaryAnodyneMonomorphismTest
