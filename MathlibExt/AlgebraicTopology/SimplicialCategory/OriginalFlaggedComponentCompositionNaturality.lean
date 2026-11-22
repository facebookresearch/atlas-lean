/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentConcatenation

/-!
# Original component composition under every source map

The SAME native pushout gluing commutes with the complete original input
map. Its component composition therefore retains the literal original
source map, all scalar flags and all three supplied vertex images.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace
open OriginalBead.TerminalFlag (coefficientObject)

private theorem object_same_data {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (N : Data) {i j : N.object.{u} ⟶ K}
    (hi₀ : SSet.yonedaEquiv (N.source ≫ i) = x)
    (hi₁ : SSet.yonedaEquiv (N.target ≫ i) = y)
    (hj₀ : SSet.yonedaEquiv (N.source ≫ j) = x)
    (hj₁ : SSet.yonedaEquiv (N.target ≫ j) = y)
    (c : (coefficientObject N.dimension).obj q)
    (hc : ∀ k ∈ N.joints, ULift.up.{u} k ∈ (c.obj 0).I) (h : i = j) :
    (Object.mk N i hi₀ hi₁ c hc : Object K x y q) = Object.mk N j hj₀ hj₁ c hc := by
  cases h
  rfl

/-- The SAME original whole input gluing retains every actual source-map image. -/
theorem sourceObject_concat {K L : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (f : K ⟶ L) (T : Object K x y q) (U : Object K y z q) :
    sourceObject f (concat T U) = concat (sourceObject f T) (sourceObject f U) := by
  apply object_same_data
  exact concatInput_naturality T.necklace U.necklace T.input U.input
    (concat_endpoint_eq T U) f

namespace Components

/-- EVERY full original component composition commutes with the SAME actual source simplicial map. -/
theorem concatenate_source {K L : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (f : K ⟶ L) (a : ConnectedComponents (Object K x y q))
    (b : ConnectedComponents (Object K y z q)) :
    (sourceMap f x z).app q (concatenate a b) =
      concatenate ((sourceMap f x y).app q a) ((sourceMap f y z).app q b) := by
  induction a using _root_.Quotient.inductionOn' with
  | h T =>
    induction b using _root_.Quotient.inductionOn' with
    | h U => exact congrArg ConnectedComponents.mk (sourceObject_concat f T U)

/-- The SAME full component-composition square retains all three original vertex images. -/
theorem composition_source {K L : SSet.{u}} (f : K ⟶ L) (x y z : K _⦋0⦌) :
    composition K x y z ≫ sourceMap f x z =
      (sourceMap f x y ⊗ₘ sourceMap f y z) ≫
        composition L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) (f.app (op ⦋0⦌) z) := by
  ext q ab
  obtain ⟨a, b⟩ := ab
  exact concatenate_source f a b

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
