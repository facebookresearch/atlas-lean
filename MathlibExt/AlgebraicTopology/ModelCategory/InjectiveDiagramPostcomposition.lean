/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Postcomposition preserves the two global injective right classes

Base Quillen preservation gives the literal strict images of the objectwise
left classes. Native right-orthogonal antitonicity and the existing adjunction
strict-image identity transfer both whole natural right classes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uK vK uC vC uD vD

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace CategoryTheory.Adjunction

variable (K : Type uK) [Category.{vK} K]
  {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  [ModelCategory C] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- Postcomposition by the same right adjoint preserves the global right
orthogonals of both objectwise left classes, for every original index K. -/
theorem injectiveDiagram_rightClasses_le_inverseImage
    (adj : L ⊣ R) [h : adj.IsQuillenAdjunction] :
    (((trivialCofibrations D).functorCategory K).rlp ≤
      (((trivialCofibrations C).functorCategory K).rlp).inverseImage
        ((Functor.whiskeringRight K D C).obj R)) ∧
    (((cofibrations D).functorCategory K).rlp ≤
      (((cofibrations C).functorCategory K).rlp).inverseImage
        ((Functor.whiskeringRight K D C).obj R)) := by
  constructor
  · have hImage : ((trivialCofibrations C).functorCategory K).strictMap
        ((Functor.whiskeringRight K C D).obj L) ≤
        (trivialCofibrations D).functorCategory K := by
      rw [strictMap_le_iff_le_inverseImage]
      intro X Y i hi k
      exact h.preservesTrivialCofibrations _ (hi k)
    rw [← strictMap_rlp_eq_inverseImage_rlp
      ((trivialCofibrations C).functorCategory K)
      ((Functor.whiskeringRight K C D).obj L)
      ((Functor.whiskeringRight K D C).obj R) (adj.whiskerRight K)]
    exact antitone_rlp hImage
  · have hImage : ((cofibrations C).functorCategory K).strictMap
        ((Functor.whiskeringRight K C D).obj L) ≤
        (cofibrations D).functorCategory K := by
      rw [strictMap_le_iff_le_inverseImage]
      intro X Y i hi k
      exact h.preservesCofibrations _ (hi k)
    rw [← strictMap_rlp_eq_inverseImage_rlp
      ((cofibrations C).functorCategory K)
      ((Functor.whiskeringRight K C D).obj L)
      ((Functor.whiskeringRight K D C).obj R) (adj.whiskerRight K)]
    exact antitone_rlp hImage

end CategoryTheory.Adjunction
