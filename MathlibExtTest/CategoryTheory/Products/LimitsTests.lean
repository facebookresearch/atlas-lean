/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Products.Limits

/-!
# Consumer checks for Preadditive-free product limits

Scope: pins the canonical product zero instance and the componentwise
zero/pushout/pullback iff's from `Products.Limits`, using independent
universes with no `Preadditive`, `ExactCategory`, or Waldhausen
assumptions, so an over-constrained source fails here.

Nonclaims: no exact or Waldhausen wrappers, no biproducts, no additivity,
no K/G-theory, no realization or spectra.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace MathlibExtTest.CategoryTheory.Products.LimitsTests

variable (C : Type u₁) [Category.{v₁} C] [HasZeroObject C]
variable (D : Type u₂) [Category.{v₂} D] [HasZeroObject D]

/-- Product zero object is inferred from the component zeros. -/
example : HasZeroObject (C × D) := inferInstance

/-- Two-direction zero correspondence for the product. -/
example (X : C × D) : IsZero X ↔ IsZero X.1 ∧ IsZero X.2 :=
  isZero_prod_iff C D

/-- Forward pushout projection: product pushout gives both components. -/
example {Z X Y P : C × D} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) :
    IsPushout f.1 g.1 inl.1 inr.1 ∧ IsPushout f.2 g.2 inl.2 inr.2 :=
  (isPushout_prod_iff C D).mp h

/-- Backward pushout combination over arbitrary legs. -/
example {Z X Y P : C × D} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P}
    (hC : IsPushout f.1 g.1 inl.1 inr.1)
    (hD : IsPushout f.2 g.2 inl.2 inr.2) : IsPushout f g inl inr :=
  (isPushout_prod_iff C D).mpr ⟨hC, hD⟩

/-- Two-direction pullback correspondence for the product. -/
example {X Y Z P : C × D} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst : P ⟶ X} {snd : P ⟶ Y} :
    IsPullback fst snd f g ↔
      IsPullback fst.1 snd.1 f.1 g.1 ∧ IsPullback fst.2 snd.2 f.2 g.2 :=
  isPullback_prod_iff C D

end MathlibExtTest.CategoryTheory.Products.LimitsTests
