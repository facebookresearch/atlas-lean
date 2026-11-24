/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

import MathlibExt.CategoryTheory.ExactCategory.Bicartesian

/-!
# Exact-category bicartesian tests

These tests consume the pullback theorem, its pushout dual, and the
admissible-middle corollary in generic exact categories, with no balanced or
abelian hypothesis. They pin both square orientations, the identity
boundaries, independent category universes, and the absence of any opposite
exact-category instance introduced by this API.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.ExactCategory.BicartesianTests

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The generic adapter converts exactness of the square short complex into
the pushout property. -/
noncomputable example
    {X₁ X₂ X₃ X₄ : C}
    {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃}
    {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄}
    (sq : CommSq f g inl inr)
    (h : IsAdmissibleExact sq.shortComplex) :
    IsPushout f g inl inr :=
  isPushout_of_isAdmissibleExact_shortComplex sq h

/-- The generic adapter converts exactness of the square short complex into
the pullback property. -/
noncomputable example
    {X₁ X₂ X₃ X₄ : C}
    {fst : X₁ ⟶ X₂} {snd : X₁ ⟶ X₃}
    {f : X₂ ⟶ X₄} {g : X₃ ⟶ X₄}
    (sq : CommSq fst snd f g)
    (h : IsAdmissibleExact sq.shortComplex') :
    IsPullback fst snd f g :=
  isPullback_of_isAdmissibleExact_shortComplex' sq h

/-- An isomorphism on the left of a morphism of conflations gives the
pullback square on the final two terms. -/
example {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₁] :
    IsPullback S.g φ.τ₂ φ.τ₃ T.g :=
  isPullback_g_of_isAdmissibleExact_of_isIso_left φ hS hT

/-- The resulting square has the reviewed orientation. -/
example {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₁] :
    S.g ≫ φ.τ₃ = φ.τ₂ ≫ T.g :=
  (isPullback_g_of_isAdmissibleExact_of_isIso_left φ hS hT).w

/-- If the right component is an admissible mono, so is the middle one. -/
example {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₁] (h₃ : IsAdmissibleMono φ.τ₃) :
    IsAdmissibleMono φ.τ₂ :=
  isAdmissibleMono_middle_of_isIso_left φ hS hT h₃

/-- An isomorphism on the right of a morphism of conflations gives the
pushout square on the first two terms. -/
example {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₃] :
    IsPushout S.f φ.τ₁ φ.τ₂ T.f :=
  isPushout_f_of_isAdmissibleExact_of_isIso_right φ hS hT

/-- The pushout square has the source-first orientation of `φ.comm₁₂`. -/
example {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₃] :
    S.f ≫ φ.τ₂ = φ.τ₁ ≫ T.f :=
  (isPushout_f_of_isAdmissibleExact_of_isIso_right φ hS hT).w

/-- The identity morphism yields the identity pullback boundary. -/
example {S : ShortComplex C} (hS : IsAdmissibleExact S) :
    IsPullback S.g (𝟙 S.X₂) (𝟙 S.X₃) S.g := by
  simpa using
    (isPullback_g_of_isAdmissibleExact_of_isIso_left (𝟙 S) hS hS)

/-- The identity morphism also yields the identity pushout boundary. -/
example {S : ShortComplex C} (hS : IsAdmissibleExact S) :
    IsPushout S.f (𝟙 S.X₁) (𝟙 S.X₂) S.f := by
  simpa using
    (isPushout_f_of_isAdmissibleExact_of_isIso_right (𝟙 S) hS hS)

section IndependentUniverse

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- A second, independently quantified category universe consumes the same
right-isomorphism theorem. -/
example {S T : ShortComplex D} (φ : S ⟶ T)
    (hS : IsAdmissibleExact S) (hT : IsAdmissibleExact T)
    [IsIso φ.τ₃] :
    IsPushout S.f φ.τ₁ φ.τ₂ T.f :=
  isPushout_f_of_isAdmissibleExact_of_isIso_right φ hS hT

end IndependentUniverse

section Nonclaims

#guard_msgs (error, substring := true) in
#synth ExactCategory Cᵒᵖ

end Nonclaims

#print axioms isPushout_of_isAdmissibleExact_shortComplex
#print axioms isPushout_f_of_isAdmissibleExact_of_isIso_right

end MathlibExtTest.CategoryTheory.ExactCategory.BicartesianTests
