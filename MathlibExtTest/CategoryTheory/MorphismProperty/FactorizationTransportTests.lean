/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.FactorArrowFunctors
import Mathlib.CategoryTheory.Types.Basic

/-!
# Explicit factorization transport, composition and roundtrip clients

The datum factors each function through its actual codomain. Its identity
equivalence is supplied explicitly, so these clients exercise the reusable
API independently of spectrum model constructions.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MorphismProperty
open CategoryTheory.MorphismProperty.FunctorialFactorizationData

namespace CategoryTheory.FactorizationTransportTests

/-- The explicit factorization sends a function to its codomain and identity. -/
def rightIdentityData :
    FunctorialFactorizationData (⊤ : MorphismProperty (Type u)) ⊤ where
  Z := Arrow.rightFunc
  i := Arrow.leftToRight
  p := 𝟙 Arrow.rightFunc
  fac := by simp
  hi _ := trivial
  hp _ := trivial

/-- A supplied equivalence of the small function category with itself. -/
def sourceEquivalence : Type u ≌ Type u := Equivalence.refl

example : rightIdentityData.Z = (Arrow.rightFunc : Arrow (Type u) ⥤ Type u) := rfl

example (a : Arrow (Type u)) :
    rightIdentityData.i.app a = a.hom ∧ rightIdentityData.p.app a = 𝟙 a.right := ⟨rfl, rfl⟩

example :
    FunctorialFactorizationData
      ((⊤ : MorphismProperty (Type u)).inverseImage sourceEquivalence.functor)
      ((⊤ : MorphismProperty (Type u)).inverseImage sourceEquivalence.functor) :=
  rightIdentityData.ofEquivalence sourceEquivalence

example (a : Arrow (Type u)) :
    (rightIdentityData.ofEquivalence sourceEquivalence).i.app a ≫
      (rightIdentityData.ofEquivalence sourceEquivalence).p.app a = a.hom :=
  rightIdentityData.ofEquivalence_fac_app sourceEquivalence a

example :
    ((rightIdentityData.ofEquivalence sourceEquivalence).ofEquivalence sourceEquivalence).Z =
      (rightIdentityData.ofEquivalence (sourceEquivalence.trans sourceEquivalence)).Z :=
  rightIdentityData.ofEquivalence_trans_Z sourceEquivalence sourceEquivalence

example (a : Arrow (Type u)) :
    ((rightIdentityData.ofEquivalence sourceEquivalence).ofEquivalence sourceEquivalence).i.app a =
      (rightIdentityData.ofEquivalence (sourceEquivalence.trans sourceEquivalence)).i.app a :=
  rightIdentityData.ofEquivalence_trans_i sourceEquivalence sourceEquivalence a

example (a : Arrow (Type u)) :
    ((rightIdentityData.ofEquivalence sourceEquivalence).ofEquivalence sourceEquivalence).p.app a =
      (rightIdentityData.ofEquivalence (sourceEquivalence.trans sourceEquivalence)).p.app a :=
  rightIdentityData.ofEquivalence_trans_p sourceEquivalence sourceEquivalence a

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    (sourceEquivalence.functor ⋙ sourceEquivalence.functor).map
        (((rightIdentityData.ofEquivalence sourceEquivalence).ofEquivalence
          sourceEquivalence).Z.map φ) ≫
      (rightIdentityData.ofEquivalenceTransComparisonIso
        sourceEquivalence sourceEquivalence).hom.app b =
      (rightIdentityData.ofEquivalenceTransComparisonIso
        sourceEquivalence sourceEquivalence).hom.app a ≫
        rightIdentityData.Z.map
          ((sourceEquivalence.functor ⋙ sourceEquivalence.functor).mapArrow.map φ) :=
  rightIdentityData.ofEquivalence_trans_naturality sourceEquivalence sourceEquivalence φ

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    rightIdentityData.Z.map
        ((sourceEquivalence.functor ⋙ sourceEquivalence.functor).mapArrow.map φ) ≫
      (rightIdentityData.ofEquivalenceTransComparisonIso
        sourceEquivalence sourceEquivalence).inv.app b =
      (rightIdentityData.ofEquivalenceTransComparisonIso
        sourceEquivalence sourceEquivalence).inv.app a ≫
        (sourceEquivalence.functor ⋙ sourceEquivalence.functor).map
          (((rightIdentityData.ofEquivalence sourceEquivalence).ofEquivalence
            sourceEquivalence).Z.map φ) :=
  rightIdentityData.ofEquivalence_trans_inverse_naturality sourceEquivalence sourceEquivalence φ

example (a : Arrow (Type u)) :
    ((rightIdentityData.ofEquivalence sourceEquivalence.symm).ofEquivalence
        sourceEquivalence).i.app a ≫
      (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).hom.app a =
        rightIdentityData.i.app a :=
  rightIdentityData.ofEquivalence_roundtrip_i sourceEquivalence a

example (a : Arrow (Type u)) :
    (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).hom.app a ≫
        rightIdentityData.p.app a =
      ((rightIdentityData.ofEquivalence sourceEquivalence.symm).ofEquivalence
        sourceEquivalence).p.app a :=
  rightIdentityData.ofEquivalence_roundtrip_p sourceEquivalence a

example (a : Arrow (Type u)) :
    rightIdentityData.i.app a ≫
        (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).inv.app a =
      ((rightIdentityData.ofEquivalence sourceEquivalence.symm).ofEquivalence
        sourceEquivalence).i.app a :=
  rightIdentityData.ofEquivalence_roundtrip_inverse_i sourceEquivalence a

example (a : Arrow (Type u)) :
    (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).inv.app a ≫
      ((rightIdentityData.ofEquivalence sourceEquivalence.symm).ofEquivalence
        sourceEquivalence).p.app a = rightIdentityData.p.app a :=
  rightIdentityData.ofEquivalence_roundtrip_inverse_p sourceEquivalence a

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    ((rightIdentityData.ofEquivalence sourceEquivalence.symm).ofEquivalence
        sourceEquivalence).Z.map φ ≫
      (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).hom.app b =
      (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).hom.app a ≫
        rightIdentityData.Z.map φ :=
  rightIdentityData.ofEquivalence_roundtrip_naturality sourceEquivalence φ

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    rightIdentityData.Z.map φ ≫
      (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).inv.app b =
      (rightIdentityData.ofEquivalenceRoundtripComparisonIso sourceEquivalence).inv.app a ≫
        ((rightIdentityData.ofEquivalence sourceEquivalence.symm).ofEquivalence
          sourceEquivalence).Z.map φ :=
  rightIdentityData.ofEquivalence_roundtrip_inverse_naturality sourceEquivalence φ

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    (rightIdentityData.originalLeftFactorFunctor.map φ).left = φ.left ∧
      (rightIdentityData.originalLeftFactorFunctor.map φ).right = rightIdentityData.Z.map φ :=
  rightIdentityData.originalLeftFactorFunctor_map_fields φ

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    (rightIdentityData.originalRightFactorFunctor.map φ).left = rightIdentityData.Z.map φ ∧
      (rightIdentityData.originalRightFactorFunctor.map φ).right = φ.right :=
  rightIdentityData.originalRightFactorFunctor_map_fields φ

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    ((rightIdentityData.ofEquivalence sourceEquivalence).originalLeftFactorFunctor ⋙
        sourceEquivalence.functor.mapArrow).map φ ≫
      (rightIdentityData.originalLeftFactorEquivalenceIso sourceEquivalence).hom.app b =
      (rightIdentityData.originalLeftFactorEquivalenceIso sourceEquivalence).hom.app a ≫
        (sourceEquivalence.functor.mapArrow ⋙ rightIdentityData.originalLeftFactorFunctor).map φ :=
  (rightIdentityData.originalLeftFactorEquivalenceIso sourceEquivalence).hom.naturality φ

example {a b : Arrow (Type u)} (φ : a ⟶ b) :
    (sourceEquivalence.functor.mapArrow ⋙ rightIdentityData.originalRightFactorFunctor).map φ ≫
      (rightIdentityData.originalRightFactorEquivalenceIso sourceEquivalence).inv.app b =
      (rightIdentityData.originalRightFactorEquivalenceIso sourceEquivalence).inv.app a ≫
        ((rightIdentityData.ofEquivalence sourceEquivalence).originalRightFactorFunctor ⋙
          sourceEquivalence.functor.mapArrow).map φ :=
  (rightIdentityData.originalRightFactorEquivalenceIso sourceEquivalence).inv.naturality φ

example (a : Arrow (Type u)) :
    (rightIdentityData.originalLeftFactorEquivalenceIso sourceEquivalence).hom.app a ≫
        (rightIdentityData.originalLeftFactorEquivalenceIso sourceEquivalence).inv.app a =
      𝟙 _ :=
  (rightIdentityData.originalLeftFactorEquivalenceIso sourceEquivalence).hom_inv_id_app a

example (a : Arrow (Type u)) :
    (rightIdentityData.originalRightFactorEquivalenceIso sourceEquivalence).inv.app a ≫
        (rightIdentityData.originalRightFactorEquivalenceIso sourceEquivalence).hom.app a =
      𝟙 _ :=
  (rightIdentityData.originalRightFactorEquivalenceIso sourceEquivalence).inv_hom_id_app a

end CategoryTheory.FactorizationTransportTests
