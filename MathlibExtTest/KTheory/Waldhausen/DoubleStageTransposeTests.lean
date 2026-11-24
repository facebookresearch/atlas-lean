/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageTranspose

/-!
# Original double-stage inverse, genuine corner and given cocone clients
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

universe u v

namespace MathlibExtTest.KTheory.Waldhausen.DoubleStageTranspose

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Both original equivalence functors have their earned named exactness. -/
private theorem bothOriginalExact (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject (Stage C n) m;
    letI := generalStageWaldhausenCategory (Stage C n) m;
    letI := generalStageHasZeroObject (Stage C m) n;
    letI := generalStageWaldhausenCategory (Stage C m) n;
    (doubleStageTransposeEquivalence C m n).functor.IsWaldhausenExact ∧
      (doubleStageTransposeEquivalence C m n).inverse.IsWaldhausenExact := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  let := generalStageHasZeroObject (Stage C m) n
  let := generalStageWaldhausenCategory (Stage C m) n
  exact ⟨doubleStageTransposeFunctor_isWaldhausenExact C m n,
    doubleStageTransposeEquivalence_inverse_isWaldhausenExact C m n⟩

/-- Arbitrary original zero objects are preserved in both directions. -/
private theorem arbitraryZeroBoth (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject (Stage C n) m;
    letI := generalStageWaldhausenCategory (Stage C n) m;
    letI := generalStageHasZeroObject (Stage C m) n;
    letI := generalStageWaldhausenCategory (Stage C m) n;
    (∀ {A : Stage (Stage C n) m}, IsZero A →
      IsZero ((doubleStageTransposeEquivalence C m n).functor.obj A)) ∧
    (∀ {A : Stage (Stage C m) n}, IsZero A →
      IsZero ((doubleStageTransposeEquivalence C m n).inverse.obj A)) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  let := generalStageHasZeroObject (Stage C m) n
  let := generalStageWaldhausenCategory (Stage C m) n
  exact ⟨(doubleStageTransposeFunctor_isWaldhausenExact C m n).map_isZero,
    (doubleStageTransposeEquivalence_inverse_isWaldhausenExact C m n).map_isZero⟩

/-- Every supplied original cocone retains the forward mapped original apex and legs. -/
private theorem everyGivenPushoutForward (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject (Stage C n) m;
    letI := generalStageWaldhausenCategory (Stage C n) m;
    letI := generalStageHasZeroObject (Stage C m) n;
    letI := generalStageWaldhausenCategory (Stage C m) n;
    ∀ {A B A' P : Stage (Stage C n) m} (i : A ⟶ B) (f : A ⟶ A')
      (l : A' ⟶ P) (r : B ⟶ P) (_hi : IsCofibration i) (_hP : IsPushout f i l r),
      IsPushout ((doubleStageTransposeEquivalence C m n).functor.map f)
        ((doubleStageTransposeEquivalence C m n).functor.map i)
        ((doubleStageTransposeEquivalence C m n).functor.map l)
        ((doubleStageTransposeEquivalence C m n).functor.map r) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  let := generalStageHasZeroObject (Stage C m) n
  let := generalStageWaldhausenCategory (Stage C m) n
  intro A B A' P i f l r hi hP
  exact (doubleStageTransposeFunctor_isWaldhausenExact C m n).map_pushout i f l r hi hP

/-- Every supplied original cocone retains the inverse mapped original apex and legs. -/
private theorem everyGivenPushoutInverse (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject (Stage C n) m;
    letI := generalStageWaldhausenCategory (Stage C n) m;
    letI := generalStageHasZeroObject (Stage C m) n;
    letI := generalStageWaldhausenCategory (Stage C m) n;
    ∀ {A B A' P : Stage (Stage C m) n} (i : A ⟶ B) (f : A ⟶ A')
      (l : A' ⟶ P) (r : B ⟶ P) (_hi : IsCofibration i) (_hP : IsPushout f i l r),
      IsPushout ((doubleStageTransposeEquivalence C m n).inverse.map f)
        ((doubleStageTransposeEquivalence C m n).inverse.map i)
        ((doubleStageTransposeEquivalence C m n).inverse.map l)
        ((doubleStageTransposeEquivalence C m n).inverse.map r) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  let := generalStageHasZeroObject (Stage C m) n
  let := generalStageWaldhausenCategory (Stage C m) n
  intro A B A' P i f l r hi hP
  exact (doubleStageTransposeEquivalence_inverse_isWaldhausenExact C m n).map_pushout
    i f l r hi hP

/-- The actual genuine corner predicate is reflected and preserved on the original morphism. -/
private theorem genuineOriginalCorner (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B),
      stageCofibrations (Stage C m) n ((doubleStageTransposeFunctor C m n).map φ) ↔
        stageCofibrations (Stage C n) m φ := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ
  exact doubleStageTransposeFunctor_stageCofibrations_iff C m n φ

/-- The original pointwise weak predicate is reflected and preserved. -/
private theorem originalWeakPredicate (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B),
      stageWeak (Stage C m) n ((doubleStageTransposeFunctor C m n).map φ) ↔
        stageWeak (Stage C n) m φ := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ
  exact doubleStageTransposeFunctor_stageWeak_iff C m n φ

/-- The whole original inclusion, quotient arrow and apex remain a cofiber row. -/
private theorem wholeOriginalCofiberRow (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject (Stage C n) m;
    letI := generalStageWaldhausenCategory (Stage C n) m;
    letI := generalStageHasZeroObject (Stage C m) n;
    letI := generalStageWaldhausenCategory (Stage C m) n;
    ∀ {A B Q : Stage (Stage C n) m} (i : A ⟶ B) (p : B ⟶ Q)
      (_hSeq : IsCofibrationSequence i p),
      IsCofibrationSequence ((doubleStageTransposeEquivalence C m n).functor.map i)
        ((doubleStageTransposeEquivalence C m n).functor.map p) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  let := generalStageHasZeroObject (Stage C m) n
  let := generalStageWaldhausenCategory (Stage C m) n
  intro A B Q i p hSeq
  exact (doubleStageTransposeFunctor_isWaldhausenExact C m n).map_cofibrationSequence hSeq

/-- Both whole original inverse composites equal the original identity functor. -/
private theorem wholeOriginalInverseComposites (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    doubleStageTransposeFunctor C m n ⋙ doubleStageTransposeFunctor C n m =
        𝟭 (Stage (Stage C n) m) ∧
      doubleStageTransposeFunctor C n m ⋙ doubleStageTransposeFunctor C m n =
        𝟭 (Stage (Stage C m) n) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  exact ⟨doubleStageTransposeFunctor_involution C m n,
    doubleStageTransposeFunctor_involution C n m⟩

/-- The actual unit and counit are identity families on the original whole double stages. -/
private theorem originalUnitCounitFamilies (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    (∀ A : Stage (Stage C n) m,
      (doubleStageTransposeEquivalence C m n).unitIso.hom.app A = 𝟙 A) ∧
    (∀ A : Stage (Stage C m) n,
      (doubleStageTransposeEquivalence C m n).counitIso.hom.app A = 𝟙 A) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  exact ⟨doubleStageTransposeEquivalence_unitIso_hom_app C m n,
    doubleStageTransposeEquivalence_counitIso_hom_app C m n⟩

/-- Both diagram directions and every mapped morphism retain the original coefficients. -/
private theorem originalMapDictionary (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B)
      {x x' : Ar n} (f : x ⟶ x') {y y' : Ar m} (g : y ⟶ y'),
      (((doubleStageTransposeFunctor C m n).obj A).obj.obj x).obj.map g =
          (A.obj.map g).hom.app x ∧
      (((doubleStageTransposeFunctor C m n).obj A).obj.map f).hom.app y =
          (A.obj.obj y).obj.map f ∧
      (((doubleStageTransposeFunctor C m n).map φ).hom.app x).hom.app y =
          (φ.hom.app y).hom.app x := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ x x' f y y' g
  exact ⟨doubleStageTransposeFunctor_obj_innerMap C m n A x g,
    doubleStageTransposeFunctor_obj_outerMap C m n A f y,
    doubleStageTransposeFunctor_map_cell C m n φ x y⟩

#print axioms
  CategoryTheory.Waldhausen.SConstruction.doubleStageTransposeFunctor_isWaldhausenExact
#print axioms
  CategoryTheory.Waldhausen.SConstruction.doubleStageTransposeEquivalence_inverse_isWaldhausenExact

end MathlibExtTest.KTheory.Waldhausen.DoubleStageTranspose

end
