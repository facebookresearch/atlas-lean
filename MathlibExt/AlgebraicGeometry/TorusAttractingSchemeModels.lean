/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusFixedSchemeModels
public import MathlibExt.AlgebraicGeometry.AlgebraicWeightBundleModels
public import MathlibExt.AlgebraicGeometry.ThetaQuotientSources

/-!
# Actual one-parameter attracting families and evaluations

A family is an algebraic map T times A1 to X, equivariant for the
actual one-parameter subgroup, and extending its literal orbit on
T times Gm. Its evaluations are the original maps at zero and one.
Fixed limits factor through the all-scheme fixed-point functor.
Representations and their image/support constructions are separate
source-normalized construction requests.

Reference: Maulik--Okounkov 1211.1287v3, Sections3.1--3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusAttractingSchemeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open TorusFixedSchemeModels AlgebraicWeightBundleModels ThetaQuotientSources

abbrev Line := affineLine ℂ

/-- Zero and one are actual polynomial evaluation maps. -/
def linePoint (z : ℂ) : 𝟙_ (Over base) ⟶ Line :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom z))) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have he : (Polynomial.evalRingHom z).comp (algebraMap ℂ (Polynomial ℂ)) = RingHom.id ℂ := by
      ext c
      simp
    simpa only [he, CommRingCat.ofHom_id] using Spec.map_id (.of ℂ))

/-- The puncture is the native polynomial-to-Laurent localization map. -/
def puncture : Gm ⟶ Line :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := ℂ)))) (by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    ext c
    simp)

def parameterPoint (T : Over base) (z : ℂ) : T ⟶ T ⊗ Line :=
  CartesianMonoidalCategory.lift (𝟙 T) (toUnit T ≫ linePoint z)

variable [ContractingAction ℂ]

/-- This is the actual coefficient-preserving scalar action on T times A1. -/
def parameterActionMap (T : Over base) : Gm ⊗ (T ⊗ Line) ⟶ T ⊗ Line :=
  CartesianMonoidalCategory.lift (snd Gm (T ⊗ Line) ≫ fst T Line)
    ((Gm ◁ snd T Line) ≫ γ[Gm,Line])

variable (A : Over base) [GrpObj A] (X : Over base) [ModObj A X]
  (lambda : Gm ⟶ A) [IsMonHom lambda]

def oneParameterAction : Gm ⊗ X ⟶ X := (lambda ▷ X) ≫ γ[A,X]

def atZero {T : Over base} (f : T ⊗ Line ⟶ X) : T ⟶ X := parameterPoint T 0 ≫ f
def atOne {T : Over base} (f : T ⊗ Line ⟶ X) : T ⟶ X := parameterPoint T 1 ≫ f

/-- Full equivariance and the native punctured-orbit equation on every scheme. -/
structure AttractingFamily (T : Over base) where
  map : T ⊗ Line ⟶ X
  equivariant : parameterActionMap T ≫ map = (Gm ◁ map) ≫ oneParameterAction A X lambda
  orbit : tensorHom (𝟙 T) puncture ≫ map =
    CartesianMonoidalCategory.lift (snd T Gm ≫ lambda) (fst T Gm ≫ atOne X map) ≫ γ[A,X]
  fixed : FixedPoint A X (atZero X map)

/-- A represented attracting scheme is fixed on all actual test maps and both evaluations. -/
structure AttractingScheme (F : FixedSchemeModel A X) where
  scheme : Over base
  families : ∀ T : Over base, (T ⟶ scheme) ≃ AttractingFamily A X lambda T
  naturality : ∀ {T U : Over base} (f : U ⟶ T) (g : T ⟶ scheme),
    (families U (f ≫ g)).map = tensorHom f (𝟙 Line) ≫ (families T g).map
  evalOne : scheme ⟶ X
  evalOne_formula : ∀ (T : Over base) (g : T ⟶ scheme),
    g ≫ evalOne = atOne X (families T g).map
  evalZero : scheme ⟶ F.scheme
  evalZero_formula : ∀ (T : Over base) (g : T ⟶ scheme),
    g ≫ evalZero ≫ F.inclusion = atZero X (families T g).map

/-- The component attracting correspondence is the literal scheme fibre of eval0. -/
def componentAttractor {F : FixedSchemeModel A X} (R : AttractingScheme A X lambda F)
    (Z : FixedComponent A X F) : Over base :=
  Over.mk (pullback.fst R.evalZero.left Z.inclusion.left ≫ R.scheme.hom)

/-- Its map to X is the actual first projection followed by eval1. -/
def componentEvaluation {F : FixedSchemeModel A X} (R : AttractingScheme A X lambda F)
    (Z : FixedComponent A X F) : (componentAttractor A X lambda R Z).left ⟶ X.left :=
  pullback.fst R.evalZero.left Z.inclusion.left ≫ R.evalOne.left

end MathlibExt.AlgebraicGeometry.TorusAttractingSchemeModels
