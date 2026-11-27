/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
public import MathlibExt.AlgebraicGeometry.DerivedTensorAffineFamilies
public import MathlibExt.Algebra.Homology.NegativeTensorNormalizations
public import MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Source normalized relative de Rham projection

The affine operation is the literal product-generator projection,
native normalized Alexander–Whitney, and generator-fixed tensor and
shift comparisons. A product cofibrant resolution is compared with
the actual Q(A⊗B), retaining its augmentation square. The derived
relative map is the inverse of that actual comparison followed by
the normalized projection. Every weight and every NC closing
coefficient remains part of the input.

Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30–32. Only the affine
Kunneth comparison is used; no global product de Rham equivalence
is asserted.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NormalizedRelativeDeRham

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicTopology
open CochainComplex.HomComplex
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.NegativeTensorNormalizations
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic

universe u
variable {k : Type u} [CommRing k]
attribute [local instance] HasDerivedCategory.standard

/-- The actual mixed realization of forms on the specified simplicial algebra. -/
structure RawDRModel (A : SAlg k) (M : SimplicialDRModel A) where
  graded : GradedMixed k
  weightIso : ∀ p : ℕ, graded.weight (p : ℤ) ≅ (normalizedForms M p)⟦(p : ℤ)⟧
  negative : ∀ w : ℤ, w < 0 → _root_.CategoryTheory.Limits.IsZero (graded.weight w)
  epsilon : ∀ (p : ℕ) (a b : ℤ) (h : a + (-1 : ℤ) = b),
    (graded.epsilon (p : ℤ)).v a b h ≫ eqToHom (by congr 2) ≫ (weightIso (p + 1)).hom.f b =
      (weightIso p).hom.f a ≫ mixedComponent M p a b h

/-- A source affine model has this same raw realization on its actual QA. -/
def rawOfAffine {Q : AlgebraReplacementFunctor k} {A : SAlg k}
    {M : SimplicialDRModel (Q.functor.obj A)} (D : AffineDRModel Q A M) :
    RawDRModel (Q.functor.obj A) M :=
  ⟨D.graded, D.weightIso, D.negative, D.epsilon_eq⟩

/-- Source algebra maps retain the literal normalized form map in every weight. -/
structure RawDRMap {A B : SAlg k} {M : SimplicialDRModel A} {N : SimplicialDRModel B}
    (D : RawDRModel A M) (E : RawDRModel B N) (f : A ⟶ B) (g : SimplicialDRMap M N f) where
  map : MixedMap D.graded E.graded
  normalized : ∀ p : ℕ,
    map.map (p : ℤ) ≫ (E.weightIso p).hom =
      (D.weightIso p).hom ≫ (shiftFunctor (Cochains k) (p : ℤ)).map (normalizedFormMap g p)

/-- Actual product resolutions, with their literal augmentation square. -/
structure ProductReplacement (Q : AlgebraReplacementFunctor k) (A B : SAlg k) where
  comparison : Q.functor.obj A ⊗ Q.functor.obj B ⟶ Q.functor.obj (A ⊗ B)
  square : comparison ≫ Q.augmentation.app (A ⊗ B) =
    Q.augmentation.app A ⊗ₘ Q.augmentation.app B
  cofibrant : IsAlgebraCofibrant (Q.functor.obj A ⊗ Q.functor.obj B)
  weak : AlgebraWeakEquivalence comparison

/-- The normalized product projection uses the native Moore map and native AW. -/
def projectedNormalization {A B : SAlg k} {M : SimplicialDRModel A}
    {P : SimplicialDRModel (A ⊗ B)} (F : ProjectionModel A B M P) (p : ℕ) :
    normalizedForms P p ⟶
      negativeExtension ((normalizedMooreComplex (ModuleCat.{u} k)).obj (M.forms p) ⊗
        (normalizedMooreComplex (ModuleCat.{u} k)).obj (coefficients B)) :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} k)).map
    (normalizedProjection F p ≫ normalizedAlexanderWhitney (M.forms p) (coefficients B))

/-- The coefficient cochain is the actual normalized underlying algebra of B. -/
def normalizedCoefficient (B : SAlg k) : Cochains k :=
  negativeExtension ((normalizedMooreComplex (ModuleCat.{u} k)).obj (coefficients B))

/-- The relative mixed map is fixed by the actual product-generator projection,
AW cuts, and every native tensor/shift generator. -/
structure RelativeDRModel {A B : SAlg k} {M : SimplicialDRModel A}
    {P : SimplicialDRModel (A ⊗ B)} (D : RawDRModel A M) (E : RawDRModel (A ⊗ B) P)
    (F : ProjectionModel A B M P) (T : PureTensorModel D.graded (normalizedCoefficient B)) where
  extension : ∀ p : ℕ, TensorExtensionModel
    ((normalizedMooreComplex (ModuleCat.{u} k)).obj (M.forms p))
    ((normalizedMooreComplex (ModuleCat.{u} k)).obj (coefficients B))
  shift : ∀ p : ℕ, LeftShiftTensorModel (normalizedForms M p) (normalizedCoefficient B) (p : ℤ)
  map : MixedMap E.graded T.mixed
  normalized : ∀ p : ℕ,
    map.map (p : ℤ) ≫ (T.weightIso (p : ℤ)).hom =
      (E.weightIso p).hom ≫ (shiftFunctor (Cochains k) (p : ℤ)).map (projectedNormalization F p) ≫
      (shiftFunctor (Cochains k) (p : ℤ)).map (extension p).comparison.hom ≫
      (shift p).comparison.hom ≫ ((D.weightIso p).inv ⊗ₘ 𝟙 (normalizedCoefficient B))

/-- The affine derived NC relative map is the inverse actual product comparison
followed by the actual normalized relative NC projection. -/
def affineKappa {A B : SAlg k} {M : SimplicialDRModel A} {P : SimplicialDRModel (A ⊗ B)}
    {C : SAlg k} {N : SimplicialDRModel C}
    {D : RawDRModel A M} {E : RawDRModel (A ⊗ B) P} {H : RawDRModel C N}
    {F : ProjectionModel A B M P} {T : PureTensorModel D.graded (normalizedCoefficient B)}
    (K : RelativeDRModel D E F T) {f : A ⊗ B ⟶ C} {g : SimplicialDRMap P N f}
    (J : RawDRMap E H f g) (p : ℤ)
    (NE : NegativeCyclicModel E.graded p) (NH : NegativeCyclicModel H.graded p)
    (NT : NegativeCyclicModel T.mixed p)
    (C₁ : CyclicMapModel J.map p NE NH) (C₂ : CyclicMapModel K.map p NE NT)
    [IsIso (DerivedCategory.Q.map C₁.map)] :
    DerivedCategory.Q.obj NH.complex ⟶ DerivedCategory.Q.obj NT.complex :=
  inv (DerivedCategory.Q.map C₁.map) ≫ DerivedCategory.Q.map C₂.map

end MathlibExt.AlgebraicGeometry.NormalizedRelativeDeRham
