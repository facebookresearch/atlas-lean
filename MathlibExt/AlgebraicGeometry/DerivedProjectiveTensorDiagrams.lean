/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
public import MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels

/-!
# Full source tensor diagrams and the derived projection-formula class

Both tensor factors and all their actual diagram arrows are retained.
Every map is fixed by the literal homogeneous tensor map. The derived
projection formula is computed from the actual form and coefficient
cones, through their actual weak augmentation maps, before the native
mixed-diagram limit. This keeps nonflat coefficients out of an
unjustified ordinary tensor comparison.

Reference: PTVV arXiv:1111.3209v4, §2.1, pp.30–32.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedProjectiveTensorDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels

universe u
variable {k : Type u} [CommRing k] {J : Type (u + 1)} [Category.{u} J]

/-- Tensor diagrams fix both source functors and every weightwise tensor map. -/
structure TensorMixedDiagram (F : J ⥤ GradedMixed (LargeScalar k))
    (C : J ⥤ Cochains (LargeScalar k)) where
  diagram : J ⥤ GradedMixed (LargeScalar k)
  model : ∀ j, PureTensorModel (F.obj j) (C.obj j)
  object : ∀ j, diagram.obj j = (model j).mixed
  map : ∀ (j l : J) (f : j ⟶ l) (w : ℤ),
    (diagram.map f).map w ≫ (pureWeightComparison (diagram.obj l) (model l) (object l) w).hom =
      (pureWeightComparison (diagram.obj j) (model j) (object j) w).hom ≫
        ((F.map f).map w ⊗ₘ C.map f)

/-- Native tensor natural transformations retain both complete source maps. -/
structure TensorDiagramMap {F F' : J ⥤ GradedMixed (LargeScalar k)}
    {C C' : J ⥤ Cochains (LargeScalar k)} (f : F ⟶ F') (c : C ⟶ C')
    (P : TensorMixedDiagram F C) (P' : TensorMixedDiagram F' C') where
  map : P.diagram ⟶ P'.diagram
  normalized : ∀ (j : J) (w : ℤ),
    (map.app j).map w ≫ (pureWeightComparison (P'.diagram.obj j) (P'.model j) (P'.object j) w).hom =
      (pureWeightComparison (P.diagram.obj j) (P.model j) (P.object j) w).hom ≫
        ((f.app j).map w ⊗ₘ c.app j)

/-- Constant tensor data use exactly the specified native pure-tensor model. -/
def constantTensor {E : GradedMixed (LargeScalar k)} {C : Cochains (LargeScalar k)}
    (P : PureTensorModel E C) :
    TensorMixedDiagram ((Functor.const J).obj E) ((Functor.const J).obj C) where
  diagram := (Functor.const J).obj P.mixed
  model _ := P
  object _ := rfl
  map j l f w := by
    change 𝟙 (P.mixed.weight w) ≫ (pureWeightComparison P.mixed P rfl w).hom =
      (pureWeightComparison P.mixed P rfl w).hom ≫ (𝟙 (E.weight w) ⊗ₘ 𝟙 C)
    simp

/-- The actual projective tensor square uses form and coefficient augmentation maps,
and the two genuine cones. Only those normalized tensor maps enter its class. -/
structure ProjectionFormulaDiagram {F₀ F₁ : J ⥤ GradedMixed (LargeScalar k)}
    {C₀ C₁ : J ⥤ Cochains (LargeScalar k)} {E : GradedMixed (LargeScalar k)}
    {C : Cochains (LargeScalar k)}
    (f : F₀ ⟶ F₁) (c : C₀ ⟶ C₁)
    (formCone : (Functor.const J).obj E ⟶ F₁)
    (coefficientCone : (Functor.const J).obj C ⟶ C₁)
    (P : PureTensorModel E C) where
  raw : TensorMixedDiagram F₀ C₀
  coefficientResolved : TensorMixedDiagram F₀ C₁
  constantCoefficient : TensorMixedDiagram F₀ ((Functor.const J).obj C)
  formResolved : TensorMixedDiagram F₁ ((Functor.const J).obj C)
  coneMap : TensorDiagramMap formCone (𝟙 _) (constantTensor P) formResolved
  formAugmentation : TensorDiagramMap f (𝟙 _) constantCoefficient formResolved
  coefficientConeMap : TensorDiagramMap (𝟙 _) coefficientCone constantCoefficient coefficientResolved
  coefficientAugmentation : TensorDiagramMap (𝟙 _) c raw coefficientResolved
  formWeak : ∀ (j : J) (w : ℤ), QuasiIso ((formAugmentation.map.app j).map w)
  coefficientWeak : ∀ (j : J) (w : ℤ), QuasiIso ((coefficientAugmentation.map.app j).map w)
  replacement : MixedDiagramReplacement raw.diagram

/-- The full projection-formula class is the native cone/tensor composite
through the actual two weak augmentations. -/
def projectionFormulaClass {F₀ F₁ : J ⥤ GradedMixed (LargeScalar k)}
    {C₀ C₁ : J ⥤ Cochains (LargeScalar k)} {E : GradedMixed (LargeScalar k)}
    {C : Cochains (LargeScalar k)} {f : F₀ ⟶ F₁} {c : C₀ ⟶ C₁}
    {formCone : (Functor.const J).obj E ⟶ F₁}
    {coefficientCone : (Functor.const J).obj C ⟶ C₁} {P : PureTensorModel E C}
    (B : ProjectionFormulaDiagram f c formCone coefficientCone P) :
    (mixedDiagramQ (LargeScalar k) J).obj ((Functor.const J).obj P.mixed) ⟶
      (mixedDiagramQ (LargeScalar k) J).obj B.replacement.diagram := by
  letI := (mixedDiagramWeakEquivalences (LargeScalar k) J).Q_inverts
    B.formAugmentation.map B.formWeak
  letI := (mixedDiagramWeakEquivalences (LargeScalar k) J).Q_inverts
    B.coefficientAugmentation.map B.coefficientWeak
  exact (mixedDiagramQ (LargeScalar k) J).map B.coneMap.map ≫
    inv ((mixedDiagramQ (LargeScalar k) J).map B.formAugmentation.map) ≫
    (mixedDiagramQ (LargeScalar k) J).map B.coefficientConeMap.map ≫
    inv ((mixedDiagramQ (LargeScalar k) J).map B.coefficientAugmentation.map) ≫
    (mixedDiagramQ (LargeScalar k) J).map B.replacement.augmentation

/-- A mixed limit retains every native weight limit and the whole mixed cone. -/
structure MixedLimitModel (D : J ⥤ GradedMixed (LargeScalar k)) where
  mixed : GradedMixed (LargeScalar k)
  weight : ∀ w : ℤ, mixed.weight w ≅ limit (D ⋙ weightFunctor w)
  cone : (Functor.const J).obj mixed ⟶ D
  normalized : ∀ (j : J) (w : ℤ),
    (cone.app j).map w = (weight w).hom ≫ limit.π (D ⋙ weightFunctor w) j

/-- The native mixed projection formula is fixed to its entire computed diagram class. -/
structure ProjectionFormulaRealization {F₀ F₁ : J ⥤ GradedMixed (LargeScalar k)}
    {C₀ C₁ : J ⥤ Cochains (LargeScalar k)} {E : GradedMixed (LargeScalar k)}
    {C : Cochains (LargeScalar k)} {f : F₀ ⟶ F₁} {c : C₀ ⟶ C₁}
    {formCone : (Functor.const J).obj E ⟶ F₁}
    {coefficientCone : (Functor.const J).obj C ⟶ C₁} {P : PureTensorModel E C}
    (B : ProjectionFormulaDiagram f c formCone coefficientCone P)
    (H : MixedLimitModel B.replacement.diagram) where
  map : MixedMap P.mixed H.mixed
  normalized : (mixedDiagramQ (LargeScalar k) J).map
    ((Functor.const J).map map ≫ H.cone) = projectionFormulaClass B

end MathlibExt.AlgebraicGeometry.DerivedProjectiveTensorDiagrams
