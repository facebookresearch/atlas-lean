/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentIndependence
public import MathlibExt.CategoryTheory.Comma.Over.Diagram
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Natural derived cotangent comparison on polynomial resolutions

The bisimplicial polynomial cotangent replacement and its two augmentations are
functorial in augmented simplicial `k`-algebras over `A`. Diagonal normalization,
extension from chain degree `n` to cochain degree `-n`, and derived localization
preserve their natural maps.

Restrict to the full subcategory of augmentations with polynomial presentations in
every degree and with underlying simplicial-set augmentation a trivial fibration.
Both replacement augmentations become isomorphisms after derived localization, so
their span gives a natural isomorphism from the derived cotangent-model functor to
the constant canonical derived cotangent object. The derived-category universe is
independent of the ground-ring and module-carrier universes.

For cotangent resolutions and their functorial comparisons, see the Stacks Project,
§§92.4 and 92.6–92.7.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v w

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The functor assigning to an augmented simplicial algebra over `A` its bisimplicial
polynomial cotangent replacement, with maps induced in every degree.
-/
def polynomialCotangentReplacementFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      SimplicialObject (SimplicialObject (ModuleCat.{max u v} A)) :=
  Over.liftDiagramFunctor (J := SimplexCategoryᵒᵖ) A ⋙
    (SimplicialObject.whiskering (Over A) (SimplicialObject (ModuleCat.{max u v} A))).obj
      (polynomialCotangentSimplicialFunctor.{u, v} k A)

/--
The natural transformation from the polynomial cotangent replacement to the
cotangent diagram of the augmented algebra made constant in the inner direction.
-/
def polynomialCotangentReplacementVerticalNatTrans :
    polynomialCotangentReplacementFunctor.{u, v} k A ⟶
      cotangentSimplicialFunctor.{u, v} k A ⋙
        (SimplicialObject.whiskering (ModuleCat.{max u v} A)
          (SimplicialObject (ModuleCat.{max u v} A))).obj
            (SimplicialObject.const (ModuleCat.{max u v} A)) where
  app Q := polynomialCotangentReplacementVertical.{u, v} k A Q
  naturality {P Q} f := by
    apply NatTrans.ext
    funext q
    exact polynomialCotangentAugmentation_naturality k A
      ((Over.liftDiagramMap A f).app q)

/--
The natural transformation from the polynomial cotangent replacement to the fixed
canonical cotangent diagram of `A`, made constant in the outer direction.
-/
def polynomialCotangentReplacementHorizontalNatTrans :
    polynomialCotangentReplacementFunctor.{u, v} k A ⟶
      (Functor.const
        (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))).obj
          ((SimplicialObject.const (SimplicialObject (ModuleCat.{max u v} A))).obj
            ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A)))) where
  app Q := polynomialCotangentReplacementHorizontal.{u, v} k A Q
  naturality {P Q} f := by
    apply NatTrans.ext
    funext q
    let F := polynomialCotangentSimplicialFunctor.{u, v} k A
    let qP : (Over.lift P.left P.hom).obj q ⟶ Over.mk (𝟙 A) :=
      Over.homMk (P.hom.app q) (Category.comp_id _)
    let qQ : (Over.lift Q.left Q.hom).obj q ⟶ Over.mk (𝟙 A) :=
      Over.homMk (Q.hom.app q) (Category.comp_id _)
    have h : (Over.liftDiagramMap A f).app q ≫ qQ = qP := by
      apply Over.OverMorphism.ext
      exact NatTrans.congr_app f.w q
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map h).trans (Category.comp_id _).symm)

/--
For an augmented-algebra map `f : P ⟶ Q`, the diagonal replacement map followed by
the vertical comparison at `Q` equals the vertical comparison at `P` followed by
the cotangent map of `f`.
-/
@[reassoc]
theorem polynomialCotangentReplacementToOriginal_naturality
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)} (f : P ⟶ Q) :
    (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).map
        ((polynomialCotangentReplacementFunctor.{u, v} k A).map f) ≫
      polynomialCotangentReplacementToOriginal k A Q =
        polynomialCotangentReplacementToOriginal k A P ≫ cotangentSimplicialMap.{u, v} k A f := by
  apply NatTrans.ext
  funext q
  exact NatTrans.congr_app
    (polynomialCotangentAugmentation_naturality k A ((Over.liftDiagramMap A f).app q)) q

/--
For an augmented-algebra map `f : P ⟶ Q`, the diagonal replacement map followed by
the horizontal comparison at `Q` equals the horizontal comparison at `P` to the fixed
canonical cotangent diagram.
-/
@[reassoc]
theorem polynomialCotangentReplacementToStandard_naturality
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)} (f : P ⟶ Q) :
    (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).map
        ((polynomialCotangentReplacementFunctor.{u, v} k A).map f) ≫
      polynomialCotangentReplacementToStandard k A Q =
        polynomialCotangentReplacementToStandard k A P := by
  let D := SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)
  let s := (SimplicialObject.diagonalConstIso (ModuleCat.{max u v} A)
    ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A)))).hom
  let a := (polynomialCotangentReplacementFunctor.{u, v} k A).map f
  let hP := polynomialCotangentReplacementHorizontal.{u, v} k A P
  let hQ := polynomialCotangentReplacementHorizontal.{u, v} k A Q
  have h : a ≫ hQ = hP :=
    ((polynomialCotangentReplacementHorizontalNatTrans.{u, v} k A).naturality f).trans
      (Category.comp_id _)
  change D.map a ≫ (D.map hQ ≫ s) = D.map hP ≫ s
  exact (Category.assoc (D.map a) (D.map hQ) s).symm.trans
    (congrArg (fun a => a ≫ s) ((D.map_comp a hQ).symm.trans (congrArg D.map h)))

/--
The functor assigning to each augmented simplicial algebra over `A` the normalized
Moore complex of its degreewise cotangent diagram.
-/
def cotangentResolutionComplexFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v} A) ℕ :=
  cotangentSimplicialFunctor.{u, v} k A ⋙ normalizedMooreComplex (ModuleCat.{max u v} A)

/--
The functor assigning to each augmented simplicial algebra over `A` the normalized
Moore complex of the diagonal polynomial cotangent replacement.
-/
def polynomialCotangentReplacementComplexFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      ChainComplex (ModuleCat.{max u v} A) ℕ :=
  polynomialCotangentReplacementFunctor.{u, v} k A ⋙
    SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A) ⋙
      normalizedMooreComplex (ModuleCat.{max u v} A)

/--
The cochain-complex functor obtained by placing normalized cotangent chain degree `n`
in integer cochain degree `-n` and extending by zero in positive cochain degrees.
-/
def cotangentResolutionCochainFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      CochainComplex (ModuleCat.{max u v} A) ℤ where
  obj Q := (cotangentResolutionComplex.{u, v} k A Q).extend ComplexShape.embeddingDownNat
  map f := HomologicalComplex.extendMap
    ((cotangentResolutionComplexFunctor.{u, v} k A).map f) ComplexShape.embeddingDownNat
  map_id Q := by
    rw [(cotangentResolutionComplexFunctor.{u, v} k A).map_id Q,
      HomologicalComplex.extendMap_id]
    rfl
  map_comp f g := by
    rw [(cotangentResolutionComplexFunctor.{u, v} k A).map_comp f g,
      HomologicalComplex.extendMap_comp]
    rfl

/--
The cochain-complex functor obtained from the normalized diagonal polynomial
replacement by placing chain degree `n` in cochain degree `-n` and extending by zero
in positive cochain degrees.
-/
def polynomialCotangentReplacementCochainFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      CochainComplex (ModuleCat.{max u v} A) ℤ where
  obj Q := (polynomialCotangentReplacementComplex.{u, v} k A Q).extend ComplexShape.embeddingDownNat
  map f := HomologicalComplex.extendMap
    ((polynomialCotangentReplacementComplexFunctor.{u, v} k A).map f) ComplexShape.embeddingDownNat
  map_id Q := by
    rw [(polynomialCotangentReplacementComplexFunctor.{u, v} k A).map_id Q,
      HomologicalComplex.extendMap_id]
    rfl
  map_comp f g := by
    rw [(polynomialCotangentReplacementComplexFunctor.{u, v} k A).map_comp f g,
      HomologicalComplex.extendMap_comp]
    rfl

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]

/--
The functor obtained by localizing the nonpositive-degree cotangent cochain model in
the derived category, with its specified independent derived-category universe.
-/
def cotangentResolutionDerivedFunctor := cotangentResolutionCochainFunctor k A ⋙ DerivedCategory.Q

/--
The functor obtained by applying derived localization to the nonpositive-degree
cochain model of the diagonal polynomial replacement.
-/
def polynomialCotangentReplacementDerivedFunctor :=
  polynomialCotangentReplacementCochainFunctor k A ⋙ DerivedCategory.Q

/--
The natural transformation from the derived polynomial replacement to the derived
cotangent model of the augmentation, induced by the vertical comparison.
-/
def polynomialCotangentReplacementDerivedVertical :
    polynomialCotangentReplacementDerivedFunctor k A ⟶ cotangentResolutionDerivedFunctor k A where
  app Q := DerivedCategory.Q.map (HomologicalComplex.extendMap
    (polynomialCotangentReplacementChainToOriginal k A Q) ComplexShape.embeddingDownNat)
  naturality {P Q} f := by
    let G := normalizedMooreComplex (ModuleCat.{max u v} A) ⋙
      ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{max u v} A) ⋙ DerivedCategory.Q
    let a := (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).map
      ((polynomialCotangentReplacementFunctor.{u, v} k A).map f)
    let vP := polynomialCotangentReplacementToOriginal.{u, v} k A P
    let vQ := polynomialCotangentReplacementToOriginal.{u, v} k A Q
    let b := cotangentSimplicialMap.{u, v} k A f
    have h : a ≫ vQ = vP ≫ b :=
      polynomialCotangentReplacementToOriginal_naturality.{u, v} k A f
    change G.map a ≫ G.map vQ = G.map vP ≫ G.map b
    exact (G.map_comp a vQ).symm.trans
      ((congrArg G.map h).trans (G.map_comp vP b))

/--
The natural transformation from the derived polynomial replacement to the constant
canonical derived cotangent object of `A`, induced by the horizontal comparison.
-/
def polynomialCotangentReplacementDerivedHorizontal :
    polynomialCotangentReplacementDerivedFunctor k A ⟶
      (Functor.const
        (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))).obj
          (cotangentDerived k A) where
  app Q := DerivedCategory.Q.map (HomologicalComplex.extendMap
    (polynomialCotangentReplacementChainToStandard k A Q) ComplexShape.embeddingDownNat)
  naturality {P Q} f := by
    let G := normalizedMooreComplex (ModuleCat.{max u v} A) ⋙
      ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{max u v} A) ⋙ DerivedCategory.Q
    let a := (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} A)).map
      ((polynomialCotangentReplacementFunctor.{u, v} k A).map f)
    let hP := polynomialCotangentReplacementToStandard.{u, v} k A P
    let hQ := polynomialCotangentReplacementToStandard.{u, v} k A Q
    have h : a ≫ hQ = hP :=
      polynomialCotangentReplacementToStandard_naturality.{u, v} k A f
    change G.map a ≫ G.map hQ = G.map hP ≫ 𝟙 _
    exact (G.map_comp a hQ).symm.trans
      ((congrArg G.map h).trans (Category.comp_id _).symm)

/--
The object condition consisting of a polynomial presentation in every simplicial
degree and a trivial-fibration underlying simplicial-set augmentation. Presentations
may use different variable types of height `max u v` in different degrees.
-/
def polynomialCotangentResolutionObjects :
    ObjectProperty (Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :=
  fun Q =>
    (∀ q : ℕ, ∃ σ : Type (max u v),
      Nonempty ((free.{u, v} k).obj σ ≅ Q.left.obj (op ⦋q⦌))) ∧
    polynomialCotangentResolutionCondition k A Q

/--
The full subcategory of augmented simplicial algebras over `A` satisfying the
polynomial cotangent resolution object condition.
-/
abbrev PolynomialCotangentResolutions := (polynomialCotangentResolutionObjects k A).FullSubcategory

/--
On the full category of degreewise polynomial resolutions with underlying
trivial-fibration augmentation, the derived cotangent-model functor is naturally
isomorphic to the constant canonical derived cotangent object, through the two
localized replacement augmentations.
-/
def polynomialCotangentResolutionDerivedNatIso :
    (polynomialCotangentResolutionObjects k A).ι ⋙ cotangentResolutionDerivedFunctor k A ≅
      (Functor.const (PolynomialCotangentResolutions k A)).obj (cotangentDerived k A) := by
  let ι := (polynomialCotangentResolutionObjects k A).ι
  let eV : ι ⋙ polynomialCotangentReplacementDerivedFunctor k A ≅
      ι ⋙ cotangentResolutionDerivedFunctor k A :=
    NatIso.ofComponents
      (fun Q => by
        letI : QuasiIso (polynomialCotangentReplacementChainToOriginal k A Q.obj) :=
          polynomialCotangentReplacementChainToOriginal_quasiIso k A Q.obj Q.property.1
        let φ := HomologicalComplex.extendMap
          (polynomialCotangentReplacementChainToOriginal k A Q.obj) ComplexShape.embeddingDownNat
        have hφ : IsIso (DerivedCategory.Q.map φ) :=
          (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) φ).mpr inferInstance
        exact @asIso _ _ _ _ (DerivedCategory.Q.map φ) hφ)
      (by
        intro P Q f
        exact (polynomialCotangentReplacementDerivedVertical k A).naturality f.hom)
  let eH : ι ⋙ polynomialCotangentReplacementDerivedFunctor k A ≅
      (Functor.const (PolynomialCotangentResolutions k A)).obj (cotangentDerived k A) :=
    NatIso.ofComponents
      (fun Q => by
        letI : QuasiIso (polynomialCotangentReplacementChainToStandard k A Q.obj) :=
          polynomialCotangentReplacementChainToStandard_quasiIso k A Q.obj Q.property.2
        let φ := HomologicalComplex.extendMap
          (polynomialCotangentReplacementChainToStandard k A Q.obj) ComplexShape.embeddingDownNat
        have hφ : IsIso (DerivedCategory.Q.map φ) :=
          (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) φ).mpr inferInstance
        exact @asIso _ _ _ _ (DerivedCategory.Q.map φ) hφ)
      (by
        intro P Q f
        exact (polynomialCotangentReplacementDerivedHorizontal k A).naturality f.hom)
  exact eV.symm ≪≫ eH

end CommAlgCat

end
