/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import MathlibExt.Algebra.Homology.FirstQuadrantEdge
public import MathlibExt.CategoryTheory.CategoryHomology.Localization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSGroupCompletionSpectralSequence
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedFiberHomologyComparison

/-!
# Localized core-action coefficient refinement

Core homology carries its constructed integral skeleton action. Its category
homology over the translation category gives a module-valued coefficient
refinement of the original Bousfield--Kan second page after forgetting scalars.

Localizing this coefficient refinement commutes with category homology through
the canonical coproduct and normalized-bar comparisons. Every localized
coefficient arrow is invertible, so the actual initial zero translation object
computes the positive-degree vanishing and the zero column.

The localized coefficient refinement is the object `Lambda = L(Q)`. Its
comparison with the actual localized second page is constructed in
`SInverseSActualLocalizedSecondPage` via the integral linear comparison.
The final unlocalized edge declarations retain their stated concentration
hypothesis.

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

local instance localizedSpectralSequenceHasCoproductsAddCommGrpCat :
    HasCoproducts.{u} AddCommGrpCat.{u} := by
  let h : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

namespace CategoryTheory
namespace SInverseS

/-! ### Forgetting module structure in category homology -/

section ForgetCategoryHomology

variable {J A : Type u} [Category.{u} J] [CommRing A]
  (M : J ⥤ ModuleCat.{u} A)


/-- Forgetting module structure commutes with each coproduct object in a
coefficient bar. -/
noncomputable def coefficientBarForgetObjIso (n : ℕ) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj (CategoryHomology.coefficientBarObj M n) ≅
      CategoryHomology.coefficientBarObj (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) n := by
  change ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj (∐ CategoryHomology.coefficientBarFamily M n) ≅
    ∐ fun F ↦ ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj ((CategoryHomology.coefficientBarFamily M n) F)
  exact PreservesCoproduct.iso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
    (CategoryHomology.coefficientBarFamily M n)

/-- The forward degreewise forgetful comparison carries mapped summand
inclusions to the corresponding underlying summand inclusions. -/
@[reassoc]
theorem map_coefficientBarι_comp_coefficientBarForgetObjIso_hom
    {n : ℕ} (F : ComposableArrows J n) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarι M F) ≫
        (coefficientBarForgetObjIso M n).hom =
      CategoryHomology.coefficientBarι (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) F := by
  change ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (Sigma.ι (CategoryHomology.coefficientBarFamily M n) F) ≫
      (PreservesCoproduct.iso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
        (CategoryHomology.coefficientBarFamily M n)).hom =
    Sigma.ι
      (fun F ↦ ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj ((CategoryHomology.coefficientBarFamily M n) F)) F
  rw [← cancel_mono
    (PreservesCoproduct.iso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
      (CategoryHomology.coefficientBarFamily M n)).inv]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [PreservesCoproduct.inv_hom] using
    (Limits.ι_comp_sigmaComparison (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
      (CategoryHomology.coefficientBarFamily M n) F).symm

/-- The inverse degreewise forgetful comparison carries underlying summand
inclusions to mapped module-valued summand inclusions. -/
@[reassoc]
theorem coefficientBarι_comp_coefficientBarForgetObjIso_inv
    {n : ℕ} (F : ComposableArrows J n) :
    CategoryHomology.coefficientBarι (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) F ≫
        (coefficientBarForgetObjIso M n).inv =
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarι M F) := by
  change Sigma.ι
      (fun F ↦ ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj ((CategoryHomology.coefficientBarFamily M n) F)) F ≫
      (PreservesCoproduct.iso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
        (CategoryHomology.coefficientBarFamily M n)).inv =
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (Sigma.ι (CategoryHomology.coefficientBarFamily M n) F)
  simpa only [PreservesCoproduct.inv_hom] using
    Limits.ι_comp_sigmaComparison (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
      (CategoryHomology.coefficientBarFamily M n) F

/-- The degreewise forgetful comparisons assemble into an isomorphism of
simplicial coefficient-bar data. -/
noncomputable def coefficientBarForgetDataIso :
    SimplicialObject.Data.mapObj (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
        (CategoryHomology.coefficientBarData M) ≅
      CategoryHomology.coefficientBarData (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) where
  hom :=
    { app := fun n ↦ (coefficientBarForgetObjIso M n).hom
      w_δ := by
        intro n i
        change (coefficientBarForgetObjIso M (n + 1)).hom ≫
            CategoryHomology.coefficientBarFace (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) i =
          ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarFace M i) ≫
            (coefficientBarForgetObjIso M n).hom
        rw [← cancel_epi (coefficientBarForgetObjIso M (n + 1)).inv]
        rw [Iso.inv_hom_id_assoc]
        apply CategoryHomology.coefficientBar_hom_ext (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
        intro F
        rw [CategoryHomology.coefficientBarι_face]
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarForgetObjIso_inv]
        rw [← Category.assoc, ← ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [CategoryHomology.coefficientBarι_face]
        rw [((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [Category.assoc,
          map_coefficientBarι_comp_coefficientBarForgetObjIso_hom
            M ((nerve J).δ i F)]
        rfl
      w_σ := by
        intro n i
        change (coefficientBarForgetObjIso M n).hom ≫
            CategoryHomology.coefficientBarDegeneracy (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) i =
          ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarDegeneracy M i) ≫
            (coefficientBarForgetObjIso M (n + 1)).hom
        rw [← cancel_epi (coefficientBarForgetObjIso M n).inv]
        rw [Iso.inv_hom_id_assoc]
        apply CategoryHomology.coefficientBar_hom_ext (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
        intro F
        rw [CategoryHomology.coefficientBarι_degeneracy]
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarForgetObjIso_inv]
        rw [← Category.assoc, ← ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [CategoryHomology.coefficientBarι_degeneracy]
        rw [((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [Category.assoc,
          map_coefficientBarι_comp_coefficientBarForgetObjIso_hom
            M ((nerve J).σ i F)]
        rfl }
  inv :=
    { app := fun n ↦ (coefficientBarForgetObjIso M n).inv
      w_δ := by
        intro n i
        change (coefficientBarForgetObjIso M (n + 1)).inv ≫
            ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarFace M i) =
          CategoryHomology.coefficientBarFace (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) i ≫
            (coefficientBarForgetObjIso M n).inv
        apply CategoryHomology.coefficientBar_hom_ext (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
        intro F
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarForgetObjIso_inv M F]
        rw [← ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [CategoryHomology.coefficientBarι_face]
        rw [((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [← Category.assoc, CategoryHomology.coefficientBarι_face]
        rw [Category.assoc,
          coefficientBarι_comp_coefficientBarForgetObjIso_inv
            M ((nerve J).δ i F)]
        rfl
      w_σ := by
        intro n i
        change (coefficientBarForgetObjIso M n).inv ≫
            ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (CategoryHomology.coefficientBarDegeneracy M i) =
          CategoryHomology.coefficientBarDegeneracy (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) i ≫
            (coefficientBarForgetObjIso M (n + 1)).inv
        apply CategoryHomology.coefficientBar_hom_ext (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
        intro F
        rw [← Category.assoc,
          coefficientBarι_comp_coefficientBarForgetObjIso_inv M F]
        rw [← ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [CategoryHomology.coefficientBarι_degeneracy]
        rw [((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map_comp]
        rw [← Category.assoc,
          CategoryHomology.coefficientBarι_degeneracy]
        rw [Category.assoc,
          coefficientBarι_comp_coefficientBarForgetObjIso_inv
            M ((nerve J).σ i F)]
        rfl }
  hom_inv_id := by
    apply SimplicialObject.Data.Hom.ext
    intro n
    exact (coefficientBarForgetObjIso M n).hom_inv_id
  inv_hom_id := by
    apply SimplicialObject.Data.Hom.ext
    intro n
    exact (coefficientBarForgetObjIso M n).inv_hom_id

/-- Forgetting module structure commutes with the simplicial coefficient
bar. -/
noncomputable def coefficientBarForgetSimplicialIso :
    CategoryHomology.coefficientBarSimplicial M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) ≅
      CategoryHomology.coefficientBarSimplicial (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
  SimplicialObject.Data.toSimplicialObject_mapObjIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})
      (CategoryHomology.coefficientBarData M) ≪≫
    (SimplicialObject.Data.toSimplicialFunctor
      (C := AddCommGrpCat.{u})).mapIso (coefficientBarForgetDataIso M)

/-- Forgetting module structure commutes with the alternating coefficient-bar
complex. -/
noncomputable def coefficientBarComplexForgetIso :
    (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryHomology.coefficientBarComplex M) ≅
      CategoryHomology.coefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app (CategoryHomology.coefficientBarSimplicial M) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).mapIso
      (coefficientBarForgetSimplicialIso M)

/-- Forgetting module structure commutes with normalized coefficient bars up
to the canonical Dold--Kan homotopy equivalences. -/
noncomputable def normalizedCoefficientBarForgetHomotopyEquiv :
    HomotopyEquiv
      ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryHomology.normalizedCoefficientBarComplex M))
      (CategoryHomology.normalizedCoefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))) :=
  (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomotopyEquiv
      (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
        (Y := CategoryHomology.coefficientBarSimplicial M))).trans
    ((HomotopyEquiv.ofIso (coefficientBarComplexForgetIso M)).trans
      (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
        (Y := CategoryHomology.coefficientBarSimplicial (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})))).symm)

/-- Forgetting module structure commutes with category homology with
coefficients. -/
noncomputable def homologyWithCoefficientsForgetIso (p : ℕ) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj (CategoryHomology.homologyWithCoefficients M p) ≅
      CategoryHomology.homologyWithCoefficients (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) p :=
  ((HomologicalComplex.mapHomologyFunctorIso p (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app
      (CategoryHomology.normalizedCoefficientBarComplex M)).symm ≪≫
    (normalizedCoefficientBarForgetHomotopyEquiv M).toHomologyIso p

end ForgetCategoryHomology

/-! ### The module refinement and its localization -/

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Category homology of the translation category with coefficients in core
homology carrying its skeleton monoid-algebra action.  The indices are the
core-homology degree and category-homology degree, respectively. -/
noncomputable abbrev coreTranslationActionCoefficientHomology
    (R : AddCommGrpCat.{u}) (q p : ℕ) :=
  CategoryHomology.homologyWithCoefficients
    (coreTranslationCoefficientFunctor C R q) p

/-- After forgetting its monoid-algebra module structure, core-action
coefficient homology is the category homology of the underlying coefficient
system. -/
noncomputable def coreTranslationActionCoefficientHomologyForgetIso
    (R : AddCommGrpCat.{u}) (q p : ℕ) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationActionCoefficientHomology C R q p) ≅
      CategoryHomology.homologyWithCoefficients
        (coreTranslationCoefficientFunctor C R q ⋙
          forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}) p :=
  homologyWithCoefficientsForgetIso
    (coreTranslationCoefficientFunctor C R q) p

/-- The module-valued core-action coefficient homology refines the
translation-projection Bousfield--Kan second page after forgetting scalars. -/
noncomputable def coreTranslationActionSecondPageIso
    (R : AddCommGrpCat.{u}) (p q : ℕ) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationActionCoefficientHomology C R q p) ≅
      ((translationBKHomologySpectralSequence C R).page 2).X (p, q) :=
  coreTranslationActionCoefficientHomologyForgetIso C R q p ≪≫
    (CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C) (A := AddCommGrpCat.{u}) p).mapIso
        (coreTranslationCoefficientFiberNatIso C R q) ≪≫
    (translationBKSecondPageIso C R p q).symm

/-- Localization of the constructed core-action coefficient homology in
bidegree `(p,q)`. -/
noncomputable abbrev localizedCoreTranslationActionCoefficientRefinement
    (R : AddCommGrpCat.{u}) (p q : ℕ) :=
  (ModuleCat.localizedModuleFunctor
      (coreTranslationDenominators C)).obj
    (coreTranslationActionCoefficientHomology C R q p)

/-- The localized coefficient refinement is category homology with the
explicit morphism-inverting localized core-homology coefficient system. -/
noncomputable def localizedCoreTranslationActionCoefficientRefinementIso
    (R : AddCommGrpCat.{u}) (p q : ℕ) :
    localizedCoreTranslationActionCoefficientRefinement C R p q ≅
      localizedCoreTranslationCoefficientHomology C R q p :=
  CategoryHomology.homologyWithCoefficientsLocalizationIso
      (coreTranslationDenominators C)
      (coreTranslationCoefficientFunctor C R q) p ≪≫
    localizedCoreTranslationActionCoefficientHomologyIso C R q p

/-- Every positive horizontal degree of the localized coefficient refinement
vanishes. -/
theorem isZero_localizedCoreTranslationActionCoefficientRefinement
    (R : AddCommGrpCat.{u}) (p q : ℕ) (hp : 1 ≤ p) :
    IsZero (localizedCoreTranslationActionCoefficientRefinement C R p q) :=
  IsZero.of_iso
    (isZero_localizedCoreTranslationCoefficientHomology C R q p hp)
    (localizedCoreTranslationActionCoefficientRefinementIso C R p q)

/-- The zero column of the localized coefficient refinement is
localized core homology. -/
noncomputable def localizedCoreTranslationActionCoefficientRefinementZeroIso
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    localizedCoreTranslationActionCoefficientRefinement C R 0 q ≅
      localizedCoreTranslationHomologyModuleCat C R q :=
  localizedCoreTranslationActionCoefficientRefinementIso C R 0 q ≪≫
    localizedCoreTranslationCoefficientHomologyZeroIso C R q

/-- Compatibility name for the localized coefficient refinement. -/
abbrev translationBKLocalizedSecondPage
    (R : AddCommGrpCat.{u}) (p q : ℕ) :=
  localizedCoreTranslationActionCoefficientRefinement C R p q

/-- Compatibility name for the canonical localized coefficient comparison. -/
def translationBKLocalizedSecondPageIso
    (R : AddCommGrpCat.{u}) (p q : ℕ) :
    translationBKLocalizedSecondPage C R p q ≅
      localizedCoreTranslationCoefficientHomology C R q p :=
  localizedCoreTranslationActionCoefficientRefinementIso C R p q

/-- Compatibility name for positive-degree coefficient-refinement vanishing. -/
theorem isZero_translationBKLocalizedSecondPage
    (R : AddCommGrpCat.{u}) (p q : ℕ) (hp : 1 ≤ p) :
    IsZero (translationBKLocalizedSecondPage C R p q) :=
  isZero_localizedCoreTranslationActionCoefficientRefinement C R p q hp

/-- Compatibility name for the coefficient-refinement zero-column comparison. -/
def translationBKLocalizedSecondPageZeroIso
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    translationBKLocalizedSecondPage C R 0 q ≅
      localizedCoreTranslationHomologyModuleCat C R q :=
  localizedCoreTranslationActionCoefficientRefinementZeroIso C R q

/-! ### The available unlocalized edge comparison -/

/-- Under an independent concentration hypothesis on the original BK second
page, the underlying zero-column core-action term is the homology of the BK
total complex.

This declaration uses the stated unlocalized concentration hypothesis. Its
proof applies the actual unlocalized second-page edge comparison. -/
noncomputable def coreTranslationActionSecondPageTotalHomologyIso
    (R : AddCommGrpCat.{u}) (q : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((translationBKHomologySpectralSequence C R).page 2).X (p, q))) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationActionCoefficientHomology C R q 0) ≅
      (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R
        (SSet.rightCommaNerveDiagram
          (translationProjection (C := C)))).homology q :=
  coreTranslationActionSecondPageIso C R 0 q ≪≫
    HomologicalComplex₂.horizontalSecondPageZeroColumnTotalHomologyIso
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
        (SSet.rightCommaNerveDiagram
          (translationProjection (C := C)))) q hpos

/-- Under the same unlocalized concentration hypothesis, the zero-column
core-action term identifies with homology of the additive `S⁻¹S` nerve. -/
noncomputable def coreTranslationActionSecondPageAbutmentIso
    (R : AddCommGrpCat.{u}) (q : ℕ)
    (hpos : ∀ p q : ℕ, 1 ≤ p → IsZero
      (((translationBKHomologySpectralSequence C R).page 2).X (p, q))) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationActionCoefficientHomology C R q 0) ≅
      ((nerve (Pair C)).chainComplex R).homology q :=
  coreTranslationActionSecondPageTotalHomologyIso C R q hpos ≪≫
    translationBKAbutmentHomologyIso C R q

end SInverseS
end CategoryTheory

end
