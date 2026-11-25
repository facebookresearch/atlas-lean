/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.BGTContravariantPresheaves
public import MathlibExt.AlgebraicTopology.BGTVerdierQuotients
public import MathlibExt.AlgebraicTopology.StableInfinityFilteredColimits

/-!
# The actual Ind-omega, kappa-compact cone and Verdier suspension sources

Ind-omega is the full subcategory of the actual right-fibration presheaf
localization consisting of filtered colimits of actual representables.
Every such colimit has its native coherent cocone and universal test.
F-kappa is a small presentation of the native kappa-compact full category
of that same Ind category. Sigma-kappa is its actual Verdier cofiber by
the original Yoneda inclusion. No swindle or K-theory vanishing is input.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Section 2.4,
Definition 9.1 and Remark 9.2, pages 57--58.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.BGTIndKappaModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityCategoryModels
open StableInfinityFilteredColimits StableInfinityMappingSpaceMaps
open BGTContravariantPresheaves BGTVerdierQuotients
open scoped Simplicial Cardinal

/-- The actual apex of the entire native universal cocone. -/
def coconeApex {I : Type} [Category.{0} I] (C : SSet.{1})
    (d : indexNerve I ⟶ C) (c : (rightCones C d) _⦋0⦌) : C _⦋0⦌ :=
  (coconeDiagram C d c).app (op ⦋0⦌)
    (ULift.up (ComposableArrows.mk₀ (WithTerminal.star : WithTerminal I)))

/-- Membership is a native filtered-colimit presentation by representables. -/
def IsIndOmegaVertex {C : SSet.{0}} (P : PresheafInfinitySource C)
    (Y : PresheafYonedaSource C P) (x : P.category _⦋0⦌) : Prop :=
  ∃ (J : SSet.{0}) (_ : SSet.Quasicategory J) (M : CofinalKappaIndex ℵ₀ J)
    (d : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj J ⟶ P.category),
    (∀ j : J _⦋0⦌, IsRepresentableVertex P Y
      (d.app (op ⦋0⦌) (ULift.up j))) ∧
    ∃ c : (rightCones P.category (indexedDiagram M d)) _⦋0⦌,
      IsInitialObject (rightCones P.category (indexedDiagram M d)) c ∧
      EquivalentVertices P.category x
        (coconeApex P.category (indexedDiagram M d) c)

/-- The actual full filtered-representable closure in the presheaf source. -/
def indOmegaCategory {C : SSet.{0}} (P : PresheafInfinitySource C)
    (Y : PresheafYonedaSource C P) : SSet.{1} :=
  (P.category.fullEnhancedSubcategory (IsIndOmegaVertex P Y)).toSSet

/-- The native inclusion keeps all coherent parameter arrows. -/
def indOmegaInclusion {C : SSet.{0}} (P : PresheafInfinitySource C)
    (Y : PresheafYonedaSource C P) : indOmegaCategory P Y ⟶ P.category :=
  (P.category.fullEnhancedSubcategory (IsIndOmegaVertex P Y)).ι

/-- The actual compact objects are selected by the native mapping-colimit test. -/
def compactCategory (k : Cardinal.{0}) (I : StableInfinityCategory.{1}) : SSet.{1} :=
  (I.toSSet.fullEnhancedSubcategory (IsKappaCompactVertex k I.toSSet)).toSSet

/-- The actual compact full subcategory includes every coherent map. -/
def compactInclusion (k : Cardinal.{0}) (I : StableInfinityCategory.{1}) :
    compactCategory k I ⟶ I.toSSet :=
  (I.toSSet.fullEnhancedSubcategory (IsKappaCompactVertex k I.toSSet)).ι

/-- Existence of filtered colimits is tested on the original universal cocones. -/
def HasOmegaFilteredColimits (I : SSet.{1}) : Prop :=
  ∀ (J : SSet.{0}) [SSet.Quasicategory J] (M : CofinalKappaIndex ℵ₀ J)
    (d : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj J ⟶ I),
    ∃ c : (rightCones I (indexedDiagram M d)) _⦋0⦌,
      IsInitialObject (rightCones I (indexedDiagram M d)) c

/-- The cone source is fixed by actual Ind, compactness and whole-category comparisons. -/
structure FKappaSource (C : StableInfinityCategory.{0})
    (k : UncountableRegularCardinal) where
  presheaves : PresheafInfinitySource C.toSSet
  yoneda : PresheafYonedaSource C.toSSet presheaves
  ind : StableInfinityCategory.{1}
  ind_normalization : ind.toSSet = indOmegaCategory presheaves yoneda
  filtered_colimits : HasOmegaFilteredColimits ind.toSSet
  compact : StableInfinityCategory.{1}
  compact_normalization : compact.toSSet = compactCategory k.value ind
  small : StableInfinityCategory.{0}
  small_comparison :
    (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj small.toSSet ⟶ compact.toSSet
  small_weak : CategoricalWeakEquivalence small_comparison
  inclusion : FullStableInclusion C small
  inclusion_normalization :
    (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).map inclusion.functor.map ≫
      small_comparison ≫ eqToHom compact_normalization ≫
      compactInclusion k.value ind ≫ eqToHom ind_normalization ≫
      indOmegaInclusion presheaves yoneda = yoneda.map

/-- The literal normalized inclusion from F-kappa into the same presheaf source. -/
def FKappaSource.presheafMap {C : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (F : FKappaSource C k) :
    (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj F.small.toSSet ⟶
      F.presheaves.category :=
  F.small_comparison ≫ eqToHom F.compact_normalization ≫
    compactInclusion k.value F.ind ≫ eqToHom F.ind_normalization ≫
    indOmegaInclusion F.presheaves F.yoneda

/-- Sigma-kappa is the actual quotient of this source cone by this source inclusion. -/
structure SigmaKappaSource (C : StableInfinityCategory.{0})
    (k : UncountableRegularCardinal) where
  cone : FKappaSource C k
  quotient : StableVerdierQuotient cone.inclusion

/-- Its exact sequence has the original category, native compact cone and native quotient. -/
def SigmaKappaSource.exactSequence {C : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (S : SigmaKappaSource C k) :
    StableExactSequence.{0} :=
  ⟨C, S.cone.small, S.cone.inclusion, S.quotient⟩

/-- The suspension carrier is the actual Verdier cofiber category. -/
def sigmaCategory {C : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (S : SigmaKappaSource C k) :
    StableInfinityCategory.{0} := S.quotient.category

/-- The actual suspension map is the original quotient functor. -/
def sigmaQuotient {C : StableInfinityCategory.{0}}
    {k : UncountableRegularCardinal} (S : SigmaKappaSource C k) :
    ExactFunctor S.cone.small (sigmaCategory S) := S.quotient.quotient

end MathlibExt.AlgebraicTopology.BGTIndKappaModels
