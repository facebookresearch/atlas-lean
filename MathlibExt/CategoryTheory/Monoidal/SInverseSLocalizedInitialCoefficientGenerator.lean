/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.LocalizationGenerator
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedSpectralSequence
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Logic.Small.Basic

/-!
# The actual localized initial coefficient class

The original initial coefficient summand, followed by the alternating quotient
and inverse Dold--Kan homology comparison, is carried by the existing localized
coefficient-refinement zero isomorphism to the canonical shrunk/raw component.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SInverseS

open CategoryHomology

/-- The original module carrier has all coproducts indexed at its actual universe. -/
noncomputable local instance localizedInitialModuleCoproducts
    (S : Type u) [Ring S] : HasCoproducts.{u} (ModuleCat.{u} S) :=
  fun (I : Type u) => by
    let : Small.{u} (Discrete I) := small_self (Discrete I)
    let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
      AddCommGrpCat.hasColimitsOfShape.{u, u, u} (J := Discrete I)
    exact ModuleCat.hasColimitsOfShape.{u, u, u, u} (J := Discrete I) (R := S)

section InitialCaches

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u}) (q : ℕ)

/-- The exact original coefficient functor at the given core degree. -/
private abbrev cachedInitialCoefficientFunctor :
    Translation C ⥤ ModuleCat.{u} (coreTranslationRing C) :=
  coreTranslationCoefficientFunctor C R q

/-- The same original alternating coefficient-bar complex, with its carrier fixed. -/
private abbrev cachedInitialCoefficientComplex :
    ChainComplex (ModuleCat.{u} (coreTranslationRing C)) ℕ :=
  CategoryHomology.coefficientBarComplex (cachedInitialCoefficientFunctor C R q)

/-- The original normalized-to-alternating Dold--Kan comparison. -/
private abbrev cachedInitialCoefficientZeroIso :
    CategoryHomology.homologyWithCoefficients (cachedInitialCoefficientFunctor C R q) 0 ≅
      (cachedInitialCoefficientComplex C R q).homology 0 :=
  CategoryHomology.coefficientHomologyZeroComparison (cachedInitialCoefficientFunctor C R q)

/-- The actual localization functor between the two original module categories. -/
private abbrev cachedInitialLocalization :
    ModuleCat.{u} (coreTranslationRing C) ⥤
      ModuleCat.{u} (Localization (coreTranslationDenominators C)) :=
  ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)

/-- The original zero-column comparison, with both module endpoints fixed. -/
private abbrev cachedInitialRefinementZeroIso :
    (cachedInitialLocalization C).obj
        (CategoryHomology.homologyWithCoefficients (cachedInitialCoefficientFunctor C R q) 0) ≅
      localizedCoreTranslationHomologyModuleCat C R q :=
  localizedCoreTranslationActionCoefficientRefinementZeroIso C R q

/-- The same terminal coefficient component, with its source object fixed. -/
private abbrev cachedInitialCoefficientComponentIso :
    (cachedInitialLocalization C).obj
        ((cachedInitialCoefficientFunctor C R q).obj (0 : Translation C)) ≅
      localizedCoreTranslationHomologyModuleCat C R q :=
  coreTranslationCoefficientLocalizationIsoApp C R q (0 : Translation C)

set_option diagnostics true in
/-- The literal original summand, alternating quotient and inverse Dold--Kan map. -/
private abbrev cachedInitialRawCoefficientClass :
    (cachedInitialCoefficientFunctor C R q).obj (0 : Translation C) ⟶
      CategoryHomology.homologyWithCoefficients (cachedInitialCoefficientFunctor C R q) 0 :=
  CategoryHomology.coefficientBarι (cachedInitialCoefficientFunctor C R q)
      (ComposableArrows.mk₀ (0 : Translation C)) ≫
    (cachedInitialCoefficientComplex C R q).pOpcycles 0 ≫
    (cachedInitialCoefficientComplex C R q).isoHomologyι₀.inv ≫
    (cachedInitialCoefficientZeroIso C R q).inv

/-- Associativity identifies that same raw route with the existing named class. -/
private theorem cachedInitialRawCoefficientClass_eq_class :
    cachedInitialRawCoefficientClass C R q =
      CategoryHomology.coefficientHomologyClass
        (cachedInitialCoefficientFunctor C R q) (0 : Translation C) := by
  let F : Translation C ⥤ ModuleCat.{u} (coreTranslationRing C) :=
    cachedInitialCoefficientFunctor C R q
  let K : ChainComplex (ModuleCat.{u} (coreTranslationRing C)) ℕ :=
    cachedInitialCoefficientComplex C R q
  let a : F.obj (0 : Translation C) ⟶ K.X 0 :=
    CategoryHomology.coefficientBarι F (ComposableArrows.mk₀ (0 : Translation C))
  let b : K.X 0 ⟶ K.opcycles 0 := K.pOpcycles 0
  let c : K.opcycles 0 ⟶ K.homology 0 := K.isoHomologyι₀.inv
  let d : K.homology 0 ⟶ CategoryHomology.homologyWithCoefficients F 0 :=
    (cachedInitialCoefficientZeroIso C R q).inv
  change a ≫ b ≫ c ≫ d = a ≫ (b ≫ c) ≫ d
  exact congrArg
    (fun k : K.X 0 ⟶ CategoryHomology.homologyWithCoefficients F 0 => a ≫ k)
    (Category.assoc b c d).symm

end InitialCaches

-- Reducing the normalized/bar and localization comparisons exceeds the default heartbeat limit.
set_option diagnostics true in
/-- The actual localized initial coefficient class is the canonical shrunk/raw
coefficient component under the existing coefficient-refinement zero iso. -/
private theorem cachedInitialRawClass_calibration
    (C : Type u) [Category.{u} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    (cachedInitialLocalization C).map (cachedInitialRawCoefficientClass C R q) ≫
      (cachedInitialRefinementZeroIso C R q).hom =
        (cachedInitialCoefficientComponentIso C R q).hom := by
  rw [cachedInitialRawCoefficientClass_eq_class]
  let F : Translation C ⥤ ModuleCat.{u} (coreTranslationRing C) :=
    coreTranslationCoefficientFunctor C R q
  let L : ModuleCat.{u} (coreTranslationRing C) ⥤
      ModuleCat.{u} (Localization (coreTranslationDenominators C)) :=
    ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)
  let G : Translation C ⥤ ModuleCat.{u} (Localization (coreTranslationDenominators C)) :=
    localizedCoreTranslationCoefficientFunctor C R q
  let E : F ⋙ L ≅ G := coreTranslationCoefficientLocalizationNatIso C R q
  let H₀ : (Translation C ⥤ ModuleCat.{u} (Localization (coreTranslationDenominators C))) ⥤
      ModuleCat.{u} (Localization (coreTranslationDenominators C)) :=
    CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C)
      (A := ModuleCat.{u} (Localization (coreTranslationDenominators C))) 0
  let eLoc : L.obj (CategoryHomology.homologyWithCoefficients F 0) ≅
      CategoryHomology.homologyWithCoefficients (F ⋙ L) 0 :=
    CategoryHomology.homologyWithCoefficientsLocalizationIso
      (coreTranslationDenominators C) F 0
  let hCoeff : CategoryHomology.homologyWithCoefficients (F ⋙ L) 0 ⟶
      CategoryHomology.homologyWithCoefficients G 0 := H₀.map E.hom
  let eInit : CategoryHomology.homologyWithCoefficients G 0 ≅ G.obj (0 : Translation C) :=
    CategoryHomology.homologyWithCoefficientsZeroIsoOfIsInitial
      G (0 : Translation C) (Translation.zeroIsInitial (C := C))
  let zeta : L.obj (CategoryHomology.homologyWithCoefficients F 0) ≅
      G.obj (0 : Translation C) := cachedInitialRefinementZeroIso C R q
  let xi : L.obj (F.obj (0 : Translation C)) ≅ G.obj (0 : Translation C) :=
    cachedInitialCoefficientComponentIso C R q
  have hZeta : zeta.hom = eLoc.hom ≫ hCoeff ≫ eInit.hom := by
    have hIso : zeta = (eLoc ≪≫ H₀.mapIso E) ≪≫ eInit := by rfl
    have hHom : zeta.hom = (eLoc.hom ≫ hCoeff) ≫ eInit.hom :=
      congrArg
        (fun e : L.obj (CategoryHomology.homologyWithCoefficients F 0) ≅
          G.obj (0 : Translation C) => e.hom) hIso
    exact hHom.trans (Category.assoc eLoc.hom hCoeff eInit.hom)
  have hL : L.map (CategoryHomology.coefficientHomologyClass F (0 : Translation C)) ≫
      eLoc.hom = CategoryHomology.coefficientHomologyClass (F ⋙ L) (0 : Translation C) :=
    CategoryHomology.map_coefficientHomologyClass_comp_homologyWithCoefficientsLocalizationIso_hom
      (coreTranslationDenominators C) F (0 : Translation C)
  have hE : CategoryHomology.coefficientHomologyClass (F ⋙ L) (0 : Translation C) ≫ hCoeff =
      E.hom.app (0 : Translation C) ≫
        CategoryHomology.coefficientHomologyClass G (0 : Translation C) :=
    CategoryHomology.coefficientHomologyClass_naturality E.hom (0 : Translation C)
  have hG : CategoryHomology.coefficientHomologyClass G (0 : Translation C) ≫
      eInit.hom = 𝟙 (G.obj (0 : Translation C)) := by
    let K : ChainComplex (ModuleCat.{u} (Localization (coreTranslationDenominators C))) ℕ :=
      CategoryHomology.coefficientBarComplex G
    let a : G.obj (0 : Translation C) ⟶ K.X 0 :=
      CategoryHomology.coefficientBarι G (ComposableArrows.mk₀ (0 : Translation C))
    let b : K.X 0 ⟶ K.opcycles 0 := K.pOpcycles 0
    let c : K.opcycles 0 ⟶ K.homology 0 := K.isoHomologyι₀.inv
    let d : K.homology 0 ⟶ CategoryHomology.homologyWithCoefficients G 0 :=
      (CategoryHomology.coefficientHomologyZeroComparison G).inv
    have hRaw : a ≫ b ≫ c ≫ d ≫ eInit.hom = 𝟙 (G.obj (0 : Translation C)) := by
      have h :=
        CategoryHomology.coefficientBarι_comp_homologyWithCoefficientsZeroIsoOfIsInitial_hom
          G (0 : Translation C) (Translation.zeroIsInitial (C := C))
      change a ≫ b ≫ c ≫ d ≫ eInit.hom = 𝟙 (G.obj (0 : Translation C)) at h
      exact h
    change (a ≫ (b ≫ c) ≫ d) ≫ eInit.hom = 𝟙 (G.obj (0 : Translation C))
    rw [Category.assoc a ((b ≫ c) ≫ d) eInit.hom,
      Category.assoc (b ≫ c) d eInit.hom,
      Category.assoc b c (d ≫ eInit.hom)]
    exact hRaw
  have hXi : E.hom.app (0 : Translation C) = xi.hom := by rfl
  change L.map (CategoryHomology.coefficientHomologyClass F (0 : Translation C)) ≫
    zeta.hom = xi.hom
  calc
    _ = L.map (CategoryHomology.coefficientHomologyClass F (0 : Translation C)) ≫
        eLoc.hom ≫ hCoeff ≫ eInit.hom := by rw [hZeta]
    _ = CategoryHomology.coefficientHomologyClass (F ⋙ L) (0 : Translation C) ≫
        hCoeff ≫ eInit.hom := by
      rw [← Category.assoc, hL]
    _ = E.hom.app (0 : Translation C) ≫
        CategoryHomology.coefficientHomologyClass G (0 : Translation C) ≫ eInit.hom := by
      rw [← Category.assoc, hE, Category.assoc]
    _ = E.hom.app (0 : Translation C) := by rw [hG, Category.comp_id]
    _ = xi.hom := hXi

/-- The original coefficient homology class is carried by the same localized
zero-column comparison to the canonical coefficient component. The private
raw calibration proves the identical summand/quotient/Dold--Kan route. -/
theorem localizedCoreTranslationActionCoefficientRefinementZeroIso_initial_generator
    (C : Type u) [Category.{u} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    (ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)).map
        (CategoryHomology.coefficientHomologyClass
          (coreTranslationCoefficientFunctor C R q) (0 : Translation C)) ≫
      (localizedCoreTranslationActionCoefficientRefinementZeroIso C R q).hom =
        (coreTranslationCoefficientLocalizationIsoApp C R q
          (0 : Translation C)).hom := by
  let F : Translation C ⥤ ModuleCat.{u} (coreTranslationRing C) :=
    coreTranslationCoefficientFunctor C R q
  let L : ModuleCat.{u} (coreTranslationRing C) ⥤
      ModuleCat.{u} (Localization (coreTranslationDenominators C)) :=
    ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)
  let ζ := localizedCoreTranslationActionCoefficientRefinementZeroIso C R q
  have hRaw : cachedInitialRawCoefficientClass C R q =
      CategoryHomology.coefficientHomologyClass F (0 : Translation C) :=
    cachedInitialRawCoefficientClass_eq_class C R q
  have hMap : L.map (cachedInitialRawCoefficientClass C R q) ≫ ζ.hom =
      L.map (CategoryHomology.coefficientHomologyClass F (0 : Translation C)) ≫ ζ.hom :=
    congrArg
      (fun f : F.obj (0 : Translation C) ⟶ CategoryHomology.homologyWithCoefficients F 0 =>
        L.map f ≫ ζ.hom) hRaw
  exact hMap.symm.trans (cachedInitialRawClass_calibration C R q)

end CategoryTheory.SInverseS

end
