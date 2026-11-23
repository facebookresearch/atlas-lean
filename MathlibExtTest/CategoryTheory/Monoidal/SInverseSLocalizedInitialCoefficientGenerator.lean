/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedInitialCoefficientGenerator
public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnit

/-! Ordinary-client use of the actual characteristic, its inverse unit square,
and its value on every whole-core canonical localization point. -/

public section

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SInverseS.LocalizedInitialCoefficientGeneratorTests

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0}) (q : ℕ)

/-- The canonical degree-zero coefficient class used by these ordinary clients. -/
abbrev clientInitialClass :
    coreTranslationHomologyModuleCat C R q ⟶ coreTranslationActionCoefficientHomology C R q 0 :=
  CategoryHomology.coefficientHomologyClass (coreTranslationCoefficientFunctor C R q)
    (0 : Translation C)

local notation "T" => coreTranslationDenominators C
local notation "L" => ModuleCat.localizedModuleFunctor T
local notation "V" => coreTranslationHomologyModuleCat C R q
local notation "W" => coreTranslationActionCoefficientHomology C R q 0
local notation "P" => localizedCoreTranslationHomologyModuleCat C R q
local notation "z" => localizedCoreTranslationActionCoefficientRefinementZeroIso C R q
local notation "xiso" => coreTranslationCoefficientLocalizationIsoApp C R q (0 : Translation C)

example : (L).map (clientInitialClass C R q) = (xiso).hom ≫ (z).inv := by
  have h := localizedCoreTranslationActionCoefficientRefinementZeroIso_initial_generator C R q
  change (L).map (clientInitialClass C R q) ≫ (z).hom = (xiso).hom at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun f => f ≫ (z).inv) h

example :
    clientInitialClass C R q ≫ (ModuleCat.localizedModuleFunctorUnit T).app W =
      (ModuleCat.localizedModuleFunctorUnit T).app V ≫
        (ModuleCat.restrictScalars
          (algebraMap (coreTranslationRing C) (Localization T))).map (xiso).hom ≫
        (ModuleCat.restrictScalars
          (algebraMap (coreTranslationRing C) (Localization T))).map (z).inv := by
  have h := localizedCoreTranslationActionCoefficientRefinementZeroIso_initial_generator C R q
  change (L).map (clientInitialClass C R q) ≫ (z).hom = (xiso).hom at h
  have hInv : (L).map (clientInitialClass C R q) = (xiso).hom ≫ (z).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f => f ≫ (z).inv) h
  have hUnit := ModuleCat.localizedModuleFunctorUnit_naturality T (clientInitialClass C R q)
  rw [hInv] at hUnit
  simpa only [Functor.map_comp, Category.assoc] using hUnit

example (x : coreTranslationHomologyModule C R q) :
    ((L).map (clientInitialClass C R q) ≫ (z).hom)
        ((V).localizedModuleMkLinearMap T x) = LocalizedModule.mk x (1 : T) := by
  have h := localizedCoreTranslationActionCoefficientRefinementZeroIso_initial_generator C R q
  change (L).map (clientInitialClass C R q) ≫ (z).hom = (xiso).hom at h
  have hx := congrArg (fun f => f x)
    (coreTranslationCoefficientLocalizationLinearEquiv_comp_mk C R q)
  have hPoint : (xiso).hom ((V).localizedModuleMkLinearMap T x) =
      LocalizedModule.mk x (1 : T) := hx
  calc
    _ = (xiso).hom ((V).localizedModuleMkLinearMap T x) :=
      congrArg (fun f : (L).obj V ⟶ P => f ((V).localizedModuleMkLinearMap T x)) h
    _ = _ := hPoint

end CategoryTheory.SInverseS.LocalizedInitialCoefficientGeneratorTests

end
