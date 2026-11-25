/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationUnitIso

/-! # Tests for localization of modules already inverting denominators -/

@[expose] public section

noncomputable section

open CategoryTheory

universe v u

namespace MathlibExtTest.ModuleCatLocalizationUnitIso

variable {R : Type u} [CommRing R] [Small.{v} R]
variable (S : Submonoid R) (M : ModuleCat.{v} R)
variable (h : ∀ s : S, Function.Bijective (fun x : M => (s : R) • x))

#check IsLocalizedModule.idOfBijectiveSmul
#check ModuleCat.localizedModuleLinearEquivOfBijectiveSmul
#check ModuleCat.localizedModuleLinearEquivOfBijectiveSmul_apply_mk
#check ModuleCat.localizedModuleAddCommGrpIsoOfBijectiveSmul
#check ModuleCat.localizedModuleAddCommGrpIsoOfBijectiveSmul_hom_mk

example (x : M) :
    ModuleCat.localizedModuleLinearEquivOfBijectiveSmul S M h
        (M.localizedModuleMkLinearMap S x) = x := by
  simp

#print axioms IsLocalizedModule.idOfBijectiveSmul
#print axioms ModuleCat.localizedModuleLinearEquivOfBijectiveSmul
#print axioms ModuleCat.localizedModuleLinearEquivOfBijectiveSmul_apply_mk
#print axioms ModuleCat.localizedModuleAddCommGrpIsoOfBijectiveSmul

end MathlibExtTest.ModuleCatLocalizationUnitIso

end
