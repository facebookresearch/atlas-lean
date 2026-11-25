/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Category.ModuleCat.LocalizationColimits

/-! # Tests for colimit preservation by module localization -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u

variable {R : Type u} [CommRing R]

namespace ModuleCatLocalizationColimitsTests

#check ModuleCat.localizationRestrictScalarsLinearEquiv
#check ModuleCat.extendScalarsLocalizationTensorEquiv
#check ModuleCat.localizedModuleLinearEquivExtendScalars
#check ModuleCat.localizedModuleIsoExtendScalarsApp
#check ModuleCat.localizedModuleIsoExtendScalarsApp_hom_mk_apply
#check ModuleCat.localizedModuleIsoExtendScalarsApp_hom_naturality
#check ModuleCat.localizedModuleFunctorIsoExtendScalars

example (S : Submonoid R) (M : ModuleCat.{u} R) (m : M) :
    (ModuleCat.localizedModuleIsoExtendScalarsApp S M).hom
        (M.localizedModuleMkLinearMap S m) =
      (1 : Localization S) ⊗ₜ[R, algebraMap R (Localization S)] m :=
  ModuleCat.localizedModuleIsoExtendScalarsApp_hom_mk_apply S M m

example (S : Submonoid R) :
    ModuleCat.localizedModuleFunctor.{u} S ≅
      ModuleCat.extendScalars.{u, u, u}
        (algebraMap R (Localization S)) :=
  ModuleCat.localizedModuleFunctorIsoExtendScalars S

example (S : Submonoid R) :
    PreservesColimits (ModuleCat.localizedModuleFunctor.{u} S) := by
  infer_instance

example (S : Submonoid R) {J : Type u} [Category.{u} J]
    (F : J ⥤ ModuleCat.{u} R) :
    PreservesColimit F (ModuleCat.localizedModuleFunctor.{u} S) := by
  infer_instance

#print axioms ModuleCat.localizedModuleFunctorIsoExtendScalars
#print axioms ModuleCat.localizedModuleFunctor_preservesColimits

end ModuleCatLocalizationColimitsTests

end
