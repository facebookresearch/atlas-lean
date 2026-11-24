/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Algebra.Category.FGModuleCat.RestrictScalarsCoherence
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall

/-! # Independent ring and module-universe finite restriction clients -/

set_option autoImplicit false
noncomputable section

open CategoryTheory FGModuleCat

namespace MathlibExtTest.RestrictScalarsUniverseLift

universe v w uR uA
variable {R : Type uR} {A : Type uA} [Ring R] [Ring A]
variable (f : R →+* A) (hf : f.IsFinite)

include hf in
example (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    @Module.Finite R M _ _ (Module.compHom M f) :=
  finite_of_finite f hf M

example {M N : FGModuleCat.{v} A} (g : M ⟶ N) :
    ((restrictScalars.{v} f hf).map g).hom =
      (ModuleCat.restrictScalars.{v} f).map g.hom :=
  restrictScalars_map_hom.{v} f hf g

example : (restrictScalars.{v} f hf).Faithful := restrictScalars_faithful.{v} f hf

example : restrictScalars.{v} f hf ⋙ FGModuleCat.ulift.{v, w} R ≅
    FGModuleCat.ulift.{v, w} A ⋙ restrictScalars.{max v w} f hf :=
  restrictScalarsULiftIso f hf

example (M : FGModuleCat.{v} A) (x : M) :
    (restrictScalarsULiftIso.{v, w} f hf).hom.app M (ULift.up x) = ULift.up x :=
  restrictScalarsULiftIso_hom_apply f hf M x

example : (FGModuleCat.ulift.{max uR v, w, uR} R).IsEquivalence := inferInstance

example : (FGModuleCat.ulift.{max uA v, w, uA} A).IsEquivalence := inferInstance

example : restrictScalars.{v} f hf ⋙
      forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ≅
    forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ ModuleCat.restrictScalars.{v} f :=
  restrictScalarsCompForget₂Iso f hf


#print axioms finite_of_finite
#print axioms restrictScalars
#print axioms restrictScalarsULiftIso
#print axioms restrictScalarsULiftIso_hom_apply
#print axioms restrictScalarsCompForget₂Iso

end MathlibExtTest.RestrictScalarsUniverseLift
