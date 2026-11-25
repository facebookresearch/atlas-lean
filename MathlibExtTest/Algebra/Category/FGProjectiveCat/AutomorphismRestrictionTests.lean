/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.AutomorphismRestriction

/-!
# Consumers of scalar automorphism restriction

The tests retain independent ring/carrier universes and the original tensor
representatives, inverse unit and natural module-map action.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe v uR uS

namespace MathlibExtTest.Algebra.Category.FGProjectiveCat.AutomorphismRestrictionTests

variable {R : Type uR} {S : Type uS} [Ring R] [CommRing S]
variable (f : R →+* S) (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f)

example (M : ModuleCat.{max uS v} S) (s : S) (p : M) :
    ModuleCat.automorphismRestrictionLinearEquiv f σ hσ M
      (show (ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars σ.toRingHom).obj M) from
        s • (show (ModuleCat.extendScalars σ.toRingHom).obj M from
          (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app M p)) =
      (show (ModuleCat.restrictScalars f).obj M from σ.symm s • p) :=
  ModuleCat.automorphismRestrictionLinearEquiv_pure f σ hσ M s p

example (M : ModuleCat.{max uS v} S) (p : M) :
    (ModuleCat.automorphismRestrictionLinearEquiv f σ hσ M).symm p =
      (show (ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars σ.toRingHom).obj M) from
        (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app M p) :=
  ModuleCat.automorphismRestrictionLinearEquiv_symm_apply f σ hσ M p

example (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule) :
    FGProjectiveCat.baseChange.{max uS v} σ.toRingHom ⋙
        FGProjectiveCat.restrictScalars.{max uS v} f hf hp ≅
      FGProjectiveCat.restrictScalars.{max uS v} f hf hp :=
  FGProjectiveCat.baseChangeAutomorphismRestrictScalarsIso f hf hp σ hσ

#print axioms ModuleCat.automorphismRestrictionLinearEquiv
#print axioms FGProjectiveCat.baseChangeAutomorphismRestrictScalarsIso

end MathlibExtTest.Algebra.Category.FGProjectiveCat.AutomorphismRestrictionTests

end
