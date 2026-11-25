/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.RestrictScalarsBaseChange

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (hf : f.IsFinite)
variable (hp : @Module.Projective R _ S _ f.toModule)
variable (eS : letI : Module R S := f.toModule; S ≃ₗ[R] R × R)

example (P : FGProjectiveCat.{u} R) :
    (FGProjectiveCat.restrictScalars f hf hp).obj ((FGProjectiveCat.baseChange f).obj P) ≅
      P ⊞ P :=
  FGProjectiveCat.restrictScalarsBaseChangeBiprodIso f hf hp eS P

example (P : FGProjectiveCat.{u} R) (s : S) (p : P) :
    FGProjectiveCat.restrictScalarsBaseChangeProductEquiv f hf hp eS P (s ⊗ₜ[R,f] p) =
      ((eS s).1 • p, (eS s).2 • p) :=
  FGProjectiveCat.restrictScalarsBaseChangeProductEquiv_tmul f hf hp eS P s p

end
