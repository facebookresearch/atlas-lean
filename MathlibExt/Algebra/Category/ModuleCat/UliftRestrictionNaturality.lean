/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY needed original-ring output lift bridge; Native has not been run.
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Native scalar restriction and module lift commute naturally

Both orders retain the same original lifted carrier and use the original
ring-map action on its down value. Their actual module objects and maps are
compared through identity components. This bridge returns the coefficient
and output lift comparisons through the original-ring scalar restrictions;
no scalar action or coefficient carrier is replaced.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v s h

namespace ModuleCat

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The native module lift commutes with the same actual scalar restriction,
for independently sized rings and original coefficient carriers. -/
def restrictScalarsUliftIso (f : S →+* R) :
    (restrictScalars f : ModuleCat.{s} R ⥤ ModuleCat.{s} S) ⋙ uliftFunctor.{h, s} S ≅
      uliftFunctor.{h, s} R ⋙
        (restrictScalars f : ModuleCat.{max s h} R ⥤ ModuleCat.{max s h} S) :=
  NatIso.ofComponents (fun M => Iso.refl _) (by
    intro M N a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

/-- The comparison retains every original native lifted module element. -/
theorem restrictScalarsUliftIso_hom_apply (f : S →+* R) (M : ModuleCat.{s} R)
    (m : ULift.{h} M) :
    ((restrictScalarsUliftIso.{u, v, s, h} f).hom.app M).hom m = m := rfl

/-- The inverse comparison retains that same original lifted carrier value. -/
theorem restrictScalarsUliftIso_inv_apply (f : S →+* R) (M : ModuleCat.{s} R)
    (m : ULift.{h} M) :
    ((restrictScalarsUliftIso.{u, v, s, h} f).inv.app M).hom m = m := rfl

end ModuleCat

end
