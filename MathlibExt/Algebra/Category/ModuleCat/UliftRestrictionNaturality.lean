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
# Scalar restriction commutes with module carrier lifting

For a homomorphism f : S → R of rings, restricting an R-module to S and then lifting its
carrier agrees naturally with lifting the R-module first and restricting afterward. Both
orders use the same lifted carrier and the S-action through f.

The comparison and its inverse preserve every lifted element. The two ring universes, the
module carrier universe and the lift height are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v s h

namespace ModuleCat

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The natural isomorphism between restriction and module lifting.

For f : S → R, restriction along f followed by lifting is naturally isomorphic to lifting
followed by restriction along f, through identity maps on the carriers. -/
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

/-- Elements under the forward restriction–lift comparison.

The forward component sends each m ∈ ULift M to the same lifted element m. -/
theorem restrictScalarsUliftIso_hom_apply (f : S →+* R) (M : ModuleCat.{s} R)
    (m : ULift.{h} M) :
    ((restrictScalarsUliftIso.{u, v, s, h} f).hom.app M).hom m = m := rfl

/-- Elements under the inverse restriction–lift comparison.

The inverse component sends each m ∈ ULift M to the same lifted element m. -/
theorem restrictScalarsUliftIso_inv_apply (f : S →+* R) (M : ModuleCat.{s} R)
    (m : ULift.{h} M) :
    ((restrictScalarsUliftIso.{u, v, s, h} f).inv.app M).hom m = m := rfl

end ModuleCat

end
