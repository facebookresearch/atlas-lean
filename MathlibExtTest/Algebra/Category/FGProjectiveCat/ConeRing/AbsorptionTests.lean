/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ConeRing.Absorption

/-!
# Original pointwise absorption clients

These clients retain the categorical biproduct, both original inverse
programs, arbitrary projective morphisms, and the canonical cofiber row.
No product presentation of a projective carrier is imposed.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe uR

namespace FGProjectiveCat.ConeRing.AbsorptionTests

variable (R : Type uR) [Ring R]

/-- The actual component is an isomorphism of the original chosen biproduct. -/
theorem original_component (X : category R) :
    Nonempty (X ⊞ (infinityFunctor R).obj X ≅ (infinityFunctor R).obj X) :=
  ⟨(absorption R).app X⟩

/-- The original return program followed by forward is the actual infinity identity. -/
theorem return_then_forward (X : category R) :
    (absorption R).inv.app X ≫ (absorption R).hom.app X =
      𝟙 ((infinityFunctor R).obj X) :=
  (absorption R).inv_hom_id_app X

/-- The original forward followed by return is the actual chosen biproduct identity. -/
theorem forward_then_return (X : category R) :
    (absorption R).hom.app X ≫ (absorption R).inv.app X =
      𝟙 (X ⊞ (infinityFunctor R).obj X) :=
  (absorption R).hom_inv_id_app X

/-- The whole pointwise matrix square uses the same original projective morphism. -/
theorem original_map_square {X Y : category R} (v : X ⟶ Y) :
    biprod.map v ((infinityFunctor R).map v) ≫ (absorption R).hom.app Y =
      (absorption R).hom.app X ≫ (infinityFunctor R).map v :=
  (absorption R).hom.naturality v

/-- The exact same original inclusion/projection row is a canonical cofiber sequence. -/
theorem original_cofiber_row (X : category R) :
    letI : WaldhausenCategoryWithoutGluing (category R) := ExactCategory.waldhausenCategory (category R)
    IsCofiberSequence ((sumBicone R).inl.app X) ((sumBicone R).snd.app X) :=
  sum_cofiber_sequence R X

end FGProjectiveCat.ConeRing.AbsorptionTests

end
