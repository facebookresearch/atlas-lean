/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.RoundtripFactors

/-!
# Complete original factorization recovery under the given roundtrip

The whole original Z comparison recovers both natural factor maps, their
entire factor Arrows and the same original caller factorization.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe uC vC uD vD
open CategoryTheory

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty C} [W₁.RespectsIso] [W₂.RespectsIso]

/-- The same original first map is recovered through the whole roundtrip intermediate. -/
theorem ofEquivalence_roundtrip_i (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    ((data.ofEquivalence e.symm).ofEquivalence e).i.app a ≫
      (data.ofEquivalenceRoundtripComparisonIso e).hom.app a = data.i.app a :=
  originalMiddleRoundtrip_i data.Z data.i e a

/-- The same original second map is recovered through the whole roundtrip intermediate. -/
theorem ofEquivalence_roundtrip_p (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    (data.ofEquivalenceRoundtripComparisonIso e).hom.app a ≫ data.p.app a =
      ((data.ofEquivalence e.symm).ofEquivalence e).p.app a :=
  originalMiddleRoundtrip_p data.Z data.p e a

/-- The inverse middle recovers the entire roundtrip first map. -/
theorem ofEquivalence_roundtrip_inverse_i (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    data.i.app a ≫ (data.ofEquivalenceRoundtripComparisonIso e).inv.app a =
      ((data.ofEquivalence e.symm).ofEquivalence e).i.app a := by
  rw [← data.ofEquivalence_roundtrip_i e a, Category.assoc,
    (data.ofEquivalenceRoundtripComparisonIso e).hom_inv_id_app, Category.comp_id]

/-- The inverse middle recovers the entire original second map. -/
theorem ofEquivalence_roundtrip_inverse_p (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    (data.ofEquivalenceRoundtripComparisonIso e).inv.app a ≫
      ((data.ofEquivalence e.symm).ofEquivalence e).p.app a = data.p.app a := by
  rw [← data.ofEquivalence_roundtrip_p e a, ← Category.assoc,
    (data.ofEquivalenceRoundtripComparisonIso e).inv_hom_id_app, Category.id_comp]

/-- The entire first-factor Arrow is compared through the given original middle unit. -/
def ofEquivalenceRoundtripLeftArrowIso (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    Arrow.mk (((data.ofEquivalence e.symm).ofEquivalence e).i.app a) ≅
      Arrow.mk (data.i.app a) :=
  Arrow.isoMk (Iso.refl _) ((data.ofEquivalenceRoundtripComparisonIso e).app a)
    (by
      change 𝟙 a.left ≫ data.i.app a =
        ((data.ofEquivalence e.symm).ofEquivalence e).i.app a ≫
          (data.ofEquivalenceRoundtripComparisonIso e).hom.app a
      exact (Category.id_comp (data.i.app a)).trans
        (data.ofEquivalence_roundtrip_i e a).symm)

/-- The entire second-factor Arrow is compared through the given original middle unit. -/
def ofEquivalenceRoundtripRightArrowIso (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    Arrow.mk (((data.ofEquivalence e.symm).ofEquivalence e).p.app a) ≅
      Arrow.mk (data.p.app a) :=
  Arrow.isoMk ((data.ofEquivalenceRoundtripComparisonIso e).app a) (Iso.refl _)
    (by
      change (data.ofEquivalenceRoundtripComparisonIso e).hom.app a ≫ data.p.app a =
        ((data.ofEquivalence e.symm).ofEquivalence e).p.app a ≫ 𝟙 a.right
      exact (data.ofEquivalence_roundtrip_p e a).trans
        (Category.comp_id (((data.ofEquivalence e.symm).ofEquivalence e).p.app a)).symm)

/-- The recovered original maps still factor exactly the caller's original Arrow. -/
theorem ofEquivalence_roundtrip_fac (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    ((data.ofEquivalence e.symm).ofEquivalence e).i.app a ≫
      ((data.ofEquivalence e.symm).ofEquivalence e).p.app a = a.hom :=
  ((data.ofEquivalence e.symm).ofEquivalence e).fac_app

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
