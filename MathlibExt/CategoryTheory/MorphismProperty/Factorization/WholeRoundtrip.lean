/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeFunctor
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.RoundtripData

/-!
# Whole original factorization diagrams under the actual roundtrip

The existing original middle-unit comparison identifies both complete factor
diagrams, with identity maps on the unchanged source and target. The inverse
and every arbitrary Arrow square retain the same original factor maps.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD

open CategoryTheory CategoryTheory.ComposableArrows

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {P Q : MorphismProperty C} [P.RespectsIso] [Q.RespectsIso]

/-- The actual original unit compares both entire two-factor diagrams simultaneously. -/
def originalWholeFactorizationRoundtripIso (data : FunctorialFactorizationData P Q)
    (e : C ≌ D) :
    ((data.ofEquivalence e.symm).ofEquivalence e).originalFactorizationFunctor ≅
      data.originalFactorizationFunctor :=
  NatIso.ofComponents (fun a =>
    isoMk₂ (Iso.refl _) ((data.ofEquivalenceRoundtripComparisonIso e).app a) (Iso.refl _)
      (by
        change ((data.ofEquivalence e.symm).ofEquivalence e).i.app a ≫
            (data.ofEquivalenceRoundtripComparisonIso e).hom.app a = 𝟙 _ ≫ data.i.app a
        exact (data.ofEquivalence_roundtrip_i e a).trans (Category.id_comp _).symm)
      (by
        change ((data.ofEquivalence e.symm).ofEquivalence e).p.app a ≫ 𝟙 _ =
          (data.ofEquivalenceRoundtripComparisonIso e).hom.app a ≫ data.p.app a
        exact (Category.comp_id _).trans (data.ofEquivalence_roundtrip_p e a).symm))
    (by
      intro a b φ
      apply hom_ext₂
      · exact (Category.comp_id φ.left).trans (Category.id_comp φ.left).symm
      · exact (data.ofEquivalenceRoundtripComparisonIso e).hom.naturality φ
      · exact (Category.comp_id φ.right).trans (Category.id_comp φ.right).symm)

/-- All forward fields keep the original endpoints and actual full middle unit. -/
theorem originalWholeFactorizationRoundtripIso_hom_fields
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (a : Arrow C) :
    ((data.originalWholeFactorizationRoundtripIso e).hom.app a).app 0 = 𝟙 a.left ∧
      ((data.originalWholeFactorizationRoundtripIso e).hom.app a).app 1 =
        (data.ofEquivalenceRoundtripComparisonIso e).hom.app a ∧
      ((data.originalWholeFactorizationRoundtripIso e).hom.app a).app 2 = 𝟙 a.right :=
  ⟨rfl, rfl, rfl⟩

/-- All inverse fields retain the same endpoints and original inverse middle unit. -/
theorem originalWholeFactorizationRoundtripIso_inv_fields
    (data : FunctorialFactorizationData P Q) (e : C ≌ D) (a : Arrow C) :
    ((data.originalWholeFactorizationRoundtripIso e).inv.app a).app 0 = 𝟙 a.left ∧
      ((data.originalWholeFactorizationRoundtripIso e).inv.app a).app 1 =
        (data.ofEquivalenceRoundtripComparisonIso e).inv.app a ∧
      ((data.originalWholeFactorizationRoundtripIso e).inv.app a).app 2 = 𝟙 a.right :=
  ⟨rfl, rfl, rfl⟩

/-- The same entire forward diagram comparison preserves every original Arrow square. -/
theorem originalWholeFactorizationRoundtripIso_hom_naturality
    (data : FunctorialFactorizationData P Q) (e : C ≌ D)
    {a b : Arrow C} (φ : a ⟶ b) :
    ((data.ofEquivalence e.symm).ofEquivalence e).originalFactorizationFunctor.map φ ≫
        (data.originalWholeFactorizationRoundtripIso e).hom.app b =
      (data.originalWholeFactorizationRoundtripIso e).hom.app a ≫
        data.originalFactorizationFunctor.map φ :=
  (data.originalWholeFactorizationRoundtripIso e).hom.naturality φ

/-- The complete inverse comparison preserves every original Arrow square as well. -/
theorem originalWholeFactorizationRoundtripIso_inv_naturality
    (data : FunctorialFactorizationData P Q) (e : C ≌ D)
    {a b : Arrow C} (φ : a ⟶ b) :
    data.originalFactorizationFunctor.map φ ≫
        (data.originalWholeFactorizationRoundtripIso e).inv.app b =
      (data.originalWholeFactorizationRoundtripIso e).inv.app a ≫
        ((data.ofEquivalence e.symm).ofEquivalence e).originalFactorizationFunctor.map φ :=
  (data.originalWholeFactorizationRoundtripIso e).inv.naturality φ

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
