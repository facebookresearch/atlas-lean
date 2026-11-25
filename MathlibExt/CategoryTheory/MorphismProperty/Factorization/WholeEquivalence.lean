/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeFunctor
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

/-!
# One complete original factorization comparison through the actual equivalence

The full diagram of source, original selected middle and target is compared
through the given actual counit. Both factor maps, all three endpoint fields,
every arbitrary Arrow square and the exact caller composite are retained.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory CategoryTheory.ComposableArrows

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty D} [W₁.RespectsIso] [W₂.RespectsIso]

/-- The whole original two-factor diagram is compared at once by the actual middle counit. -/
def originalWholeFactorizationEquivalenceIso (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) :
    (data.ofEquivalence e).originalFactorizationFunctor ⋙ e.functor.mapComposableArrows 2 ≅
      e.functor.mapArrow ⋙ data.originalFactorizationFunctor :=
  NatIso.ofComponents (fun a =>
    isoMk₂ (Iso.refl _) ((data.ofEquivalenceZComparisonIso e).app a) (Iso.refl _)
      (by
        change e.functor.map ((data.ofEquivalence e).i.app a) ≫
            (data.ofEquivalenceZComparisonIso e).hom.app a =
          𝟙 (e.functor.obj a.left) ≫ data.i.app (e.functor.mapArrow.obj a)
        exact (data.ofEquivalence_mapped_i e a).trans (Category.id_comp _).symm)
      (by
        change e.functor.map ((data.ofEquivalence e).p.app a) ≫ 𝟙 _ =
          (data.ofEquivalenceZComparisonIso e).hom.app a ≫
            data.p.app (e.functor.mapArrow.obj a)
        exact (Category.comp_id _).trans (data.ofEquivalence_mapped_p e a).symm))
    (by
      intro a b φ
      apply hom_ext₂
      · change e.functor.map φ.left ≫ 𝟙 _ = 𝟙 _ ≫ e.functor.map φ.left
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact (data.ofEquivalenceZComparisonIso e).hom.naturality φ
      · change e.functor.map φ.right ≫ 𝟙 _ = 𝟙 _ ≫ e.functor.map φ.right
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- All forward fields retain the original source identity, counit and target identity. -/
theorem originalWholeFactorizationEquivalenceIso_hom_fields
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (a : Arrow C) :
    ((data.originalWholeFactorizationEquivalenceIso e).hom.app a).app 0 =
        𝟙 (e.functor.obj a.left) ∧
      ((data.originalWholeFactorizationEquivalenceIso e).hom.app a).app 1 =
        (data.ofEquivalenceZComparisonIso e).hom.app a ∧
      ((data.originalWholeFactorizationEquivalenceIso e).hom.app a).app 2 =
        𝟙 (e.functor.obj a.right) := ⟨rfl, rfl, rfl⟩

/-- All three inverse fields retain the two original caller identities and exact inverse counit. -/
theorem originalWholeFactorizationEquivalenceIso_inv_fields
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (a : Arrow C) :
    ((data.originalWholeFactorizationEquivalenceIso e).inv.app a).app 0 =
        𝟙 (e.functor.obj a.left) ∧
      ((data.originalWholeFactorizationEquivalenceIso e).inv.app a).app 1 =
        (data.ofEquivalenceZComparisonIso e).inv.app a ∧
      ((data.originalWholeFactorizationEquivalenceIso e).inv.app a).app 2 =
        𝟙 (e.functor.obj a.right) := ⟨rfl, rfl, rfl⟩

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
