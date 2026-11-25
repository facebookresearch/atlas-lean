/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

/-!
# Whole factor Arrows under the supplied equivalence

The complete comparison is obtained from the original intermediate counit.
Both factor Arrows retain the original caller endpoint and original map.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe uC vC uD vD
open CategoryTheory

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty D} [W₁.RespectsIso] [W₂.RespectsIso]

/-- The entire mapped first factor Arrow is the same original first factor through its counit. -/
def ofEquivalenceLeftArrowIso (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    Arrow.mk (e.functor.map ((data.ofEquivalence e).i.app a)) ≅
      Arrow.mk (data.i.app (e.functor.mapArrow.obj a)) :=
  Arrow.isoMk (Iso.refl _) ((data.ofEquivalenceZComparisonIso e).app a)
    (by
      change 𝟙 (e.functor.obj a.left) ≫ data.i.app (e.functor.mapArrow.obj a) =
        e.functor.map ((data.ofEquivalence e).i.app a) ≫
          (data.ofEquivalenceZComparisonIso e).hom.app a
      rw [Category.id_comp]
      exact (data.ofEquivalence_mapped_i e a).symm)

/-- The entire mapped second factor Arrow is the same original second factor through its counit. -/
def ofEquivalenceRightArrowIso (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (a : Arrow C) :
    Arrow.mk (e.functor.map ((data.ofEquivalence e).p.app a)) ≅
      Arrow.mk (data.p.app (e.functor.mapArrow.obj a)) :=
  Arrow.isoMk ((data.ofEquivalenceZComparisonIso e).app a) (Iso.refl _)
    (by
      change (data.ofEquivalenceZComparisonIso e).hom.app a ≫
        data.p.app (e.functor.mapArrow.obj a) =
          e.functor.map ((data.ofEquivalence e).p.app a) ≫ 𝟙 (e.functor.obj a.right)
      exact (data.ofEquivalence_mapped_p e a).trans
        (Category.comp_id (e.functor.map ((data.ofEquivalence e).p.app a))).symm)

/-- The first-factor Arrow retains the original caller identity and actual middle counit. -/
theorem ofEquivalenceLeftArrowIso_hom_fields
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (a : Arrow C) :
    (data.ofEquivalenceLeftArrowIso e a).hom.left = 𝟙 (e.functor.obj a.left) ∧
      (data.ofEquivalenceLeftArrowIso e a).hom.right =
        (data.ofEquivalenceZComparisonIso e).hom.app a := ⟨rfl, rfl⟩

/-- The second-factor Arrow retains the actual middle counit and original caller identity. -/
theorem ofEquivalenceRightArrowIso_hom_fields
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (a : Arrow C) :
    (data.ofEquivalenceRightArrowIso e a).hom.left =
        (data.ofEquivalenceZComparisonIso e).hom.app a ∧
      (data.ofEquivalenceRightArrowIso e a).hom.right = 𝟙 (e.functor.obj a.right) := ⟨rfl, rfl⟩

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
