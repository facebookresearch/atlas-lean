/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Products.Basic

section

-- Author: @toskua, Codex


/-!
# Actual evaluation comparisons for flipped framing parameters

Evaluation of a flipped bifunctor retains the original fixed-variable functor. Flipping
a constant-valued prolongation retains the original coefficient functor. The complete
natural comparisons in both directions use the original identity component maps.
-/

@[expose] public section

set_option autoImplicit false

universe uC uD uE vC vD vE

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]

/-- The actual evaluated flipped bifunctor is naturally the original fixed-degree functor. -/
def flippedEvaluationIso (F : D ⥤ C ⥤ E) (j : D) :
    F.flip ⋙ (evaluation D E).obj j ≅ F.obj j where
  hom := { app X := 𝟙 ((F.obj j).obj X) }
  inv := { app X := 𝟙 ((F.obj j).obj X) }

/-- The full forward comparison retains the original coefficient identity. -/
theorem flippedEvaluationIso_hom_app (F : D ⥤ C ⥤ E) (j : D) (X : C) :
    (flippedEvaluationIso F j).hom.app X = 𝟙 ((F.obj j).obj X) := rfl

/-- The full inverse comparison retains the original coefficient identity. -/
theorem flippedEvaluationIso_inv_app (F : D ⥤ C ⥤ E) (j : D) (X : C) :
    (flippedEvaluationIso F j).inv.app X = 𝟙 ((F.obj j).obj X) := rfl

/-- A fixed degree of the flipped constant prolongation is the original coefficient functor. -/
def constFlippedObjIso (F : C ⥤ E) (j : D) :
    (F ⋙ Functor.const D).flip.obj j ≅ F where
  hom := { app X := 𝟙 (F.obj X) }
  inv := { app X := 𝟙 (F.obj X) }

/-- The full forward constant comparison uses the same original identity map. -/
theorem constFlippedObjIso_hom_app (F : C ⥤ E) (j : D) (X : C) :
    (constFlippedObjIso F j).hom.app X = 𝟙 (F.obj X) := rfl

/-- The full inverse constant comparison uses the same original identity map. -/
theorem constFlippedObjIso_inv_app (F : C ⥤ E) (j : D) (X : C) :
    (constFlippedObjIso F j).inv.app X = 𝟙 (F.obj X) := rfl

/-- An actual fixed-degree comparison retains its full original component map after evaluation. -/
theorem flippedEvaluationIso_comp_hom_app (F : D ⥤ C ⥤ E) (G : C ⥤ E) (j : D)
    (e : F.obj j ≅ (G ⋙ Functor.const D).flip.obj j) (X : C) :
    (flippedEvaluationIso F j ≪≫ e ≪≫ constFlippedObjIso G j).hom.app X = e.hom.app X := by
  simp only [Iso.trans_hom, NatTrans.comp_app, flippedEvaluationIso_hom_app,
    constFlippedObjIso_hom_app]
  exact (Category.id_comp (e.hom.app X ≫ 𝟙 (G.obj X))).trans (Category.comp_id (e.hom.app X))

/-- The inverse evaluation presentation retains the full original comparison component. -/
theorem constFlippedObjIso_comp_hom_app (F : D ⥤ C ⥤ E) (G : C ⥤ E) (j : D)
    (e : (G ⋙ Functor.const D).flip.obj j ≅ F.obj j) (X : C) :
    ((constFlippedObjIso G j).symm ≪≫ e ≪≫ (flippedEvaluationIso F j).symm).hom.app X =
      e.hom.app X := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, flippedEvaluationIso_inv_app,
    constFlippedObjIso_inv_app, Category.id_comp, Category.comp_id]

end CategoryTheory.Functor

end
end
