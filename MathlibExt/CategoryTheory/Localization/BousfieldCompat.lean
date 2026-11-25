/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

-- BACKPORT: Extracted from PR #42860 head `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
-- path `Mathlib/CategoryTheory/Localization/Bousfield.lean`,
-- blob `b32fa01cee9e849f3f39eb93e08aa4b338a34892`, authors Junyan Xu.
-- See `BACKPORTS.md` for copied surface, adaptations, and upgrade-removal steps.

public import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Bousfield localization: locality from colimits (backport)

Backports `ObjectProperty.isLocal_of_isColimit` from upstream PR #42860
(head `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
path `Mathlib/CategoryTheory/Localization/Bousfield.lean`,
blob `b32fa01cee9e849f3f39eb93e08aa4b338a34892`).
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

namespace ObjectProperty

variable (P : ObjectProperty C)

open Limits in
open Category in
-- Note: for lcF, only lcF.hom_ext is used
theorem isLocal_of_isColimit {F G : D ⥤ C} {cF : Cocone F} {cG : Cocone G}
    (lcF : IsColimit cF) (lcG : IsColimit cG) (φ : F ⟶ G) (ψ : cF.pt ⟶ cG.pt)
    (comm : φ ≫ cG.ι = cF.ι ≫ (Functor.const D).map ψ) (loc : ∀ d, P.isLocal (φ.app d)) :
    P.isLocal ψ := fun X hX ↦ by
  refine ⟨fun χ₁ χ₂ eq ↦ lcG.hom_ext fun d ↦ (loc d X hX).injective ?_, fun χ ↦ ?_⟩
  · simp_rw [← Category.assoc, ← NatTrans.comp_app, comm, NatTrans.comp_app, Category.assoc]
    exact congr(_ ≫ $eq)
  let c : Cocone G := { pt := X, ι :=
    { app d := (Equiv.ofBijective _ (loc d X hX)).symm (cF.ι.app d ≫ χ),
      naturality d₁ d₂ f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, comp_id,
          Equiv.eq_symm_apply, Equiv.ofBijective_apply]
        rw [← φ.naturality_assoc f, Equiv.ofBijective_apply_symm_apply (_ ≫ ·), cF.w_assoc] } }
  refine ⟨lcG.desc c, lcF.hom_ext fun d ↦ ?_⟩
  rw [← Category.assoc]
  refine congr(($comm.symm).app _ ≫ _).trans ?_
  simpa using Equiv.ofBijective_apply_symm_apply ..

end ObjectProperty

end CategoryTheory

end
