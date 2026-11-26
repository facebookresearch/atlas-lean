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
# Local morphisms induced on colimits

Let P be a property of objects of C. A morphism u : A → B is P-local when precomposition with
u gives a bijection Hom(B,X) → Hom(A,X) for every X satisfying P. Consider diagrams F,G : D ⥤
C with chosen colimit cocones, a natural transformation φ : F → G and a map ψ between their
colimit vertices that commutes with every cocone leg.

If each component φ_d is P-local, then ψ is P-local. Uniqueness follows by testing on all
colimit legs, and componentwise factorization assembles into a cocone that gives the required
factorization through the target colimit.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

namespace ObjectProperty

variable (P : ObjectProperty C)

open Limits in
open Category in
-- Note: for lcF, only lcF.hom_ext is used
/-- Locality of a map between colimit vertices.

Let P be an object property of C, φ : F → G a natural transformation and ψ : colim F → colim G
a map commuting with the legs of specified colimit cocones. If precomposition by every φ_d is
bijective on maps to each P-object X, then precomposition by ψ is bijective on maps to X. Thus
ψ is P-local. -/
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
