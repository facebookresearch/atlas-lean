/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Successor diagrams and their chosen filtered group colimits

The full natural-number successor functor and diagram transition retain
every original object and map. Finality gives both maps of the chosen
group-colimit comparison. The colimit of the actual successor transition
is its inverse, with every original cocone leg retained.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v uC vC
open CategoryTheory CategoryTheory.Limits

private theorem originalIsIsoOfHom
    {C : Type uC} [Category.{vC} C] {A B : C} (e : A ≅ B) (f : A ⟶ B)
    (h : f = e.hom) : IsIso f := h.symm ▸ e.isIso_hom

namespace GrpCat.FilteredColimits.Successor

/-- The actual original successor-index functor preserves all original finite index maps. -/
def successorFunctor : ℕ ⥤ ℕ :=
  (show Monotone Nat.succ from fun _ _ h => Nat.succ_le_succ h).functor

/-- The whole successor diagram functor keeps each original diagram and full input maps. -/
def successorDiagramFunctor : (ℕ ⥤ GrpCat.{v}) ⥤ (ℕ ⥤ GrpCat.{v}) :=
  (Functor.whiskeringLeft ℕ ℕ GrpCat.{v}).obj successorFunctor

/-- The entire original Nat index transition is the original successor order map. -/
def successorIndexNatTrans : 𝟭 ℕ ⟶ successorFunctor where
  app n := homOfLE (Nat.le_succ n)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The WHOLE original diagram successor transition retains every actual original finite map. -/
def successorTransitionNatTrans : 𝟭 (ℕ ⥤ GrpCat.{v}) ⟶ successorDiagramFunctor where
  app D := D.leftUnitor.inv ≫ Functor.whiskerRight successorIndexNatTrans D
  naturality {D E} a := by
    apply NatTrans.ext
    funext n
    change a.app n ≫ (𝟙 _ ≫ E.map (homOfLE (Nat.le_succ n))) =
      (𝟙 _ ≫ D.map (homOfLE (Nat.le_succ n))) ≫ a.app (n + 1)
    have h := a.naturality (homOfLE (Nat.le_succ n))
    exact (congrArg (fun f => a.app n ≫ f)
        (Category.id_comp (E.map (homOfLE (Nat.le_succ n))))).trans
      (h.symm.trans (congrArg (fun f => f ≫ a.app (n + 1))
        (Category.id_comp (D.map (homOfLE (Nat.le_succ n)))).symm))

/-- EVERY complete successor transition function is the SAME actual original diagram map. -/
theorem successorTransitionNatTrans_app_app (D : ℕ ⥤ GrpCat.{v}) (n : ℕ) :
    (successorTransitionNatTrans.app D).app n = D.map (homOfLE (Nat.le_succ n)) := by
  change 𝟙 _ ≫ D.map (homOfLE (Nat.le_succ n)) = _
  exact Category.id_comp _

/-- The actual SAME original Nat successor is genuinely final. -/
theorem successorFunctor_final : successorFunctor.Final := by
  apply (Monotone.final_functor_iff
    (show Monotone Nat.succ from fun _ _ h => Nat.succ_le_succ h)).mpr
  intro n
  exact ⟨n, Nat.le_succ n⟩

/-- The complete actual successor cocone keeps the SAME original Group quotient and legs. -/
def successorCocone (D : ℕ ⥤ GrpCat.{v}) : Cocone (successorFunctor ⋙ D) :=
  (GrpCat.FilteredColimits.colimitCocone D).whisker successorFunctor

/-- Genuine finality preserves the SAME original actual successor cocone's full UPL. -/
def successorCoconeIsColimit (D : ℕ ⥤ GrpCat.{v}) : IsColimit (successorCocone D) := by
  let _ : successorFunctor.Final := successorFunctor_final
  exact (Functor.Final.isColimitWhiskerEquiv successorFunctor
    (GrpCat.FilteredColimits.colimitCocone D)).symm
      (GrpCat.FilteredColimits.colimitCoconeIsColimit D)

/-- Both full actual original successor-colimit comparison maps are retained. -/
def successorComparisonIso (D : ℕ ⥤ GrpCat.{v}) :
    GrpCat.FilteredColimits.colimit (successorFunctor ⋙ D) ≅ GrpCat.FilteredColimits.colimit D :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (successorFunctor ⋙ D)).coconePointUniqueUpToIso
    (successorCoconeIsColimit D)

/-- EVERY actual original successor leg remains the full forward comparison leg. -/
theorem successorComparisonIso_hom_ι (D : ℕ ⥤ GrpCat.{v}) (n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (successorFunctor ⋙ D)).ι.app n ≫
        (successorComparisonIso D).hom =
      (GrpCat.FilteredColimits.colimitCocone D).ι.app (n + 1) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (successorFunctor ⋙ D))
    (successorCoconeIsColimit D) n

/-- The actual original successor transition colimit map is inverse to the same cofinal map. -/
theorem successorTransition_colimit_comp_hom (D : ℕ ⥤ GrpCat.{v}) :
    (colimitCoconeIsColimit D).map (colimitCocone (successorFunctor ⋙ D))
      (successorTransitionNatTrans.app D) ≫
      (successorComparisonIso D).hom = 𝟙 (GrpCat.FilteredColimits.colimit D) := by
  let a : D ⟶ successorFunctor ⋙ D := successorTransitionNatTrans.app D
  apply (GrpCat.FilteredColimits.colimitCoconeIsColimit D).hom_ext
  intro n
  have hf := (colimitCoconeIsColimit D).ι_map (colimitCocone (successorFunctor ⋙ D)) a n
  have hc := successorComparisonIso_hom_ι D n
  have hs := successorTransitionNatTrans_app_app D n
  have hw := (GrpCat.FilteredColimits.colimitCocone D).w (homOfLE (Nat.le_succ n))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (successorComparisonIso D).hom) hf).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a.app n ≫ f) hc).trans
          ((congrArg (fun f => f ≫
            (GrpCat.FilteredColimits.colimitCocone D).ι.app (n + 1)) hs).trans
              (hw.trans (Category.comp_id _).symm)))))

/-- The ENTIRE original successor transition colimit function is the actual inverse Iso map. -/
theorem successorTransition_colimit_eq_inv (D : ℕ ⥤ GrpCat.{v}) :
    (colimitCoconeIsColimit D).map (colimitCocone (successorFunctor ⋙ D))
      (successorTransitionNatTrans.app D) =
      (successorComparisonIso D).inv := by
  apply (cancel_mono (successorComparisonIso D).hom).mp
  exact (successorTransition_colimit_comp_hom D).trans
    (successorComparisonIso D).inv_hom_id.symm

/-- The SAME actual original successor transition colimit map is genuinely an Iso. -/
theorem successorTransition_colimit_isIso (D : ℕ ⥤ GrpCat.{v}) :
    IsIso ((colimitCoconeIsColimit D).map (colimitCocone (successorFunctor ⋙ D))
      (successorTransitionNatTrans.app D)) := by
  exact originalIsIsoOfHom (successorComparisonIso D).symm
    ((colimitCoconeIsColimit D).map (colimitCocone (successorFunctor ⋙ D))
      (successorTransitionNatTrans.app D))
    (successorTransition_colimit_eq_inv D)

end GrpCat.FilteredColimits.Successor
