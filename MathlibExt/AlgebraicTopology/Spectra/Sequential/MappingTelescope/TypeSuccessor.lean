/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
import Mathlib.CategoryTheory.Limits.Final

/-!
# Successor transitions for the actual chosen Type colimits

The actual successor functor and index transformation are retained.
Mathlib's final-functor colimit isomorphism supplies the canonical
comparison. The colimit of the actual diagram transition is its inverse,
including the initial leg, and the complete transition is natural in
all input diagrams. No parallel cocone or comparison is constructed.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v
open CategoryTheory CategoryTheory.Limits

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.TypeSuccessorGeometry
open GrpCat.FilteredColimits.Successor
attribute [local instance] GrpCat.FilteredColimits.Successor.successorFunctor_final

/-- The whole original Type transition retains each actual original finite map. -/
def typeSuccessorTransitionNatTrans : 𝟭 (ℕ ⥤ Type v) ⟶
    (Functor.whiskeringLeft ℕ ℕ (Type v)).obj successorFunctor where
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

/-- Every ENTIRE Type transition function is the SAME original diagram map. -/
theorem typeSuccessorTransitionNatTrans_app_app (D : ℕ ⥤ Type v) (n : ℕ) :
    (typeSuccessorTransitionNatTrans.app D).app n = D.map (homOfLE (Nat.le_succ n)) := by
  change 𝟙 _ ≫ D.map (homOfLE (Nat.le_succ n)) = _
  exact Category.id_comp _

/-- The actual original Type transition colimit function is inverse to the cofinal comparison. -/
theorem typeSuccessorTransition_colimit_comp_hom (D : ℕ ⥤ Type v) :
    colim.map (typeSuccessorTransitionNatTrans.app D) ≫
      (Functor.Final.colimitIso successorFunctor D).hom = 𝟙 (colimit D) := by
  let a : D ⟶ successorFunctor ⋙ D := typeSuccessorTransitionNatTrans.app D
  apply colimit.hom_ext
  intro n
  have hf := colimit.ι_map a n
  have hc := Functor.Final.ι_colimitIso_hom successorFunctor D n
  have hs := typeSuccessorTransitionNatTrans_app_app D n
  have hw := (colimit.cocone D).w (homOfLE (Nat.le_succ n))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (Functor.Final.colimitIso successorFunctor D).hom) hf).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a.app n ≫ f) hc).trans
          ((congrArg (fun f => f ≫ colimit.ι D (n + 1)) hs).trans
            (hw.trans (Category.comp_id _).symm)))))

/-- The ENTIRE original Type transition colimit map is the actual inverse Iso function. -/
theorem typeSuccessorTransition_colimit_eq_inv (D : ℕ ⥤ Type v) :
    colim.map (typeSuccessorTransitionNatTrans.app D) =
      (Functor.Final.colimitIso successorFunctor D).inv := by
  apply (cancel_mono (Functor.Final.colimitIso successorFunctor D).hom).mp
  exact (typeSuccessorTransition_colimit_comp_hom D).trans
    (Functor.Final.colimitIso successorFunctor D).inv_hom_id.symm

/-- Every original index, including zero, uses the actual transition before its tail leg. -/
theorem typeSuccessorColimitIso_inv_ι_all (D : ℕ ⥤ Type v) (n : ℕ) :
    colimit.ι D n ≫ (Functor.Final.colimitIso successorFunctor D).inv =
      D.map (homOfLE (Nat.le_succ n)) ≫ colimit.ι (successorFunctor ⋙ D) n := by
  have h := (colimit.cocone D).w (homOfLE (Nat.le_succ n))
  exact (congrArg (fun f => f ≫ (Functor.Final.colimitIso successorFunctor D).inv) h.symm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun f => D.map (homOfLE (Nat.le_succ n)) ≫ f)
        (Functor.Final.ι_colimitIso_inv successorFunctor D n)))

/-- Every input diagram map preserves the whole actual successor transition on Type colimits. -/
theorem typeSuccessorTransition_colimit_naturality {D E : ℕ ⥤ Type v} (a : D ⟶ E) :
    colim.map a ≫ colim.map (typeSuccessorTransitionNatTrans.app E) =
      colim.map (typeSuccessorTransitionNatTrans.app D) ≫
        colim.map (Functor.whiskerLeft successorFunctor a) :=
  (colim.map_comp _ _).symm.trans
    ((colim.congr_map (typeSuccessorTransitionNatTrans.naturality a)).trans
      (colim.map_comp _ _))

end PointedCGWH.SequentialSpectrum.MappingTelescope.TypeSuccessorGeometry
