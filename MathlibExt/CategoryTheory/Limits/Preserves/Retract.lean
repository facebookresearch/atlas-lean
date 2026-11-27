/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

universe w' w v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]
variable {K : J ⥤ C}
variable {F G : C ⥤ D}

open Category

/-- If `F` is a retract of `G` in the functor category and `G` preserves the colimit of
`K`, then `F` preserves the colimit of `K`. -/
theorem preservesColimit_of_retract (h : Retract F G) [PreservesColimit K G] :
    PreservesColimit K F where
  preserves := fun {c} hc => by
    let cF : Cocone (K ⋙ F) := F.mapCocone c
    let cG : Cocone (K ⋙ G) := G.mapCocone c
    let cGcol : IsColimit cG := isColimitOfPreserves G hc
    let αr : (K ⋙ G) ⟶ (K ⋙ F) := Functor.whiskerLeft K h.r
    have h_pt : h.i.app c.pt ≫ h.r.app c.pt = 𝟙 cF.pt :=
      NatTrans.congr_app h.retract c.pt
    have h_obj : ∀ j : J, h.i.app (K.obj j) ≫ h.r.app (K.obj j) = 𝟙 ((K ⋙ F).obj j) :=
      fun j => NatTrans.congr_app h.retract (K.obj j)
    have hI_leg : ∀ j : J,
        cF.ι.app j ≫ h.i.app c.pt =
          (Functor.whiskerLeft K h.i).app j ≫ cG.ι.app j := by
      intro j
      change F.map (c.ι.app j) ≫ h.i.app c.pt = h.i.app (K.obj j) ≫ G.map (c.ι.app j)
      exact h.i.naturality (c.ι.app j)
    have hR_leg : ∀ j : J,
        cG.ι.app j ≫ h.r.app c.pt =
          αr.app j ≫ cF.ι.app j := by
      intro j
      change G.map (c.ι.app j) ≫ h.r.app c.pt = h.r.app (K.obj j) ≫ F.map (c.ι.app j)
      exact h.r.naturality (c.ι.app j)
    refine ⟨{
      desc := fun s => h.i.app c.pt ≫ cGcol.map s αr
      fac := fun s j => by
        calc cF.ι.app j ≫ h.i.app c.pt ≫ cGcol.map s αr
            = (cF.ι.app j ≫ h.i.app c.pt) ≫ cGcol.map s αr := by
              exact (Category.assoc _ _ _).symm
          _ = ((Functor.whiskerLeft K h.i).app j ≫ cG.ι.app j) ≫ cGcol.map s αr := by
              exact congrArg (· ≫ cGcol.map s αr) (hI_leg j)
          _ = (Functor.whiskerLeft K h.i).app j ≫ (cG.ι.app j ≫ cGcol.map s αr) := by
              exact Category.assoc _ _ _
          _ = (Functor.whiskerLeft K h.i).app j ≫ (αr.app j ≫ s.ι.app j) := by
              exact congrArg ((Functor.whiskerLeft K h.i).app j ≫ ·) (cGcol.ι_map s αr j)
          _ = ((Functor.whiskerLeft K h.i).app j ≫ αr.app j) ≫ s.ι.app j := by
              exact (Category.assoc _ _ _).symm
          _ = s.ι.app j := by
              have h_pair : (Functor.whiskerLeft K h.i).app j ≫ αr.app j = 𝟙 _ := by
                calc (Functor.whiskerLeft K h.i).app j ≫ αr.app j
                    = h.i.app (K.obj j) ≫ h.r.app (K.obj j) := rfl
                  _ = 𝟙 _ := h_obj j
              calc ((Functor.whiskerLeft K h.i).app j ≫ αr.app j) ≫ s.ι.app j
                  = 𝟙 _ ≫ s.ι.app j := by exact congrArg (· ≫ s.ι.app j) h_pair
                _ = s.ι.app j := by exact Category.id_comp _
      uniq := fun s m hm => by
        have hmG : ∀ j,
            cG.ι.app j ≫ (h.r.app c.pt ≫ m) = αr.app j ≫ s.ι.app j := by
          intro j
          calc cG.ι.app j ≫ (h.r.app c.pt ≫ m)
              = (cG.ι.app j ≫ h.r.app c.pt) ≫ m := by
                exact (Category.assoc _ _ _).symm
            _ = (αr.app j ≫ cF.ι.app j) ≫ m := by
                exact congrArg (· ≫ m) (hR_leg j)
            _ = αr.app j ≫ (cF.ι.app j ≫ m) := by
                exact Category.assoc _ _ _
            _ = αr.app j ≫ s.ι.app j := by
                exact congrArg (αr.app j ≫ ·) (hm j)
        have h_eq : h.r.app c.pt ≫ m = cGcol.map s αr := by
          apply cGcol.hom_ext
          intro j
          exact (hmG j).trans (cGcol.ι_map s αr j).symm
        calc m = 𝟙 cF.pt ≫ m := by
              exact (Category.id_comp _).symm
          _ = (h.i.app c.pt ≫ h.r.app c.pt) ≫ m := by
              -- close reflexive equality via pointwise retract identity
              exact congrArg (· ≫ m) h_pt.symm
          _ = h.i.app c.pt ≫ (h.r.app c.pt ≫ m) := by
              exact Category.assoc _ _ _
          _ = h.i.app c.pt ≫ cGcol.map s αr := by
              exact congrArg (h.i.app c.pt ≫ ·) h_eq
    }⟩

/-- Shape-wide version: if `F` is a retract of `G` and `G` preserves colimits of shape `J`,
then `F` preserves colimits of shape `J`. -/
theorem preservesColimitsOfShape_of_retract {J : Type w} [Category.{w'} J] {F G : C ⥤ D}
    (h : Retract F G) [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J F where
  preservesColimit := fun {K} => by
    have : PreservesColimit K G := inferInstance
    exact preservesColimit_of_retract (K := K) h

end Limits
end CategoryTheory
