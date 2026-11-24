/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# A copointed adjunction over the original object

A natural map from a left adjoint to the identity lifts that left adjoint
to the slice of each supplied object. The actual right adjoint is the
pullback of the original right-adjoint image along the transpose of the
same copoint. All maps are the native pullback maps; no model structure
or fibrancy hypothesis is involved.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    {L R : C ⥤ C}

/-- The supplied copoint gives the original left adjoint its literal base map. -/
def copointedOverLeft (ε : L ⟶ 𝟭 C) (B : C) : Over B ⥤ Over B where
  obj X := Over.mk (ε.app X.left ≫ X.hom)
  map f := Over.homMk (L.map f.left) (by
    change L.map f.left ≫ ε.app _ ≫ _ = ε.app _ ≫ _
    rw [← Category.assoc, ε.naturality, Category.assoc]
    change ε.app _ ≫ f.left ≫ _ = ε.app _ ≫ _
    rw [Over.w f])
  map_id X := by apply Over.OverMorphism.ext; exact L.map_id X.left
  map_comp f g := by apply Over.OverMorphism.ext; exact L.map_comp f.left g.left

/-- The actual right carrier is pulled back along the original transposed copoint. -/
def copointedOverRight (a : L ⊣ R) (ε : L ⟶ 𝟭 C) (B : C) : Over B ⥤ Over B :=
  Over.post R ⋙ Over.pullback (a.homEquiv B B (ε.app B))

/-- Whole original over-maps transpose through the same adjunction and supplied pullback. -/
def copointedOverHomEquiv (a : L ⊣ R) (ε : L ⟶ 𝟭 C) (B : C)
    (X Y : Over B) :
    ((copointedOverLeft ε B).obj X ⟶ Y) ≃
      (X ⟶ (copointedOverRight a ε B).obj Y) where
  toFun f := Over.homMk
    (pullback.lift (a.homEquiv X.left Y.left f.left) X.hom (by
      let f₀ : L.obj X.left ⟶ Y.left := f.left
      change a.homEquiv X.left Y.left f₀ ≫ R.map Y.hom =
        X.hom ≫ a.homEquiv B B (ε.app B)
      rw [← a.homEquiv_naturality_right, ← a.homEquiv_naturality_left]
      exact congrArg (a.homEquiv X.left B)
        ((Over.w f).trans (ε.naturality X.hom).symm)))
    (pullback.lift_snd _ _ _)
  invFun g := Over.homMk
    ((a.homEquiv X.left Y.left).symm (g.left ≫ pullback.fst _ _)) (by
      let t : pullback (R.map Y.hom) (a.homEquiv B B (ε.app B)) ⟶ R.obj Y.left :=
        pullback.fst _ _
      let b : pullback (R.map Y.hom) (a.homEquiv B B (ε.app B)) ⟶ B := pullback.snd _ _
      let g₀ : X.left ⟶ pullback (R.map Y.hom) (a.homEquiv B B (ε.app B)) := g.left
      change (a.homEquiv X.left Y.left).symm (g₀ ≫ t) ≫ Y.hom = ε.app X.left ≫ X.hom
      apply (a.homEquiv X.left B).injective
      rw [a.homEquiv_naturality_right, Equiv.apply_symm_apply]
      calc
        (g₀ ≫ t) ≫ R.map Y.hom = g₀ ≫ b ≫ a.homEquiv B B (ε.app B) := by
          rw [Category.assoc, show t ≫ R.map Y.hom = b ≫
            a.homEquiv B B (ε.app B) from pullback.condition]
        _ = X.hom ≫ a.homEquiv B B (ε.app B) := by rw [← Category.assoc, show g₀ ≫
          b = X.hom from Over.w g]
        _ = a.homEquiv X.left B (L.map X.hom ≫ ε.app B) :=
          (a.homEquiv_naturality_left X.hom (ε.app B)).symm
        _ = a.homEquiv X.left B (ε.app X.left ≫ X.hom) :=
          congrArg (a.homEquiv X.left B) (ε.naturality X.hom))
  left_inv f := by
    apply Over.OverMorphism.ext
    let f₀ : L.obj X.left ⟶ Y.left := f.left
    exact (congrArg (a.homEquiv X.left Y.left).symm (pullback.lift_fst _ _ _)).trans
      ((a.homEquiv X.left Y.left).symm_apply_apply f₀)
  right_inv g := by
    apply Over.OverMorphism.ext
    let g₀ : X.left ⟶ pullback (R.map Y.hom) (a.homEquiv B B (ε.app B)) := g.left
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans
        ((a.homEquiv X.left Y.left).apply_symm_apply (g₀ ≫ pullback.fst _ _))
    · exact (pullback.lift_snd _ _ _).trans (Over.w g).symm

/-- The original copointed left adjoint and literal pullback right adjoint form an
adjunction in the same slice. -/
def copointedOver (a : L ⊣ R) (ε : L ⟶ 𝟭 C) (B : C) :
    copointedOverLeft ε B ⊣ copointedOverRight a ε B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := copointedOverHomEquiv a ε B
      homEquiv_naturality_left_symm := by
        intro X X' Y f g
        apply Over.OverMorphism.ext
        let t : pullback (R.map Y.hom) (a.homEquiv B B (ε.app B)) ⟶ R.obj Y.left := pullback.fst _ _
        let g₀ : X'.left ⟶ pullback (R.map Y.hom) (a.homEquiv B B (ε.app B)) := g.left
        change (a.homEquiv X.left Y.left).symm ((f.left ≫ g₀) ≫ t) =
          L.map f.left ≫ (a.homEquiv X'.left Y.left).symm (g₀ ≫ t)
        rw [Category.assoc, a.homEquiv_naturality_left_symm]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply Over.OverMorphism.ext
        let f₀ : L.obj X.left ⟶ Y.left := f.left
        let c := a.homEquiv B B (ε.app B)
        let t : pullback (R.map Y'.hom) c ⟶ R.obj Y'.left := pullback.fst _ _
        let b : pullback (R.map Y.hom) c ⟶ B := pullback.snd _ _
        let h : X.left ⟶ pullback (R.map Y.hom) c :=
          ((copointedOverHomEquiv a ε B X Y) f).left
        let k : pullback (R.map Y.hom) c ⟶ pullback (R.map Y'.hom) c :=
          ((copointedOverRight a ε B).map g).left
        apply pullback.hom_ext
        · have ht : k ≫ t = pullback.fst (R.map Y.hom) c ≫ R.map g.left :=
            pullback.lift_fst _ _ _
          have hh : h ≫ pullback.fst (R.map Y.hom) c = a.homEquiv X.left Y.left f₀ :=
            pullback.lift_fst _ _ _
          exact (pullback.lift_fst _ _ _).trans
            ((a.homEquiv_naturality_right f₀ g.left).trans
              ((congrArg (fun q => q ≫ R.map g.left) hh.symm).trans
                ((Category.assoc _ _ _).trans
                  ((congrArg (fun q => h ≫ q) ht.symm).trans (Category.assoc _ _ _).symm))))
        · exact (Over.w ((copointedOverHomEquiv a ε B X Y') (f ≫ g))).trans
            (Over.w ((copointedOverHomEquiv a ε B X Y) f ≫ (copointedOverRight a ε B).map g)).symm }

end CategoryTheory.Adjunction
