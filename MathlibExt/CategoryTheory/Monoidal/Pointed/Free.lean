/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.Pointed.Smash

/-!
# Strong monoidality of the free pointed-object functor

For an explicitly terminal object `P` in a cartesian closed symmetric
monoidal category, freely adjoining a point under `P` is strong monoidal
from the cartesian tensor to the generic smash product under `P`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory.Pointed

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasFiniteColimits C]

private noncomputable def costarSmashQuotient
    (P : C) (hP : IsTerminal P) (X Y : Under P) :
    X.right ⊗ Y.right ⟶ (((smash P hP).obj X).obj Y).right :=
  (smashPresentation P hP X Y).2.1.inl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem costarSmashQuotient_naturality
    (P : C) (hP : IsTerminal P)
    {X X' Y Y' : Under P} (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := smashMonoidalCategory P hP
    costarSmashQuotient P hP X Y ≫ (f ⊗ₘ g).right =
      (f.right ⊗ₘ g.right) ≫ costarSmashQuotient P hP X' Y' := by
  have hf : costarSmashQuotient P hP X Y ≫
      (((smash P hP).map f).app Y).right =
        (f.right ⊗ₘ 𝟙 Y.right) ≫ costarSmashQuotient P hP X' Y := by
    dsimp only [costarSmashQuotient, smash]
    exact PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP X Y).2.2 _ _ _
  have hg : costarSmashQuotient P hP X' Y ≫
      (((smash P hP).obj X').map g).right =
        (𝟙 X'.right ⊗ₘ g.right) ≫ costarSmashQuotient P hP X' Y' := by
    dsimp only [costarSmashQuotient, smash]
    exact PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP X' Y).2.2 _ _ _
  change costarSmashQuotient P hP X Y ≫
      ((((smash P hP).map f).app Y).right ≫
        (((smash P hP).obj X').map g).right) = _
  rw [← Category.assoc, hf, Category.assoc, hg,
    tensorHom_comp_tensorHom_assoc]
  simp

omit [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
private theorem costarSmashBraiding_hom_quotient
    (P : C) (hP : IsTerminal P) (X Y : Under P) :
    costarSmashQuotient P hP X Y ≫
        (smashBraiding P hP X Y).hom.right =
      (β_ X.right Y.right).hom ≫ costarSmashQuotient P hP Y X := by
  unfold smash
  let pointedProduct (P : C) : Under P ⥤ Under P ⥤ Under P :=
    { obj X :=
        { obj Y := Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
          map {Y Y'} g := Under.homMk (𝟙 X.right ⊗ₘ g.right) (by
            dsimp
            rw [CartesianMonoidalCategory.lift_map]
            simp only [Category.comp_id, Under.w])
          map_id Y := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
            exact MonoidalCategory.id_tensorHom_id _ _
          map_comp g h := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ (g.right ≫ h.right)) =
              (𝟙 X.right ⊗ₘ g.right) ≫ (𝟙 X.right ⊗ₘ h.right)
            rw [tensorHom_comp_tensorHom, Category.id_comp] }
      map {X X'} f :=
        { app Y := Under.homMk (f.right ⊗ₘ 𝟙 Y.right) (by
            dsimp
            rw [CartesianMonoidalCategory.lift_map]
            simp only [Category.comp_id, Under.w])
          naturality {Y Y'} g := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ g.right) ≫
                (f.right ⊗ₘ 𝟙 Y'.right) =
              (f.right ⊗ₘ 𝟙 Y.right) ≫
                (𝟙 X'.right ⊗ₘ g.right)
            rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
            simp }
      map_id X := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
        exact MonoidalCategory.id_tensorHom_id _ _
      map_comp f g := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change ((f.right ≫ g.right) ⊗ₘ 𝟙 Y.right) =
          (f.right ⊗ₘ 𝟙 Y.right) ≫ (g.right ⊗ₘ 𝟙 Y.right)
        rw [tensorHom_comp_tensorHom, Category.id_comp] }
  let wedgeToProduct (P : C) (hP : IsTerminal P) (X Y : Under P) :
      ((wedge P).obj X).obj Y ⟶ ((pointedProduct P).obj X).obj Y := by
    change Under.mk (X.hom ≫ pushout.inl X.hom Y.hom) ⟶
      Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
    let leftFace : X ⟶
          Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
        Under.homMk
          (CartesianMonoidalCategory.lift (𝟙 X.right)
            (hP.from X.right ≫ Y.hom)) (by
              apply CartesianMonoidalCategory.hom_ext
              · simp
              · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
                rw [← Category.assoc,
                  hP.hom_ext (X.hom ≫ hP.from X.right) (𝟙 P)]
                simp)
    let rightFace : Y ⟶
          Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
        Under.homMk
          (CartesianMonoidalCategory.lift
            (hP.from Y.right ≫ X.hom) (𝟙 Y.right)) (by
              apply CartesianMonoidalCategory.hom_ext
              · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
                rw [← Category.assoc,
                  hP.hom_ext (Y.hom ≫ hP.from Y.right) (𝟙 P)]
                simp
              · simp)
    exact Under.homMk
      (pushout.desc leftFace.right rightFace.right (by
        exact (Under.w leftFace).trans (Under.w rightFace).symm)) (by
          change (X.hom ≫ pushout.inl X.hom Y.hom) ≫
              pushout.desc leftFace.right rightFace.right _ =
            CartesianMonoidalCategory.lift X.hom Y.hom
          rw [Category.assoc, pushout.inl_desc]
          exact Under.w leftFace)
  let data :
      { e : ((smash P hP).obj X).obj Y ≅ ((smash P hP).obj Y).obj X //
        (smashPresentation P hP X Y).2.1.inl ≫ e.hom.right =
          CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.snd X.right Y.right)
              (CartesianMonoidalCategory.fst X.right Y.right) ≫
            (smashPresentation P hP Y X).2.1.inl } := by
    let swapMap (A B : Under P) :
        { f : ((smash P hP).obj A).obj B ⟶
            ((smash P hP).obj B).obj A //
          (smashPresentation P hP A B).2.1.inl ≫ f.right =
              (β_ A.right B.right).hom ≫
                (smashPresentation P hP B A).2.1.inl ∧
            (smashPresentation P hP A B).2.1.inr ≫ f.right =
              (smashPresentation P hP B A).2.1.inr } := by
      let pAB := smashPresentation P hP A B
      let pBA := smashPresentation P hP B A
      let wedgeSwap : ((wedge P).obj A).obj B ⟶ ((wedge P).obj B).obj A :=
        Under.homMk (pushoutSymmetry A.hom B.hom).hom (by
          dsimp [wedge]
          rw [Category.assoc, inl_comp_pushoutSymmetry_hom]
          exact pushout.condition.symm)
      let productSwap : ((pointedProduct P).obj A).obj B ⟶
          ((pointedProduct P).obj B).obj A :=
        Under.homMk (β_ A.right B.right).hom (by
          dsimp [pointedProduct]
          apply CartesianMonoidalCategory.hom_ext <;> simp)
      have hProd : pAB.1.right ≫ productSwap.right =
          wedgeSwap.right ≫ pBA.1.right := by
        dsimp only [pAB, pBA, smashPresentation]
        change pushout.desc _ _ _ ≫ (β_ A.right B.right).hom =
          (pushoutSymmetry A.hom B.hom).hom ≫ pushout.desc _ _ _
        apply pushout.hom_ext
        · rw [← Category.assoc, pushout.inl_desc]
          rw [← Category.assoc]
          simp only [inl_comp_pushoutSymmetry_hom, pushout.inr_desc]
          apply CartesianMonoidalCategory.hom_ext <;> simp
        · rw [← Category.assoc, pushout.inr_desc]
          rw [← Category.assoc]
          simp only [inr_comp_pushoutSymmetry_hom, pushout.inl_desc]
          apply CartesianMonoidalCategory.hom_ext <;> simp
      have hPoint : hP.from
            (((wedge P).obj A).obj B).right ≫ 𝟙 P =
          wedgeSwap.right ≫ hP.from
            (((wedge P).obj B).obj A).right :=
        hP.hom_ext _ _
      have hCompat : pAB.1.right ≫
            (productSwap.right ≫ pBA.2.1.inl) =
          hP.from (((wedge P).obj A).obj B).right ≫ pBA.2.1.inr := by
        rw [← Category.assoc, hProd, Category.assoc,
          pBA.2.1.condition, ← Category.assoc]
        simpa only [Category.assoc, Category.comp_id] using
          congrArg (fun k => k ≫ pBA.2.1.inr) hPoint.symm
      let f : ((smash P hP).obj A).obj B ⟶
          ((smash P hP).obj B).obj A := Under.homMk
        (PushoutCocone.IsColimit.desc pAB.2.2
          (productSwap.right ≫ pBA.2.1.inl) pBA.2.1.inr hCompat) (by
            exact PushoutCocone.IsColimit.inr_desc pAB.2.2 _ _ _)
      exact ⟨f, PushoutCocone.IsColimit.inl_desc pAB.2.2 _ _ _,
        PushoutCocone.IsColimit.inr_desc pAB.2.2 _ _ _⟩
    refine ⟨{
        hom := (swapMap X Y).1
        inv := (swapMap Y X).1
        hom_inv_id := by
          apply Under.UnderMorphism.ext
          change (swapMap X Y).1.right ≫ (swapMap Y X).1.right =
            𝟙 (smashPresentation P hP X Y).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP X Y).2.2
          · rw [← Category.assoc, (swapMap X Y).2.1,
              Category.assoc, (swapMap Y X).2.1]
            simp
          · rw [← Category.assoc, (swapMap X Y).2.2,
              (swapMap Y X).2.2]
            change (smashPresentation P hP X Y).2.1.inr =
              (smashPresentation P hP X Y).2.1.inr ≫
                𝟙 (smashPresentation P hP X Y).2.1.pt
            rw [Category.comp_id]
        inv_hom_id := by
          apply Under.UnderMorphism.ext
          change (swapMap Y X).1.right ≫ (swapMap X Y).1.right =
            𝟙 (smashPresentation P hP Y X).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP Y X).2.2
          · rw [← Category.assoc, (swapMap Y X).2.1,
              Category.assoc, (swapMap X Y).2.1]
            simp
          · rw [← Category.assoc, (swapMap Y X).2.2,
              (swapMap X Y).2.2]
            change (smashPresentation P hP Y X).2.1.inr =
              (smashPresentation P hP Y X).2.1.inr ≫
                𝟙 (smashPresentation P hP Y X).2.1.pt
            rw [Category.comp_id]
        }, ?_⟩
    rw [(swapMap X Y).2.1,
      CartesianMonoidalCategory.lift_snd_fst]
  have hdata : smashBraiding P hP X Y = data.1 := by
    unfold smashBraiding
    rfl
  rw [hdata]
  simpa only [costarSmashQuotient,
    CartesianMonoidalCategory.lift_snd_fst] using data.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem costarSmashLeftUnitor_free
    (P : C) (hP : IsTerminal P) (T : Under P) :
    letI := smashMonoidalCategory P hP
    ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
        costarSmashQuotient P hP (smashUnit P) T ≫
        (smashLeftUnitor P hP T).hom.right =
      ((hP.uniqueUpToIso
          CartesianMonoidalCategory.isTerminalTensorUnit).hom ▷ T.right) ≫
        (λ_ T.right).hom := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let S0 : Under P := Under.mk (coprod.inl : P ⟶ P ⨿ P)
  let eS0 : smashUnit P ≅ S0 := Under.isoMk (Iso.refl _) (by
    dsimp [S0, smashUnit]
    simp [Under.costar_obj_hom])
  have eS0_right : eS0.hom.right = 𝟙 _ := rfl
  let p : P ≅ 𝟙_ C :=
    hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  let prodTo : S0.right ⊗ T.right ⟶ T.right :=
    (rightDistrib T.right P P).inv ≫
      coprod.desc (hP.from (P ⊗ T.right) ≫ T.hom)
        ((p.hom ▷ T.right) ≫ (λ_ T.right).hom)
  dsimp only [smashLeftUnitor]
  simp only [Iso.trans_hom, Under.comp_right]
  change ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
      costarSmashQuotient P hP (smashUnit P) T ≫
      (((smash P hP).map eS0.hom).app T).right ≫ _ = _
  have hq := costarSmashQuotient_naturality P hP eS0.hom (𝟙 T)
  have htensor : eS0.hom ⊗ₘ (𝟙 T) =
      ((smash P hP).map eS0.hom).app T := by
    change ((smash P hP).map eS0.hom).app T ≫
      ((smash P hP).obj S0).map (𝟙 T) = _
    rw [Functor.map_id, Category.comp_id]
  rw [htensor] at hq
  have hq' : costarSmashQuotient P hP (smashUnit P) T ≫
      (((smash P hP).map eS0.hom).app T).right =
        (eS0.hom.right ⊗ₘ 𝟙 T.right) ≫
          costarSmashQuotient P hP S0 T := by
    simpa only [Under.id_right] using hq
  slice_lhs 2 3 => rw [hq']
  rw [eS0_right]
  simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
  dsimp only [S0, costarSmashQuotient]
  simp only [pointedPushoutIsoOfDescentData_hom_right]
  calc
    _ = (coprod.inr ▷ T.right) ≫ prodTo := by
      simpa only [Category.assoc] using congrArg
        (fun k => (coprod.inr ▷ T.right) ≫ k)
        (PushoutCocone.IsColimit.inl_desc
          (smashPresentation P hP (Under.mk coprod.inl) T).2.2 _ _ _)
    _ = _ := by
      dsimp only [prodTo]
      rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
        CategoryTheory.Limits.coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem costarSmashRightUnitor_free
    (P : C) (hP : IsTerminal P) (T : Under P) :
    letI := smashMonoidalCategory P hP
    (T.right ◁ (show P ⟶ (smashUnit P).right from coprod.inr)) ≫
        costarSmashQuotient P hP T (smashUnit P) ≫
        (smashRightUnitor P hP T).hom.right =
      (T.right ◁ (hP.uniqueUpToIso
          CartesianMonoidalCategory.isTerminalTensorUnit).hom) ≫
        (ρ_ T.right).hom := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let p : P ≅ 𝟙_ C :=
    hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  dsimp only [smashRightUnitor, Iso.trans_hom, Under.comp_right]
  slice_lhs 2 3 => rw [costarSmashBraiding_hom_quotient]
  slice_lhs 1 2 => rw [BraidedCategory.braiding_naturality_right]
  simp only [Category.assoc]
  rw [costarSmashLeftUnitor_free]
  slice_lhs 1 2 => rw [← BraidedCategory.braiding_naturality_right]
  rw [braiding_tensorUnit_right]
  slice_lhs 3 4 => rw [Iso.inv_hom_id]
  rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[instance_reducible]
private noncomputable def costarForgetLaxMonoidal
    (P : C) (hP : IsTerminal P) :
    letI := smashMonoidalCategory P hP
    (Under.forget P).LaxMonoidal := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let p : P ≅ 𝟙_ C :=
    hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  let freePoint : P ⟶ (smashUnit P).right := coprod.inr
  refine Functor.LaxMonoidal.ofTensorHom
    (p.inv ≫ freePoint)
    (fun X Y => costarSmashQuotient P hP X Y) ?_ ?_ ?_ ?_
  · intro X Y X' Y' f g
    exact (costarSmashQuotient_naturality P hP f g).symm
  · intro X Y Z
    simp only [tensorHom_id, id_tensorHom, Under.forget_obj,
      Under.forget_map]
    have hXY : costarSmashQuotient P hP (X ⊗ Y) Z =
        costarSmashQuotient P hP (((smash P hP).obj X).obj Y) Z := rfl
    have hYZ : costarSmashQuotient P hP X (Y ⊗ Z) =
        costarSmashQuotient P hP X (((smash P hP).obj Y).obj Z) := rfl
    have hα : (α_ X Y Z).hom.right =
        (smashAssociator P hP X Y Z).hom.right := rfl
    rw [hXY, hYZ, hα]
    simpa only [costarSmashQuotient, Category.assoc] using
      smashAssociator_hom_quotient P hP X Y Z
  · intro X
    change (λ_ X.right).hom =
      ((p.inv ≫ freePoint) ⊗ₘ 𝟙 X.right) ≫
        costarSmashQuotient P hP (smashUnit P) X ≫
          (smashLeftUnitor P hP X).hom.right
    simp only [tensorHom_id, MonoidalCategory.comp_whiskerRight,
      Category.assoc]
    rw [costarSmashLeftUnitor_free]
    slice_rhs 1 2 =>
      rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
        MonoidalCategory.id_whiskerRight]
    rw [Category.id_comp]
  · intro X
    change (ρ_ X.right).hom =
      (𝟙 X.right ⊗ₘ (p.inv ≫ freePoint)) ≫
        costarSmashQuotient P hP X (smashUnit P) ≫
          (smashRightUnitor P hP X).hom.right
    simp only [id_tensorHom, MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rw [costarSmashRightUnitor_free]
    slice_rhs 1 2 =>
      rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
        MonoidalCategory.whiskerLeft_id]
    rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def costarOplaxUnitIso
    (P : C) (hP : IsTerminal P) :
    letI := smashMonoidalCategory P hP
    letI := costarForgetLaxMonoidal P hP
    letI := (Under.costarAdjForget P).leftAdjointOplaxMonoidal
    (Under.costar P).obj (𝟙_ C) ≅ smashUnit P := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let _ : (Under.forget P).LaxMonoidal := costarForgetLaxMonoidal P hP
  let _ : (Under.costar P).OplaxMonoidal :=
    (Under.costarAdjForget P).leftAdjointOplaxMonoidal
  let F := Under.costar P
  let p : P ≅ 𝟙_ C :=
    hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  let freePoint : P ⟶ (smashUnit P).right := coprod.inr
  have heta_right : (Functor.OplaxMonoidal.η F).right =
      coprod.desc (smashUnit P).hom (p.inv ≫ freePoint) := by
    change (((Under.costarAdjForget P).homEquiv
      (𝟙_ C) (smashUnit P)).symm (p.inv ≫ freePoint)).right = _
    rw [Adjunction.homEquiv_counit]
    simp only [Under.comp_right]
    change ((Under.costar P).map (p.inv ≫ freePoint)).right ≫
      ((Under.costarAdjForget P).counit.app (smashUnit P)).right = _
    simp [Under.costar, Under.costarAdjForget, Adjunction.comp_counit_app,
      algebraEquivUnder, algebraToUnder, underToAlgebra, coprodMonad,
      Monad.adj]
  let e : F.obj (𝟙_ C) ≅ smashUnit P :=
    Under.isoMk (coprod.mapIso (Iso.refl P) p.symm) (by
      change (F.obj (𝟙_ C)).hom ≫ coprod.map (𝟙 P) p.inv =
        (smashUnit P).hom
      simp [F, smashUnit, Under.costar_obj_hom])
  have heta : Functor.OplaxMonoidal.η F = e.hom := by
    apply Under.UnderMorphism.ext
    rw [heta_right]
    change coprod.desc (smashUnit P).hom (p.inv ≫ freePoint) =
      coprod.map (𝟙 P) p.inv
    apply coprod.hom_ext
    · simp [smashUnit, Under.costar_obj_hom]
    · rw [coprod.inr_desc, coprod.inr_map]
  exact
    { hom := Functor.OplaxMonoidal.η F
      inv := e.inv
      hom_inv_id := by rw [heta]; exact e.hom_inv_id
      inv_hom_id := by rw [heta]; exact e.inv_hom_id }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def costarOplaxTensorIso
    (P : C) (hP : IsTerminal P) (A B : C) :
    letI := smashMonoidalCategory P hP
    letI := costarForgetLaxMonoidal P hP
    letI := (Under.costarAdjForget P).leftAdjointOplaxMonoidal
    (Under.costar P).obj (A ⊗ B) ≅
      (Under.costar P).obj A ⊗ (Under.costar P).obj B := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let _ : (Under.forget P).LaxMonoidal := costarForgetLaxMonoidal P hP
  let _ : (Under.costar P).OplaxMonoidal :=
    (Under.costarAdjForget P).leftAdjointOplaxMonoidal
  let _ : IsMonoidalDistrib C :=
    isMonoidalDistrib.of_symmetric_monoidal_closed
  let fourSplit (A B : C) :
      (P ⨿ A) ⊗ (P ⨿ B) ≅
        ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B)) :=
    (leftDistrib (P ⨿ A) P B).symm ≪≫
      coprod.mapIso (rightDistrib P P A).symm
        (rightDistrib B P A).symm
  have fourSplit_00 (A B : C) :
      ((coprod.inl : P ⟶ P ⨿ A) ⊗ₘ (coprod.inl : P ⟶ P ⨿ B)) ≫
          (fourSplit A B).hom =
        (coprod.inl : P ⊗ P ⟶ (P ⊗ P) ⨿ (A ⊗ P)) ≫
          (coprod.inl : (P ⊗ P) ⨿ (A ⊗ P) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    simp [fourSplit, tensorHom_def, Category.assoc,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  have fourSplit_A0 (A B : C) :
      ((coprod.inr : A ⟶ P ⨿ A) ⊗ₘ (coprod.inl : P ⟶ P ⨿ B)) ≫
          (fourSplit A B).hom =
        (coprod.inr : A ⊗ P ⟶ (P ⊗ P) ⨿ (A ⊗ P)) ≫
          (coprod.inl : (P ⊗ P) ⨿ (A ⊗ P) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    simp [fourSplit, tensorHom_def, Category.assoc,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  have fourSplit_0B (A B : C) :
      ((coprod.inl : P ⟶ P ⨿ A) ⊗ₘ (coprod.inr : B ⟶ P ⨿ B)) ≫
          (fourSplit A B).hom =
        (coprod.inl : P ⊗ B ⟶ (P ⊗ B) ⨿ (A ⊗ B)) ≫
          (coprod.inr : (P ⊗ B) ⨿ (A ⊗ B) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    simp [fourSplit, tensorHom_def, Category.assoc,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  have fourSplit_AB (A B : C) :
      ((coprod.inr : A ⟶ P ⨿ A) ⊗ₘ (coprod.inr : B ⟶ P ⨿ B)) ≫
          (fourSplit A B).hom =
        (coprod.inr : A ⊗ B ⟶ (P ⊗ B) ⨿ (A ⊗ B)) ≫
          (coprod.inr : (P ⊗ B) ⨿ (A ⊗ B) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    simp [fourSplit, tensorHom_def, Category.assoc,
      ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  let FA (A : C) : Under P := (Under.costar P).obj A
  have FA_hom (A : C) : (FA A).hom = (coprod.inl : P ⟶ P ⨿ A) := by
    dsimp only [FA]
    unfold Under.costar
    dsimp [Monad.free, algebraToUnder, coprodMonad]
    simp
  let unit (A : C) : A ⟶ (FA A).right :=
    (Under.costarAdjForget P).unit.app A
  have unit_eq (A : C) : unit A = (coprod.inr : A ⟶ P ⨿ A) := by
    dsimp only [unit]
    unfold Under.costarAdjForget
    rw [Adjunction.comp_unit_app, Monad.adj_unit,
      Equivalence.toAdjunction_unit, coprodMonad_η_app]
    dsimp [algebraEquivUnder, Monad.forget, Monad.Algebra.isoMk]
    simp only [Category.comp_id]
  have delta_right (A B : C) :
      (Functor.OplaxMonoidal.δ (Under.costar P) A B).right =
        coprod.desc (FA A ⊗ FA B).hom
          ((unit A ⊗ₘ unit B) ≫
            costarSmashQuotient P hP (FA A) (FA B)) := by
    rw [Adjunction.leftAdjointOplaxMonoidal_δ]
    change (((Under.costarAdjForget P).homEquiv (A ⊗ B)
      (FA A ⊗ FA B)).symm
        ((unit A ⊗ₘ unit B) ≫
          costarSmashQuotient P hP (FA A) (FA B))).right = _
    rw [Adjunction.homEquiv_counit]
    simp only [Under.comp_right]
    simp [FA, unit, Under.costar, Under.costarAdjForget,
      Adjunction.comp_counit_app, algebraEquivUnder, algebraToUnder,
      underToAlgebra, coprodMonad, Monad.adj]
  have fourSplit_FA_00 (A B : C) :
      ((FA A).hom ⊗ₘ (FA B).hom) ≫ (fourSplit A B).hom =
        (coprod.inl : P ⊗ P ⟶ (P ⊗ P) ⨿ (A ⊗ P)) ≫
          (coprod.inl : (P ⊗ P) ⨿ (A ⊗ P) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    rw [FA_hom, FA_hom]
    exact fourSplit_00 A B
  have fourSplit_FA_A0 (A B : C) :
      (unit A ⊗ₘ (FA B).hom) ≫
          (fourSplit A B).hom =
        (coprod.inr : A ⊗ P ⟶ (P ⊗ P) ⨿ (A ⊗ P)) ≫
          (coprod.inl : (P ⊗ P) ⨿ (A ⊗ P) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    rw [unit_eq, FA_hom]
    exact fourSplit_A0 A B
  have fourSplit_FA_0B (A B : C) :
      ((FA A).hom ⊗ₘ unit B) ≫
          (fourSplit A B).hom =
        (coprod.inl : P ⊗ B ⟶ (P ⊗ B) ⨿ (A ⊗ B)) ≫
          (coprod.inr : (P ⊗ B) ⨿ (A ⊗ B) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    rw [FA_hom, unit_eq]
    exact fourSplit_0B A B
  have fourSplit_FA_AB (A B : C) :
      (unit A ⊗ₘ unit B) ≫ (fourSplit A B).hom =
        (coprod.inr : A ⊗ B ⟶ (P ⊗ B) ⨿ (A ⊗ B)) ≫
          (coprod.inr : (P ⊗ B) ⨿ (A ⊗ B) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B))) := by
    rw [unit_eq, unit_eq]
    exact fourSplit_AB A B
  let leftRaw (A B : C) :
      (FA A).right ⟶ (FA A).right ⊗ (FA B).right :=
    CartesianMonoidalCategory.lift (𝟙 (FA A).right)
      (hP.from (FA A).right ≫ (FA B).hom)
  let rightRaw (A B : C) :
      (FA B).right ⟶ (FA A).right ⊗ (FA B).right :=
    CartesianMonoidalCategory.lift
      (hP.from (FA B).right ≫ (FA A).hom) (𝟙 (FA B).right)
  have rawCondition (A B : C) :
      (FA A).hom ≫ leftRaw A B = (FA B).hom ≫ rightRaw A B := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [leftRaw, rightRaw, Category.assoc,
        CartesianMonoidalCategory.lift_fst]
      rw [Category.comp_id, ← Category.assoc]
      simpa only [Category.id_comp] using
        congrArg (fun k : P ⟶ P => k ≫ (FA A).hom)
          (hP.hom_ext (𝟙 P) ((FA B).hom ≫ hP.from (FA B).right))
    · simp only [leftRaw, rightRaw, Category.assoc,
        CartesianMonoidalCategory.lift_snd]
      rw [Category.comp_id, ← Category.assoc]
      simpa only [Category.id_comp] using
        congrArg (fun k : P ⟶ P => k ≫ (FA B).hom)
          (hP.hom_ext ((FA A).hom ≫ hP.from (FA A).right) (𝟙 P))
  let wtpRaw (A B : C) :
      pushout (FA A).hom (FA B).hom ⟶
        (FA A).right ⊗ (FA B).right :=
    pushout.desc (leftRaw A B) (rightRaw A B) (rawCondition A B)
  let collapseRaw (A B : C) :
      pushout (FA A).hom (FA B).hom ⟶ P :=
    hP.from _
  let fourTo (A B : C) :
      (FA A).right ⊗ (FA B).right ⟶ (FA (A ⊗ B)).right :=
    (fourSplit A B).hom ≫
      coprod.desc
        (coprod.desc
          (hP.from (P ⊗ P) ≫ coprod.inl)
          (hP.from (A ⊗ P) ≫ coprod.inl))
        (coprod.desc
          (hP.from (P ⊗ B) ≫ coprod.inl)
          coprod.inr)
  have wtpRaw_fourTo (A B : C) :
      wtpRaw A B ≫ fourTo A B =
        collapseRaw A B ≫ (FA (A ⊗ B)).hom := by
    unfold wtpRaw collapseRaw
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc]
      apply coprod.hom_ext
      · have hface : (FA A).hom ≫ leftRaw A B =
            CartesianMonoidalCategory.lift (𝟙 P) (𝟙 P) ≫
              ((FA A).hom ⊗ₘ (FA B).hom) := by
          dsimp only [leftRaw, FA]
          apply CartesianMonoidalCategory.hom_ext
          · simp only [Category.assoc,
              CartesianMonoidalCategory.lift_fst,
              CartesianMonoidalCategory.lift_fst_assoc,
              CartesianMonoidalCategory.tensorHom_fst,
              Category.comp_id, Category.id_comp]
          · simp only [Category.assoc,
              CartesianMonoidalCategory.lift_snd,
              CartesianMonoidalCategory.lift_snd_assoc,
              CartesianMonoidalCategory.tensorHom_snd,
              Category.id_comp]
            rw [← Category.assoc]
            simpa only [Category.id_comp] using congrArg
              (fun k : P ⟶ P => k ≫ (FA B).hom)
              (hP.hom_ext
                ((FA A).hom ≫ hP.from (FA A).right) (𝟙 P))
        rw [← FA_hom A, ← Category.assoc, hface]
        dsimp only [fourTo]
        simp only [Category.assoc]
        slice_lhs 2 3 => rw [fourSplit_FA_00]
        simp only [coprod.inl_desc, Category.assoc]
        rw [← FA_hom (A ⊗ B)]
        simpa only [Category.assoc] using congrArg
          (fun k : P ⟶ P => k ≫ (FA (A ⊗ B)).hom)
          (hP.hom_ext
            (CartesianMonoidalCategory.lift (𝟙 P) (𝟙 P) ≫
              hP.from (P ⊗ P))
            ((FA A).hom ≫ pushout.inl (FA A).hom (FA B).hom ≫
              hP.from (pushout (FA A).hom (FA B).hom)))
      · have hface : unit A ≫ leftRaw A B =
            CartesianMonoidalCategory.lift (𝟙 A) (hP.from A) ≫
              (unit A ⊗ₘ (FA B).hom) := by
          dsimp only [leftRaw, FA]
          apply CartesianMonoidalCategory.hom_ext
          · with_unfolding_all simp
          · with_unfolding_all
            simp only [Category.assoc,
              CartesianMonoidalCategory.lift_snd,
              CartesianMonoidalCategory.lift_snd_assoc,
              CartesianMonoidalCategory.tensorHom_snd]
            rw [← Category.assoc]
            exact congrArg
              (fun k : A ⟶ P => k ≫ (FA B).hom)
              (hP.hom_ext
                (unit A ≫
                  hP.from (FA A).right) (hP.from A))
        rw [← unit_eq A, ← Category.assoc, hface]
        dsimp only [fourTo]
        simp only [Category.assoc]
        slice_lhs 2 3 => rw [fourSplit_FA_A0]
        simp only [coprod.inr_desc, coprod.inl_desc, Category.assoc]
        rw [← FA_hom (A ⊗ B)]
        simpa only [Category.assoc] using congrArg
          (fun k : A ⟶ P => k ≫ (FA (A ⊗ B)).hom)
          (hP.hom_ext
            (CartesianMonoidalCategory.lift (𝟙 A) (hP.from A) ≫
              hP.from (A ⊗ P))
            (unit A ≫
              pushout.inl (FA A).hom (FA B).hom ≫
              hP.from (pushout (FA A).hom (FA B).hom)))
    · rw [← Category.assoc, pushout.inr_desc]
      apply coprod.hom_ext
      · have hface : (FA B).hom ≫ rightRaw A B =
            CartesianMonoidalCategory.lift (𝟙 P) (𝟙 P) ≫
              ((FA A).hom ⊗ₘ (FA B).hom) := by
          dsimp only [rightRaw, FA]
          apply CartesianMonoidalCategory.hom_ext
          · simp only [Category.assoc,
              CartesianMonoidalCategory.lift_fst,
              CartesianMonoidalCategory.lift_fst_assoc,
              CartesianMonoidalCategory.tensorHom_fst,
              Category.id_comp]
            rw [← Category.assoc]
            simpa only [Category.id_comp] using congrArg
              (fun k : P ⟶ P => k ≫ (FA A).hom)
              (hP.hom_ext
                ((FA B).hom ≫ hP.from (FA B).right) (𝟙 P))
          · simp only [Category.assoc,
              CartesianMonoidalCategory.lift_snd,
              CartesianMonoidalCategory.lift_snd_assoc,
              CartesianMonoidalCategory.tensorHom_snd,
              Category.comp_id, Category.id_comp]
        rw [← FA_hom B, ← Category.assoc, hface]
        dsimp only [fourTo]
        simp only [Category.assoc]
        slice_lhs 2 3 => rw [fourSplit_FA_00]
        simp only [coprod.inl_desc, Category.assoc]
        rw [← FA_hom (A ⊗ B)]
        simpa only [Category.assoc] using congrArg
          (fun k : P ⟶ P => k ≫ (FA (A ⊗ B)).hom)
          (hP.hom_ext
            (CartesianMonoidalCategory.lift (𝟙 P) (𝟙 P) ≫
              hP.from (P ⊗ P))
            ((FA B).hom ≫ pushout.inr (FA A).hom (FA B).hom ≫
              hP.from (pushout (FA A).hom (FA B).hom)))
      · have hface : unit B ≫ rightRaw A B =
            CartesianMonoidalCategory.lift (hP.from B) (𝟙 B) ≫
              ((FA A).hom ⊗ₘ unit B) := by
          dsimp only [rightRaw, FA]
          apply CartesianMonoidalCategory.hom_ext
          · with_unfolding_all
            simp only [Category.assoc,
              CartesianMonoidalCategory.lift_fst,
              CartesianMonoidalCategory.lift_fst_assoc,
              CartesianMonoidalCategory.tensorHom_fst]
            rw [← Category.assoc]
            exact congrArg
              (fun k : B ⟶ P => k ≫ (FA A).hom)
              (hP.hom_ext
                (unit B ≫
                  hP.from (FA B).right) (hP.from B))
          · with_unfolding_all simp
        rw [← unit_eq B, ← Category.assoc, hface]
        dsimp only [fourTo]
        simp only [Category.assoc]
        slice_lhs 2 3 => rw [fourSplit_FA_0B]
        simp only [coprod.inl_desc, coprod.inr_desc, Category.assoc]
        rw [← FA_hom (A ⊗ B)]
        simpa only [Category.assoc] using congrArg
          (fun k : B ⟶ P => k ≫ (FA (A ⊗ B)).hom)
          (hP.hom_ext
            (CartesianMonoidalCategory.lift (hP.from B) (𝟙 B) ≫
              hP.from (P ⊗ B))
            (unit B ≫
              pushout.inr (FA A).hom (FA B).hom ≫
              hP.from (pushout (FA A).hom (FA B).hom)))
  let forward (A B : C) :
      ((smash P hP).obj (FA A)).obj (FA B) ⟶ FA (A ⊗ B) :=
    Under.homMk
      (PushoutCocone.IsColimit.desc
        (smashPresentation P hP (FA A) (FA B)).2.2
        (fourTo A B) (FA (A ⊗ B)).hom (by
          exact wtpRaw_fourTo A B)) (by
            exact PushoutCocone.IsColimit.inr_desc
              (smashPresentation P hP (FA A) (FA B)).2.2 _ _ _)
  have quotient_forward (A B : C) :
      costarSmashQuotient P hP (FA A) (FA B) ≫
        (forward A B).right = fourTo A B :=
    PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP (FA A) (FA B)).2.2 _ _ _
  have basepoint_forward (A B : C) :
      (((smash P hP).obj (FA A)).obj (FA B)).hom ≫
        (forward A B).right = (FA (A ⊗ B)).hom :=
    Under.w (forward A B)
  have tensor_hom (A B : C) :
      (FA A ⊗ FA B).hom =
        (((smash P hP).obj (FA A)).obj (FA B)).hom := rfl
  have presentation_inl (A B : C) :
      (smashPresentation P hP (FA A) (FA B)).2.1.inl =
        costarSmashQuotient P hP (FA A) (FA B) := by
    with_unfolding_all rfl
  have presentation_inr (A B : C) :
      (smashPresentation P hP (FA A) (FA B)).2.1.inr =
        (((smash P hP).obj (FA A)).obj (FA B)).hom := by
    with_unfolding_all rfl
  have leftRaw_quotient (A B : C) :
      leftRaw A B ≫ costarSmashQuotient P hP (FA A) (FA B) =
        hP.from (FA A).right ≫
          (((smash P hP).obj (FA A)).obj (FA B)).hom := by
    change leftRaw A B ≫ pushout.inl (wtpRaw A B) (collapseRaw A B) =
      hP.from (FA A).right ≫ pushout.inr (wtpRaw A B) (collapseRaw A B)
    rw [← pushout.inl_desc (leftRaw A B) (rightRaw A B)
      (rawCondition A B)]
    unfold wtpRaw collapseRaw
    rw [Category.assoc, pushout.condition]
    simpa only [Category.assoc] using congrArg
      (fun k : (FA A).right ⟶ P =>
        k ≫ pushout.inr
          (pushout.desc (leftRaw A B) (rightRaw A B) (rawCondition A B))
          (hP.from (pushout (FA A).hom (FA B).hom)))
        (hP.hom_ext
          (pushout.inl (FA A).hom (FA B).hom ≫
            hP.from (pushout (FA A).hom (FA B).hom))
          (hP.from (FA A).right))
  have rightRaw_quotient (A B : C) :
      rightRaw A B ≫ costarSmashQuotient P hP (FA A) (FA B) =
        hP.from (FA B).right ≫
          (((smash P hP).obj (FA A)).obj (FA B)).hom := by
    change rightRaw A B ≫ pushout.inl (wtpRaw A B) (collapseRaw A B) =
      hP.from (FA B).right ≫ pushout.inr (wtpRaw A B) (collapseRaw A B)
    rw [← pushout.inr_desc (leftRaw A B) (rightRaw A B)
      (rawCondition A B)]
    unfold wtpRaw collapseRaw
    rw [Category.assoc, pushout.condition]
    simpa only [Category.assoc] using congrArg
      (fun k : (FA B).right ⟶ P =>
        k ≫ pushout.inr
          (pushout.desc (leftRaw A B) (rightRaw A B) (rawCondition A B))
          (hP.from (pushout (FA A).hom (FA B).hom)))
        (hP.hom_ext
          (pushout.inr (FA A).hom (FA B).hom ≫
            hP.from (pushout (FA A).hom (FA B).hom))
          (hP.from (FA B).right))
  have branch00_factor (A B : C) :
      ((FA A).hom ⊗ₘ (FA B).hom) =
        (hP.from (P ⊗ P) ≫ (FA A).hom) ≫ leftRaw A B := by
    dsimp only [leftRaw, FA]
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.tensorHom_fst, Category.assoc,
        CartesianMonoidalCategory.lift_fst, Category.comp_id]
      exact congrArg (fun k : P ⊗ P ⟶ P => k ≫ (FA A).hom)
        (hP.hom_ext _ _)
    · rw [CartesianMonoidalCategory.tensorHom_snd, Category.assoc,
        CartesianMonoidalCategory.lift_snd]
      simpa only [Category.assoc] using congrArg
        (fun k : P ⊗ P ⟶ P => k ≫ (FA B).hom)
        (hP.hom_ext
          (CartesianMonoidalCategory.snd P P)
          ((hP.from (P ⊗ P) ≫ (FA A).hom) ≫
            hP.from (FA A).right))
  have branchA0_factor (A B : C) :
      (unit A ⊗ₘ (FA B).hom) =
        (CartesianMonoidalCategory.fst A P ≫
          unit A) ≫
          leftRaw A B := by
    dsimp only [leftRaw, FA]
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.tensorHom_fst, Category.assoc,
        CartesianMonoidalCategory.lift_fst, Category.comp_id]
    · rw [CartesianMonoidalCategory.tensorHom_snd, Category.assoc,
        CartesianMonoidalCategory.lift_snd]
      simpa only [Category.assoc] using congrArg
        (fun k : A ⊗ P ⟶ P => k ≫ (FA B).hom)
        (hP.hom_ext
          (CartesianMonoidalCategory.snd A P)
          ((CartesianMonoidalCategory.fst A P ≫ unit A) ≫
            hP.from (FA A).right))
  have branch0B_factor (A B : C) :
      ((FA A).hom ⊗ₘ unit B) =
        (CartesianMonoidalCategory.snd P B ≫
          unit B) ≫
          rightRaw A B := by
    dsimp only [rightRaw, FA]
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.tensorHom_fst, Category.assoc,
        CartesianMonoidalCategory.lift_fst]
      simpa only [Category.assoc] using congrArg
        (fun k : P ⊗ B ⟶ P => k ≫ (FA A).hom)
        (hP.hom_ext
          (CartesianMonoidalCategory.fst P B)
          ((CartesianMonoidalCategory.snd P B ≫ unit B) ≫
            hP.from (FA B).right))
    · rw [CartesianMonoidalCategory.tensorHom_snd, Category.assoc,
        CartesianMonoidalCategory.lift_snd, Category.comp_id]
  have branch00_quotient (A B : C) :
      ((FA A).hom ⊗ₘ (FA B).hom) ≫
          costarSmashQuotient P hP (FA A) (FA B) =
        hP.from (P ⊗ P) ≫
          (((smash P hP).obj (FA A)).obj (FA B)).hom := by
    rw [branch00_factor, Category.assoc, leftRaw_quotient]
    simpa only [Category.assoc] using congrArg
      (fun k : P ⊗ P ⟶ P =>
        k ≫ (((smash P hP).obj (FA A)).obj (FA B)).hom)
      (hP.hom_ext
        (hP.from (P ⊗ P) ≫ (FA A).hom ≫
          hP.from (FA A).right)
        (hP.from (P ⊗ P)))
  have branchA0_quotient (A B : C) :
      (unit A ⊗ₘ (FA B).hom) ≫
          costarSmashQuotient P hP (FA A) (FA B) =
        hP.from (A ⊗ P) ≫
          (((smash P hP).obj (FA A)).obj (FA B)).hom := by
    rw [branchA0_factor, Category.assoc, leftRaw_quotient]
    simpa only [Category.assoc] using congrArg
      (fun k : A ⊗ P ⟶ P =>
        k ≫ (((smash P hP).obj (FA A)).obj (FA B)).hom)
      (hP.hom_ext
        (CartesianMonoidalCategory.fst A P ≫
          unit A ≫
          hP.from (FA A).right)
        (hP.from (A ⊗ P)))
  have branch0B_quotient (A B : C) :
      ((FA A).hom ⊗ₘ unit B) ≫
          costarSmashQuotient P hP (FA A) (FA B) =
        hP.from (P ⊗ B) ≫
          (((smash P hP).obj (FA A)).obj (FA B)).hom := by
    rw [branch0B_factor, Category.assoc, rightRaw_quotient]
    simpa only [Category.assoc] using congrArg
      (fun k : P ⊗ B ⟶ P =>
        k ≫ (((smash P hP).obj (FA A)).obj (FA B)).hom)
      (hP.hom_ext
        (CartesianMonoidalCategory.snd P B ≫
          unit B ≫
          hP.from (FA B).right)
        (hP.from (P ⊗ B)))
  have delta_forward (A B : C) :
      Functor.OplaxMonoidal.δ (Under.costar P) A B ≫ forward A B =
        𝟙 (FA (A ⊗ B)) := by
    apply Under.UnderMorphism.ext
    rw [Under.comp_right, Under.id_right, delta_right]
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, tensor_hom,
        basepoint_forward]
      erw [← FA_hom (A ⊗ B), Category.comp_id]
    · rw [← Category.assoc, coprod.inr_desc]
      simp only [Category.assoc]
      slice_lhs 2 3 => rw [quotient_forward]
      dsimp only [fourTo]
      slice_lhs 1 2 => rw [fourSplit_FA_AB]
      rw [Category.assoc, coprod.inr_desc, coprod.inr_desc]
      exact (Category.comp_id _).symm
  have fourSplit_inv_00 (A B : C) :
      ((coprod.inl : P ⊗ P ⟶ (P ⊗ P) ⨿ (A ⊗ P)) ≫
          (coprod.inl : (P ⊗ P) ⨿ (A ⊗ P) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B)))) ≫
        (fourSplit A B).inv =
      ((coprod.inl : P ⟶ P ⨿ A) ⊗ₘ (coprod.inl : P ⟶ P ⨿ B)) := by
    apply (cancel_mono (fourSplit A B).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      fourSplit_00]
  have fourSplit_inv_A0 (A B : C) :
      ((coprod.inr : A ⊗ P ⟶ (P ⊗ P) ⨿ (A ⊗ P)) ≫
          (coprod.inl : (P ⊗ P) ⨿ (A ⊗ P) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B)))) ≫
        (fourSplit A B).inv =
      ((coprod.inr : A ⟶ P ⨿ A) ⊗ₘ (coprod.inl : P ⟶ P ⨿ B)) := by
    apply (cancel_mono (fourSplit A B).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      fourSplit_A0]
  have fourSplit_inv_0B (A B : C) :
      ((coprod.inl : P ⊗ B ⟶ (P ⊗ B) ⨿ (A ⊗ B)) ≫
          (coprod.inr : (P ⊗ B) ⨿ (A ⊗ B) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B)))) ≫
        (fourSplit A B).inv =
      ((coprod.inl : P ⟶ P ⨿ A) ⊗ₘ (coprod.inr : B ⟶ P ⨿ B)) := by
    apply (cancel_mono (fourSplit A B).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      fourSplit_0B]
  have fourSplit_inv_AB (A B : C) :
      ((coprod.inr : A ⊗ B ⟶ (P ⊗ B) ⨿ (A ⊗ B)) ≫
          (coprod.inr : (P ⊗ B) ⨿ (A ⊗ B) ⟶
            ((P ⊗ P) ⨿ (A ⊗ P)) ⨿ ((P ⊗ B) ⨿ (A ⊗ B)))) ≫
        (fourSplit A B).inv =
      ((coprod.inr : A ⟶ P ⨿ A) ⊗ₘ (coprod.inr : B ⟶ P ⨿ B)) := by
    apply (cancel_mono (fourSplit A B).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      fourSplit_AB]
  have fourTo_delta (A B : C) :
      fourTo A B ≫
          (Functor.OplaxMonoidal.δ (Under.costar P) A B).right =
        costarSmashQuotient P hP (FA A) (FA B) := by
    rw [delta_right]
    apply (cancel_epi (fourSplit A B).inv).1
    dsimp only [fourTo]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc]
        rw [Category.assoc, coprod.inl_desc]
        rw [reassoc_of% fourSplit_inv_00 A B, ← FA_hom A, ← FA_hom B,
          branch00_quotient, tensor_hom]
      · rw [coprod.inl_desc_assoc, coprod.inr_desc_assoc]
        rw [Category.assoc, coprod.inl_desc]
        rw [reassoc_of% fourSplit_inv_A0 A B, ← unit_eq A, ← FA_hom B,
          branchA0_quotient, tensor_hom]
    · apply coprod.hom_ext
      · rw [coprod.inr_desc_assoc, coprod.inl_desc_assoc]
        rw [Category.assoc, coprod.inl_desc]
        rw [reassoc_of% fourSplit_inv_0B A B, ← FA_hom A, ← unit_eq B,
          branch0B_quotient, tensor_hom]
      · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc]
        rw [reassoc_of% fourSplit_inv_AB A B, ← unit_eq A, ← unit_eq B]
        simp only [coprod.inr_desc]
  have forward_delta (A B : C) :
      forward A B ≫ Functor.OplaxMonoidal.δ (Under.costar P) A B =
        𝟙 (FA A ⊗ FA B) := by
    apply Under.UnderMorphism.ext
    rw [Under.comp_right, Under.id_right]
    apply PushoutCocone.IsColimit.hom_ext
      (smashPresentation P hP (FA A) (FA B)).2.2
    · erw [Category.comp_id, ← Category.assoc]
      rw [presentation_inl]
      rw [quotient_forward, fourTo_delta]
    · erw [Category.comp_id, ← Category.assoc]
      rw [presentation_inr]
      rw [basepoint_forward]
      exact Under.w (Functor.OplaxMonoidal.δ (Under.costar P) A B)
  exact
    { hom := Functor.OplaxMonoidal.δ (Under.costar P) A B
      inv := forward A B
      hom_inv_id := delta_forward A B
      inv_hom_id := forward_delta A B }

/-- Freely adjoining a point under a chosen terminal object is strong monoidal
from the cartesian tensor product to the smash product. -/
noncomputable def costarCoreMonoidal (P : C) (hP : IsTerminal P) :
    letI := smashMonoidalCategory P hP
    (Under.costar P).CoreMonoidal := by
  let _ : MonoidalCategory (Under P) := smashMonoidalCategory P hP
  let _ : (Under.forget P).LaxMonoidal := costarForgetLaxMonoidal P hP
  let _ : (Under.costar P).OplaxMonoidal :=
    (Under.costarAdjForget P).leftAdjointOplaxMonoidal
  let _ : IsIso (Functor.OplaxMonoidal.η (Under.costar P)) := by
    change IsIso (costarOplaxUnitIso P hP).hom
    exact (costarOplaxUnitIso P hP).isIso_hom
  let _ : ∀ A B, IsIso (Functor.OplaxMonoidal.δ (Under.costar P) A B) :=
    fun A B => by
      change IsIso (costarOplaxTensorIso P hP A B).hom
      exact (costarOplaxTensorIso P hP A B).isIso_hom
  exact Functor.CoreMonoidal.ofOplaxMonoidal (Under.costar P)

end CategoryTheory.Pointed
