/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Operad.Collection
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace CategoryTheory.Operad

/-- The universe-zero skeleton of the original finite-bijection groupoid. -/
abbrev SmallFinBijGroupoid := Core FintypeCat.Skeleton.{0}

namespace SmallFinBijGroupoid

/-- The ordered block sum of the original finite index objects. -/
def blockSumObj (X Y : SmallFinBijGroupoid) : SmallFinBijGroupoid :=
  ⟨FintypeCat.Skeleton.mk (X.of.len + Y.of.len)⟩

@[simp]
theorem blockSumObj_len (X Y : SmallFinBijGroupoid) :
    (blockSumObj X Y).of.len = X.of.len + Y.of.len :=
  rfl

/-- The shared ordered finite-block coordinate equivalence. -/
def blockSumEquiv (X Y : SmallFinBijGroupoid) :
    ULift.{0, 0} (Fin (blockSumObj X Y).of.len) ≃
      ULift.{0, 0} (Fin X.of.len) ⊕
        ULift.{0, 0} (Fin Y.of.len) :=
  Equiv.ulift.trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

end SmallFinBijGroupoid

/-- The skeleton equivalence retains the original finite-bijection objects and maps. -/
noncomputable def smallFinBijEquivalence :
    SmallFinBijGroupoid ≌ FinBijGroupoid :=
  FintypeCat.Skeleton.equivalence.core

@[simp]
theorem smallFinBijEquivalence_functor_obj (X : SmallFinBijGroupoid) :
    (smallFinBijEquivalence.functor.obj X).of =
      FintypeCat.Skeleton.incl.obj X.of :=
  rfl

@[simp]
theorem smallFinBijEquivalence_functor_map
    {X Y : SmallFinBijGroupoid} (f : X ⟶ Y) :
    (smallFinBijEquivalence.functor.map f).iso =
      FintypeCat.Skeleton.incl.mapIso f.iso :=
  rfl

namespace SmallFinBijGroupoid

/-- The ordered block sum of two original finite-bijection arrows. -/
noncomputable def blockSumHom
    {X X' Y Y' : SmallFinBijGroupoid}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    blockSumObj X Y ⟶ blockSumObj X' Y' := by
  exact
    (Core.isoMk
      { hom := fun z => (blockSumEquiv X' Y').symm
          (Sum.map f.iso.hom g.iso.hom (blockSumEquiv X Y z))
        inv := fun z => (blockSumEquiv X Y).symm
          (Sum.map f.iso.inv g.iso.inv (blockSumEquiv X' Y' z))
        hom_inv_id := by
          funext z
          apply (blockSumEquiv X Y).injective
          let w := blockSumEquiv X Y z
          have hz : (blockSumEquiv X Y).symm w = z :=
            (blockSumEquiv X Y).symm_apply_apply z
          rw [← hz]
          simp only [CategoryStruct.comp, Function.comp_apply]
          rw [(blockSumEquiv X Y).apply_symm_apply]
          rw [(blockSumEquiv X' Y').apply_symm_apply]
          rw [(blockSumEquiv X Y).apply_symm_apply]
          have hid (q : ULift (Fin (blockSumObj X Y).of.len)) :
              (𝟙 (blockSumObj X Y).of) q = q := rfl
          rw [hid, (blockSumEquiv X Y).apply_symm_apply]
          rcases w with w | w
          · simp only [Sum.map_inl]
            have h := congrArg (fun k => k w) f.iso.hom_inv_id
            change f.iso.inv (f.iso.hom w) = w at h
            exact congrArg Sum.inl h
          · simp only [Sum.map_inr]
            have h := congrArg (fun k => k w) g.iso.hom_inv_id
            change g.iso.inv (g.iso.hom w) = w at h
            exact congrArg Sum.inr h
        inv_hom_id := by
          funext z
          apply (blockSumEquiv X' Y').injective
          let w := blockSumEquiv X' Y' z
          have hz : (blockSumEquiv X' Y').symm w = z :=
            (blockSumEquiv X' Y').symm_apply_apply z
          rw [← hz]
          simp only [CategoryStruct.comp, Function.comp_apply]
          rw [(blockSumEquiv X' Y').apply_symm_apply]
          rw [(blockSumEquiv X Y).apply_symm_apply]
          rw [(blockSumEquiv X' Y').apply_symm_apply]
          have hid (q : ULift (Fin (blockSumObj X' Y').of.len)) :
              (𝟙 (blockSumObj X' Y').of) q = q := rfl
          rw [hid, (blockSumEquiv X' Y').apply_symm_apply]
          rcases w with w | w
          · simp only [Sum.map_inl]
            have h := congrArg (fun k => k w) f.iso.inv_hom_id
            change f.iso.hom (f.iso.inv w) = w at h
            exact congrArg Sum.inl h
          · simp only [Sum.map_inr]
            have h := congrArg (fun k => k w) g.iso.inv_hom_id
            change g.iso.hom (g.iso.inv w) = w at h
            exact congrArg Sum.inr h }).hom


theorem blockSumHom_equivOfHom
    {X X' Y Y' : SmallFinBijGroupoid}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    let split (A B : SmallFinBijGroupoid) :
        ULift.{0, 0} (Fin (blockSumObj A B).of.len) ≃
          ULift.{0, 0} (Fin A.of.len) ⊕
            ULift.{0, 0} (Fin B.of.len) :=
      blockSumEquiv A B
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map (blockSumHom f g)) =
      (split X Y).trans
        ((Equiv.sumCongr
          (FinBijGroupoid.equivOfHom
            (smallFinBijEquivalence.functor.map f))
          (FinBijGroupoid.equivOfHom
            (smallFinBijEquivalence.functor.map g))).trans
          (split X' Y').symm) := by
  dsimp only
  ext z
  rfl

/-- Identity law for the shared ordered block-sum arrow implementation. -/
theorem blockSumEquiv_refl (X Y : SmallFinBijGroupoid) :
    blockSumHom (𝟙 X) (𝟙 Y) = 𝟙 (blockSumObj X Y) := by
  apply Core.hom_ext
  simp only [blockSumHom, Core.isoMk_hom_iso,
    coreCategory_id_iso]
  funext z
  apply (blockSumEquiv X Y).injective
  rw [(blockSumEquiv X Y).apply_symm_apply]
  have hid : (Iso.refl (blockSumObj X Y).of).hom z = z := rfl
  rw [hid]
  rcases blockSumEquiv X Y z with z | z <;> rfl

/-- Composition law for the shared ordered block-sum arrow implementation. -/
theorem blockSumEquiv_comp
    {X X' X'' Y Y' Y'' : SmallFinBijGroupoid}
    (f : X ⟶ X') (f' : X' ⟶ X'')
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    blockSumHom f g ≫ blockSumHom f' g' =
      blockSumHom (f ≫ f') (g ≫ g') := by
  apply Core.hom_ext
  simp only [blockSumHom, Core.isoMk_hom_iso,
    coreCategory_comp_iso, Iso.trans_hom]
  funext z
  change (blockSumEquiv X'' Y'').symm
      (Sum.map f'.iso.hom g'.iso.hom
        (blockSumEquiv X' Y'
          ((blockSumEquiv X' Y').symm
            (Sum.map f.iso.hom g.iso.hom (blockSumEquiv X Y z))))) =
    (blockSumEquiv X'' Y'').symm
      (Sum.map (f'.iso.hom ∘ f.iso.hom) (g'.iso.hom ∘ g.iso.hom) (blockSumEquiv X Y z))
  apply (blockSumEquiv X'' Y'').injective
  rw [(blockSumEquiv X'' Y'').apply_symm_apply]
  rw [(blockSumEquiv X' Y').apply_symm_apply]
  rw [(blockSumEquiv X'' Y'').apply_symm_apply]
  rcases blockSumEquiv X Y z with z | z <;> rfl

/-- The shared associator of the original three ordered finite blocks. -/
def associatorEquiv (X Y Z : SmallFinBijGroupoid) :
    ULift.{0, 0} (Fin (blockSumObj (blockSumObj X Y) Z).of.len) ≃
      ULift.{0, 0} (Fin (blockSumObj X (blockSumObj Y Z)).of.len) :=
  (blockSumEquiv (blockSumObj X Y) Z).trans <|
    (Equiv.sumCongr (blockSumEquiv X Y) (Equiv.refl _)).trans <|
      (Equiv.sumAssoc _ _ _).trans <|
        (Equiv.sumCongr (Equiv.refl _) (blockSumEquiv Y Z).symm).trans
          (blockSumEquiv X (blockSumObj Y Z)).symm

/-- The shared deletion of the original empty left block. -/
def leftUnitorEquiv (X : SmallFinBijGroupoid) :
    ULift.{0, 0} (Fin (blockSumObj ⟨FintypeCat.Skeleton.mk 0⟩ X).of.len) ≃
      ULift.{0, 0} (Fin X.of.len) := by
  letI : IsEmpty
      (ULift.{0, 0} (Fin (FintypeCat.Skeleton.mk 0).len)) :=
    ⟨fun z => Fin.elim0 z.down⟩
  exact (blockSumEquiv ⟨FintypeCat.Skeleton.mk 0⟩ X).trans
    (Equiv.emptySum _ _)

/-- The shared original exchange of the two ordered finite blocks. -/
def braidingEquiv (X Y : SmallFinBijGroupoid) :
    ULift.{0, 0} (Fin (blockSumObj X Y).of.len) ≃
      ULift.{0, 0} (Fin (blockSumObj Y X).of.len) :=
  (blockSumEquiv X Y).trans <|
    (Equiv.sumComm _ _).trans (blockSumEquiv Y X).symm

/-- Turn the shared finite coordinate equivalence into its original core isomorphism. -/
abbrev mkCoreIso {X Y : SmallFinBijGroupoid}
    (e : ULift.{0, 0} (Fin X.of.len) ≃
      ULift.{0, 0} (Fin Y.of.len)) : X ≅ Y :=
  Core.isoMk
    { hom := e
      inv := e.symm
      hom_inv_id := by
        funext z
        exact e.symm_apply_apply z
      inv_hom_id := by
        funext z
        exact e.apply_symm_apply z }

/-- The shared deletion of the original empty right block. -/
def rightUnitorEquiv (X : SmallFinBijGroupoid) :
    ULift.{0, 0}
        (Fin (blockSumObj X ⟨FintypeCat.Skeleton.mk 0⟩).of.len) ≃
      ULift.{0, 0} (Fin X.of.len) := by
  letI : IsEmpty
      (ULift.{0, 0} (Fin (FintypeCat.Skeleton.mk 0).len)) :=
    ⟨fun z => Fin.elim0 z.down⟩
  exact (blockSumEquiv X ⟨FintypeCat.Skeleton.mk 0⟩).trans
    (Equiv.sumEmpty _ _)

/-- Full pointwise computation of the shared ordered block-sum arrow. -/
theorem blockSumHom_apply {A A' B B' : SmallFinBijGroupoid}
    (f : A ⟶ A') (g : B ⟶ B')
    (z : ULift.{0, 0} (Fin (blockSumObj A B).of.len)) :
    (blockSumHom f g).iso.hom z =
      (blockSumEquiv A' B').symm
        (Sum.map f.iso.hom g.iso.hom (blockSumEquiv A B z)) := by
  have h := congrArg
    (fun e : (smallFinBijEquivalence.functor.obj (blockSumObj A B)).of ≃
        (smallFinBijEquivalence.functor.obj (blockSumObj A' B')).of => e z)
    (blockSumHom_equivOfHom f g)
  change (blockSumHom f g).iso.hom z =
    (blockSumEquiv A' B').symm
      (Sum.map f.iso.hom g.iso.hom (blockSumEquiv A B z)) at h
  exact h

noncomputable instance instMonoidalCategory :
    MonoidalCategory SmallFinBijGroupoid := by
  letI : MonoidalCategoryStruct SmallFinBijGroupoid :=
    { tensorObj := blockSumObj
      whiskerLeft := fun X _ _ f => blockSumHom (𝟙 X) f
      whiskerRight := fun f Y => blockSumHom f (𝟙 Y)
      tensorHom := blockSumHom
      tensorUnit := ⟨FintypeCat.Skeleton.mk 0⟩
      associator := fun X Y Z => mkCoreIso (associatorEquiv X Y Z)
      leftUnitor := fun X => mkCoreIso (leftUnitorEquiv X)
      rightUnitor := fun X => mkCoreIso (rightUnitorEquiv X) }
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := blockSumEquiv_refl)
    (id_tensorHom := fun X _ _ f => rfl)
    (tensorHom_id := fun f Y => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      blockSumEquiv_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      change blockSumHom (blockSumHom f₁ f₂) f₃ ≫
          (mkCoreIso (associatorEquiv Y₁ Y₂ Y₃)).hom =
        (mkCoreIso (associatorEquiv X₁ X₂ X₃)).hom ≫
          blockSumHom f₁ (blockSumHom f₂ f₃)
      apply Core.hom_ext
      dsimp only [mkCoreIso]
      simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
        Iso.trans_hom]
      funext z
      dsimp only [CategoryStruct.comp, Function.comp_apply]
      simp only [blockSumHom_apply]
      dsimp only [CategoryStruct.comp, Function.comp_apply,
        associatorEquiv, leftUnitorEquiv, rightUnitorEquiv]
      apply (blockSumEquiv Y₁ (blockSumObj Y₂ Y₃)).injective
      simp only [Equiv.trans_apply,
        Equiv.apply_symm_apply]
      let w := blockSumEquiv (blockSumObj X₁ X₂) X₃ z
      have hz : (blockSumEquiv (blockSumObj X₁ X₂) X₃).symm w = z :=
        (blockSumEquiv (blockSumObj X₁ X₂) X₃).symm_apply_apply z
      rw [← hz]
      rcases w with xy | x₃
      · let q := blockSumEquiv X₁ X₂ xy
        have hq : (blockSumEquiv X₁ X₂).symm q = xy :=
          (blockSumEquiv X₁ X₂).symm_apply_apply xy
        rw [← hq]
        rcases q with x₁ | x₂
        · simp only [blockSumHom_apply, Equiv.sumCongr_apply, Sum.map_inl,
            Equiv.sumAssoc_apply_inl_inl, Equiv.refl_apply,
            Equiv.apply_symm_apply]
        · simp only [blockSumHom_apply, Equiv.sumCongr_apply,
            Sum.map_inl, Sum.map_inr,
            Equiv.sumAssoc_apply_inl_inr,
            Equiv.apply_symm_apply]
      · simp only [blockSumHom_apply, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.sumAssoc_apply_inr, Equiv.refl_apply,
          Equiv.apply_symm_apply])
    (leftUnitor_naturality := by
      intro X Y f
      change blockSumHom (𝟙 (⟨FintypeCat.Skeleton.mk 0⟩ :
          SmallFinBijGroupoid)) f ≫
          (mkCoreIso (leftUnitorEquiv Y)).hom =
        (mkCoreIso (leftUnitorEquiv X)).hom ≫ f
      apply Core.hom_ext
      dsimp only [mkCoreIso]
      simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
        Iso.trans_hom]
      funext z
      dsimp only [CategoryStruct.comp, Function.comp_apply]
      simp only [blockSumHom_apply]
      simp only [coreCategory_id_iso, Iso.refl_hom]
      dsimp only [CategoryStruct.comp, Function.comp_apply,
        associatorEquiv, leftUnitorEquiv, rightUnitorEquiv]
      let w := blockSumEquiv ⟨FintypeCat.Skeleton.mk 0⟩ X z
      have hz : (blockSumEquiv ⟨FintypeCat.Skeleton.mk 0⟩ X).symm w = z :=
        (blockSumEquiv ⟨FintypeCat.Skeleton.mk 0⟩ X).symm_apply_apply z
      rw [← hz]
      rw [(blockSumEquiv ⟨FintypeCat.Skeleton.mk 0⟩ X).apply_symm_apply]
      rcases w with z₀ | x
      · exact Fin.elim0 (show Fin 0 from z₀.down)
      · simp only [Equiv.trans_apply, Sum.map_inr,
          Equiv.apply_symm_apply, Equiv.emptySum_apply_inr])
    (rightUnitor_naturality := by
      intro X Y f
      change blockSumHom f (𝟙 (⟨FintypeCat.Skeleton.mk 0⟩ :
          SmallFinBijGroupoid)) ≫
          (mkCoreIso (rightUnitorEquiv Y)).hom =
        (mkCoreIso (rightUnitorEquiv X)).hom ≫ f
      apply Core.hom_ext
      dsimp only [mkCoreIso]
      simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
        Iso.trans_hom]
      funext z
      dsimp only [CategoryStruct.comp, Function.comp_apply]
      simp only [blockSumHom_apply]
      simp only [coreCategory_id_iso, Iso.refl_hom]
      dsimp only [CategoryStruct.comp, Function.comp_apply,
        associatorEquiv, leftUnitorEquiv, rightUnitorEquiv]
      let w := blockSumEquiv X ⟨FintypeCat.Skeleton.mk 0⟩ z
      have hz : (blockSumEquiv X ⟨FintypeCat.Skeleton.mk 0⟩).symm w = z :=
        (blockSumEquiv X ⟨FintypeCat.Skeleton.mk 0⟩).symm_apply_apply z
      rw [← hz]
      simp only [Equiv.apply_symm_apply]
      rcases w with x | z₀
      · simp only [Equiv.trans_apply, Sum.map_inl,
          Equiv.apply_symm_apply, Equiv.sumEmpty_apply_inl]
      · change ULift (Fin 0) at z₀
        exact Fin.elim0 z₀.down)
    (pentagon := by
      intro W X Y Z
      change blockSumHom (mkCoreIso (associatorEquiv W X Y)).hom (𝟙 Z) ≫
          (mkCoreIso (associatorEquiv W (blockSumObj X Y) Z)).hom ≫
            blockSumHom (𝟙 W) (mkCoreIso (associatorEquiv X Y Z)).hom =
        (mkCoreIso (associatorEquiv (blockSumObj W X) Y Z)).hom ≫
          (mkCoreIso (associatorEquiv W X (blockSumObj Y Z))).hom
      apply Core.hom_ext
      dsimp only [mkCoreIso]
      simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
        Iso.trans_hom]
      funext z
      dsimp only [CategoryStruct.comp, Function.comp_apply]
      simp only [blockSumHom_apply]
      simp only [Core.isoMk_hom_iso, coreCategory_id_iso, Iso.refl_hom]
      dsimp only [CategoryStruct.comp, Function.comp_apply,
        associatorEquiv, leftUnitorEquiv, rightUnitorEquiv]
      apply (blockSumEquiv W (blockSumObj X (blockSumObj Y Z))).injective
      rw [(blockSumEquiv W (blockSumObj X (blockSumObj Y Z))).apply_symm_apply]
      let q := blockSumEquiv (blockSumObj (blockSumObj W X) Y) Z z
      have hz :
          (blockSumEquiv (blockSumObj (blockSumObj W X) Y) Z).symm q = z :=
        (blockSumEquiv (blockSumObj (blockSumObj W X) Y) Z).symm_apply_apply z
      rw [← hz]
      simp only [Equiv.apply_symm_apply]
      rcases q with wxy | z
      · let q' := blockSumEquiv (blockSumObj W X) Y wxy
        have hq' : (blockSumEquiv (blockSumObj W X) Y).symm q' = wxy :=
          (blockSumEquiv (blockSumObj W X) Y).symm_apply_apply wxy
        rw [← hq']
        rcases q' with wx | y
        · let q'' := blockSumEquiv W X wx
          have hq'' : (blockSumEquiv W X).symm q'' = wx :=
            (blockSumEquiv W X).symm_apply_apply wx
          rw [← hq'']
          rcases q'' with w | x
          · have hid : (𝟙 W.of) w = w := rfl
            simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
              Sum.map_inl, Equiv.sumAssoc_apply_inl_inl,
              Equiv.refl_apply, Equiv.apply_symm_apply]
            exact congrArg Sum.inl hid
          · simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
              Sum.map_inl, Sum.map_inr, Equiv.sumAssoc_apply_inl_inl,
              Equiv.sumAssoc_apply_inl_inr, Equiv.refl_apply,
              Equiv.apply_symm_apply]
        · simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
            Sum.map_inl, Sum.map_inr, Equiv.sumAssoc_apply_inl_inr,
            Equiv.sumAssoc_apply_inr, Equiv.refl_apply,
            Equiv.apply_symm_apply]
      · have hid : (𝟙 Z.of) z = z := rfl
        simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
          Sum.map_inr, Equiv.sumAssoc_apply_inr, Equiv.refl_apply,
          Equiv.apply_symm_apply, hid])
    (triangle := by
      intro X Y
      change (mkCoreIso (associatorEquiv X
          ⟨FintypeCat.Skeleton.mk 0⟩ Y)).hom ≫
          blockSumHom (𝟙 X) (mkCoreIso (leftUnitorEquiv Y)).hom =
        blockSumHom (mkCoreIso (rightUnitorEquiv X)).hom (𝟙 Y)
      apply Core.hom_ext
      dsimp only [mkCoreIso]
      simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
        Iso.trans_hom]
      funext z
      dsimp only [CategoryStruct.comp, Function.comp_apply]
      simp only [blockSumHom_apply]
      simp only [Core.isoMk_hom_iso, coreCategory_id_iso, Iso.refl_hom]
      dsimp only [CategoryStruct.comp, Function.comp_apply,
        associatorEquiv, leftUnitorEquiv, rightUnitorEquiv]
      apply (blockSumEquiv X Y).injective
      rw [(blockSumEquiv X Y).apply_symm_apply]
      let q := blockSumEquiv
        (blockSumObj X ⟨FintypeCat.Skeleton.mk 0⟩) Y z
      have hz : (blockSumEquiv
          (blockSumObj X ⟨FintypeCat.Skeleton.mk 0⟩) Y).symm q = z :=
        (blockSumEquiv
          (blockSumObj X ⟨FintypeCat.Skeleton.mk 0⟩) Y).symm_apply_apply z
      rw [← hz]
      simp only [Equiv.apply_symm_apply]
      rcases q with xu | y
      · let q' := blockSumEquiv X ⟨FintypeCat.Skeleton.mk 0⟩ xu
        have hq' : (blockSumEquiv X ⟨FintypeCat.Skeleton.mk 0⟩).symm q' = xu :=
          (blockSumEquiv X ⟨FintypeCat.Skeleton.mk 0⟩).symm_apply_apply xu
        rw [← hq']
        rcases q' with x | z₀
        · have hid : (𝟙 X.of) x = x := rfl
          simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
            Equiv.sumAssoc_apply_inl_inl, Equiv.refl_apply,
            Sum.map_inl, Equiv.sumEmpty_apply_inl,
            Equiv.apply_symm_apply]
          exact congrArg Sum.inl hid
        · exact Fin.elim0 (show Fin 0 from z₀.down)
      · have hid : (𝟙 Y.of) y = y := rfl
        simp only [Equiv.trans_apply, Equiv.sumCongr_apply,
          Equiv.sumAssoc_apply_inr, Equiv.refl_apply, Sum.map_inr,
          Equiv.emptySum_apply_inr, Equiv.apply_symm_apply, hid])

noncomputable instance instSymmetricCategory :
    SymmetricCategory SmallFinBijGroupoid := by
  have mkCoreIso_hom {A B : SmallFinBijGroupoid}
      (e : ULift.{0, 0} (Fin A.of.len) ≃
        ULift.{0, 0} (Fin B.of.len)) :
      (mkCoreIso e).hom.iso.hom = e := rfl
  have block_inl {A A' B B' : SmallFinBijGroupoid}
      (f : A ⟶ A') (g : B ⟶ B')
      (a : ULift.{0, 0} (Fin A.of.len)) :
      (blockSumHom f g).iso.hom
          ((blockSumEquiv A B).symm (Sum.inl a)) =
        (blockSumEquiv A' B').symm (Sum.inl (f.iso.hom a)) := by
    apply (blockSumEquiv A' B').injective
    simp only [blockSumHom_apply, Equiv.apply_symm_apply, Sum.map_inl]
  have block_inr {A A' B B' : SmallFinBijGroupoid}
      (f : A ⟶ A') (g : B ⟶ B')
      (b : ULift.{0, 0} (Fin B.of.len)) :
      (blockSumHom f g).iso.hom
          ((blockSumEquiv A B).symm (Sum.inr b)) =
        (blockSumEquiv A' B').symm (Sum.inr (g.iso.hom b)) := by
    apply (blockSumEquiv A' B').injective
    simp only [blockSumHom_apply, Equiv.apply_symm_apply, Sum.map_inr]
  have assoc_inl_inl (A B C : SmallFinBijGroupoid)
      (a : ULift.{0, 0} (Fin A.of.len)) :
      associatorEquiv A B C
          ((blockSumEquiv (blockSumObj A B) C).symm
            (Sum.inl ((blockSumEquiv A B).symm (Sum.inl a)))) =
        (blockSumEquiv A (blockSumObj B C)).symm (Sum.inl a) := by
    apply (blockSumEquiv A (blockSumObj B C)).injective
    simp only [associatorEquiv, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumAssoc_apply_inl_inl, Equiv.refl_apply]
  have assoc_inl_inr (A B C : SmallFinBijGroupoid)
      (b : ULift.{0, 0} (Fin B.of.len)) :
      associatorEquiv A B C
          ((blockSumEquiv (blockSumObj A B) C).symm
            (Sum.inl ((blockSumEquiv A B).symm (Sum.inr b)))) =
        (blockSumEquiv A (blockSumObj B C)).symm
          (Sum.inr ((blockSumEquiv B C).symm (Sum.inl b))) := by
    apply (blockSumEquiv A (blockSumObj B C)).injective
    simp only [associatorEquiv, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr, Equiv.sumAssoc_apply_inl_inr]
  have assoc_inr (A B C : SmallFinBijGroupoid)
      (c : ULift.{0, 0} (Fin C.of.len)) :
      associatorEquiv A B C
          ((blockSumEquiv (blockSumObj A B) C).symm (Sum.inr c)) =
        (blockSumEquiv A (blockSumObj B C)).symm
          (Sum.inr ((blockSumEquiv B C).symm (Sum.inr c))) := by
    apply (blockSumEquiv A (blockSumObj B C)).injective
    simp only [associatorEquiv, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumAssoc_apply_inr, Equiv.refl_apply]
  have assoc_symm_inl_inl (A B C : SmallFinBijGroupoid)
      (a : ULift.{0, 0} (Fin A.of.len)) :
      (associatorEquiv A B C).symm
          ((blockSumEquiv A (blockSumObj B C)).symm (Sum.inl a)) =
        (blockSumEquiv (blockSumObj A B) C).symm
          (Sum.inl ((blockSumEquiv A B).symm (Sum.inl a))) := by
    rw [Equiv.symm_apply_eq]
    exact (assoc_inl_inl A B C a).symm
  have assoc_symm_inl_inr (A B C : SmallFinBijGroupoid)
      (b : ULift.{0, 0} (Fin B.of.len)) :
      (associatorEquiv A B C).symm
          ((blockSumEquiv A (blockSumObj B C)).symm
            (Sum.inr ((blockSumEquiv B C).symm (Sum.inl b)))) =
        (blockSumEquiv (blockSumObj A B) C).symm
          (Sum.inl ((blockSumEquiv A B).symm (Sum.inr b))) := by
    rw [Equiv.symm_apply_eq]
    exact (assoc_inl_inr A B C b).symm
  have assoc_symm_inr (A B C : SmallFinBijGroupoid)
      (c : ULift.{0, 0} (Fin C.of.len)) :
      (associatorEquiv A B C).symm
          ((blockSumEquiv A (blockSumObj B C)).symm
            (Sum.inr ((blockSumEquiv B C).symm (Sum.inr c)))) =
        (blockSumEquiv (blockSumObj A B) C).symm (Sum.inr c) := by
    rw [Equiv.symm_apply_eq]
    exact (assoc_inr A B C c).symm
  have braid_inl (A B : SmallFinBijGroupoid)
      (a : ULift.{0, 0} (Fin A.of.len)) :
      braidingEquiv A B ((blockSumEquiv A B).symm (Sum.inl a)) =
        (blockSumEquiv B A).symm (Sum.inr a) := by
    apply (blockSumEquiv B A).injective
    simp only [braidingEquiv, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumComm_apply]
    rfl
  have braid_inr (A B : SmallFinBijGroupoid)
      (b : ULift.{0, 0} (Fin B.of.len)) :
      braidingEquiv A B ((blockSumEquiv A B).symm (Sum.inr b)) =
        (blockSumEquiv B A).symm (Sum.inl b) := by
    apply (blockSumEquiv B A).injective
    simp only [braidingEquiv, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumComm_apply]
    rfl
  exact
    { braiding := fun X Y => mkCoreIso (braidingEquiv X Y)
      braiding_naturality_right := by
        intro X Y Z f
        change blockSumHom (𝟙 X) f ≫
            (mkCoreIso (braidingEquiv X Z)).hom =
          (mkCoreIso (braidingEquiv X Y)).hom ≫
            blockSumHom f (𝟙 X)
        apply Core.hom_ext
        dsimp only [mkCoreIso]
        simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
          Iso.trans_hom]
        funext z
        simp only [CategoryStruct.comp, Function.comp_apply]
        simp only [blockSumHom_apply]
        simp only [coreCategory_id_iso, Iso.refl_hom]
        apply (blockSumEquiv Z X).injective
        simp only [braidingEquiv, Equiv.trans_apply,
          Equiv.apply_symm_apply]
        let w := blockSumEquiv X Y z
        have hz : (blockSumEquiv X Y).symm w = z :=
          (blockSumEquiv X Y).symm_apply_apply z
        rw [← hz]
        simp only [Equiv.apply_symm_apply]
        rcases w with x | y
        · simp [Sum.swap]
        · simp [Sum.swap]
      braiding_naturality_left := by
        intro X Y f Z
        change blockSumHom f (𝟙 Z) ≫
            (mkCoreIso (braidingEquiv Y Z)).hom =
          (mkCoreIso (braidingEquiv X Z)).hom ≫
            blockSumHom (𝟙 Z) f
        apply Core.hom_ext
        dsimp only [mkCoreIso]
        simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
          Iso.trans_hom]
        funext z
        simp only [CategoryStruct.comp, Function.comp_apply]
        simp only [blockSumHom_apply]
        simp only [coreCategory_id_iso, Iso.refl_hom]
        apply (blockSumEquiv Z Y).injective
        simp only [braidingEquiv, Equiv.trans_apply,
          Equiv.apply_symm_apply]
        let w := blockSumEquiv X Z z
        have hz : (blockSumEquiv X Z).symm w = z :=
          (blockSumEquiv X Z).symm_apply_apply z
        rw [← hz]
        simp only [Equiv.apply_symm_apply]
        rcases w with x | z
        · simp [Sum.swap]
        · simp [Sum.swap]
      hexagon_forward := by
        intro X Y Z
        change (show (blockSumObj (blockSumObj X Y) Z) ⟶
              blockSumObj X (blockSumObj Y Z) from
            (mkCoreIso (associatorEquiv X Y Z)).hom) ≫
              (mkCoreIso (braidingEquiv X (blockSumObj Y Z))).hom ≫
                (mkCoreIso (associatorEquiv Y Z X)).hom =
          blockSumHom (mkCoreIso (braidingEquiv X Y)).hom (𝟙 Z) ≫
            (mkCoreIso (associatorEquiv Y X Z)).hom ≫
              blockSumHom (𝟙 Y) (mkCoreIso (braidingEquiv X Z)).hom
        apply Core.hom_ext
        dsimp only [mkCoreIso]
        simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
          Iso.trans_hom]
        funext z
        simp only [CategoryStruct.comp, Function.comp_apply]
        let q := blockSumEquiv (blockSumObj X Y) Z z
        have hz : (blockSumEquiv (blockSumObj X Y) Z).symm q = z :=
          (blockSumEquiv (blockSumObj X Y) Z).symm_apply_apply z
        rw [← hz]
        rcases q with xy | z
        · let q' := blockSumEquiv X Y xy
          have hq' : (blockSumEquiv X Y).symm q' = xy :=
            (blockSumEquiv X Y).symm_apply_apply xy
          rw [← hq']
          rcases q' with x | y
          · rw [assoc_inl_inl, braid_inl, assoc_inr,
              block_inl, mkCoreIso_hom, braid_inl, assoc_inl_inr,
              block_inr, mkCoreIso_hom, braid_inl]
          · rw [assoc_inl_inr, braid_inr, assoc_inl_inl,
              block_inl, mkCoreIso_hom, braid_inr, assoc_inl_inl,
              block_inl]
            have hid : (𝟙 Y : Y ⟶ Y).iso.hom y = y := rfl
            rw [hid]
        · rw [assoc_inr, braid_inr, assoc_inl_inr,
            block_inr, assoc_inr, block_inr, mkCoreIso_hom, braid_inr]
          have hid : (𝟙 Z : Z ⟶ Z).iso.hom z = z := rfl
          rw [hid]
      hexagon_reverse := by
        intro X Y Z
        change (mkCoreIso (associatorEquiv X Y Z)).inv ≫
              (mkCoreIso (braidingEquiv (blockSumObj X Y) Z)).hom ≫
                (mkCoreIso (associatorEquiv Z X Y)).inv =
          blockSumHom (𝟙 X) (mkCoreIso (braidingEquiv Y Z)).hom ≫
            (mkCoreIso (associatorEquiv X Z Y)).inv ≫
              blockSumHom (mkCoreIso (braidingEquiv X Z)).hom (𝟙 Y)
        apply Core.hom_ext
        dsimp only [mkCoreIso]
        simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
          Core.isoMk_inv_iso, Iso.symm_hom, Iso.trans_hom]
        funext z
        simp only [CategoryStruct.comp, Function.comp_apply]
        let q := blockSumEquiv X (blockSumObj Y Z) z
        have hz : (blockSumEquiv X (blockSumObj Y Z)).symm q = z :=
          (blockSumEquiv X (blockSumObj Y Z)).symm_apply_apply z
        rw [← hz]
        rcases q with x | yz
        · rw [assoc_symm_inl_inl, braid_inl,
            assoc_symm_inl_inr, block_inl,
            assoc_symm_inl_inl, block_inl, mkCoreIso_hom, braid_inl]
          have hid : (𝟙 X : X ⟶ X).iso.hom x = x := rfl
          rw [hid]
        · let q' := blockSumEquiv Y Z yz
          have hq' : (blockSumEquiv Y Z).symm q' = yz :=
            (blockSumEquiv Y Z).symm_apply_apply yz
          rw [← hq']
          rcases q' with y | z
          · rw [assoc_symm_inl_inr, braid_inl,
              assoc_symm_inr, block_inr, mkCoreIso_hom, braid_inl,
              assoc_symm_inr, block_inr]
            have hid : (𝟙 Y : Y ⟶ Y).iso.hom y = y := rfl
            rw [hid]
          · rw [assoc_symm_inr, braid_inr,
              assoc_symm_inl_inl, block_inr, mkCoreIso_hom, braid_inr,
              assoc_symm_inl_inr, block_inl, mkCoreIso_hom, braid_inr]
      symmetry := by
        intro X Y
        change (mkCoreIso (braidingEquiv X Y)).hom ≫
            (mkCoreIso (braidingEquiv Y X)).hom = 𝟙 (blockSumObj X Y)
        apply Core.hom_ext
        dsimp only [mkCoreIso]
        simp only [coreCategory_comp_iso, Core.isoMk_hom_iso,
          Iso.trans_hom, coreCategory_id_iso, Iso.refl_hom]
        funext z
        simp only [CategoryStruct.comp, Function.comp_apply,
          braidingEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
        let w := blockSumEquiv X Y z
        have hz : (blockSumEquiv X Y).symm w = z :=
          (blockSumEquiv X Y).symm_apply_apply z
        rw [← hz]
        have hid : (𝟙 (blockSumObj X Y).of)
            ((blockSumEquiv X Y).symm w) =
              (blockSumEquiv X Y).symm w := rfl
        rw [hid]
        apply (blockSumEquiv X Y).injective
        rw [(blockSumEquiv X Y).apply_symm_apply]
        rcases w with x | y
        · rw [(blockSumEquiv X Y).apply_symm_apply]
          rfl
        · rw [(blockSumEquiv X Y).apply_symm_apply]
          rfl }

theorem braiding_equivOfHom (X Y : SmallFinBijGroupoid) :
    FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map (β_ X Y).hom) =
      Equiv.ulift.trans (finAddFlip.trans Equiv.ulift.symm) := by
  change braidingEquiv X Y = _
  have h :
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm).trans
          ((Equiv.sumComm
              (ULift.{0, 0} (Fin X.of.len))
              (ULift.{0, 0} (Fin Y.of.len))).trans
            (Equiv.sumCongr Equiv.ulift Equiv.ulift)) =
        Equiv.sumComm (Fin X.of.len) (Fin Y.of.len) := by
    ext z
    rcases z with x | y <;> rfl
  have h' :
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm).trans
          ((Equiv.sumComm
              (ULift.{0, 0} (Fin X.of.len))
              (ULift.{0, 0} (Fin Y.of.len))).trans
            ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
              (finSumFinEquiv.trans Equiv.ulift.symm))) =
        (Equiv.sumComm (Fin X.of.len) (Fin Y.of.len)).trans
          (finSumFinEquiv.trans Equiv.ulift.symm) := by
    rw [← Equiv.trans_assoc
      (Equiv.sumComm
        (ULift.{0, 0} (Fin X.of.len))
        (ULift.{0, 0} (Fin Y.of.len)))
      (Equiv.sumCongr Equiv.ulift Equiv.ulift)
      (finSumFinEquiv.trans Equiv.ulift.symm)]
    rw [← Equiv.trans_assoc
      (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm)
      ((Equiv.sumComm
        (ULift.{0, 0} (Fin X.of.len))
        (ULift.{0, 0} (Fin Y.of.len))).trans
          (Equiv.sumCongr Equiv.ulift Equiv.ulift))
      (finSumFinEquiv.trans Equiv.ulift.symm)]
    rw [h]
  change Equiv.ulift.trans
      (finSumFinEquiv.symm.trans
        ((Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm).trans
          ((Equiv.sumComm
              (ULift.{0, 0} (Fin X.of.len))
              (ULift.{0, 0} (Fin Y.of.len))).trans
            ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
              (finSumFinEquiv.trans Equiv.ulift.symm))))) =
    Equiv.ulift.trans
      (finSumFinEquiv.symm.trans
        ((Equiv.sumComm (Fin X.of.len) (Fin Y.of.len)).trans
          (finSumFinEquiv.trans Equiv.ulift.symm)))
  rw [h']

end SmallFinBijGroupoid

universe v u

variable {C : Type u} [Category.{v} C]

namespace SymmetricCollection

/-- Restrict an original symmetric collection along the finite skeleton equivalence. -/
def restrictSmall (X : SymmetricCollection C) :
    CategoryTheory.Functor SmallFinBijGroupoid C :=
  smallFinBijEquivalence.functor ⋙ X

@[simp]
theorem restrictSmall_obj (X : SymmetricCollection C)
    (A : SmallFinBijGroupoid) :
    X.restrictSmall.obj A =
      X.obj (smallFinBijEquivalence.functor.obj A) :=
  rfl

@[simp]
theorem restrictSmall_map (X : SymmetricCollection C)
    {A B : SmallFinBijGroupoid} (f : A ⟶ B) :
    X.restrictSmall.map f =
      X.map (smallFinBijEquivalence.functor.map f) :=
  rfl

end SymmetricCollection

end CategoryTheory.Operad
