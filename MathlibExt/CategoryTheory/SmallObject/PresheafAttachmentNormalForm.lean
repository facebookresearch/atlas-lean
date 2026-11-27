/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.Types.PushoutComplement
public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Original labelled presheaf attachment normal form

The actual native Arrow attachment consists objectwise of old points and one
complementary point for each whole original generator square. Its maps retain
the original generator, top/bottom maps and both pushout legs. Original labels
can lie in a larger universe while small in the value universe; Shrink is used
only internally and every original label is recovered.

The elementary Type pushout proof is shared by the neutral PushoutComplement
API; no second filler functor or Type proof is constructed. This implements the
explicit set/presheaf calculation underlying the Hirschhorn localization bridge.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w s
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
namespace CategoryTheory.SmallObject
variable {D : Type w} [SmallCategory D]
    {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)

/-- The actual attachment is old points plus each original labelled complementary point. -/
def presheafAttachmentEquiv {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (d : Dᵒᵖ) [∀ i, Mono (j i)] :
    (X.obj d ⊕ Σ q : FunctorObjIndex j p,
      {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) ≃
        (functorObj j p).obj d := by
  classical
  let originalCell (p : X ⟶ Y)
      (q : FunctorObjIndex j p) : B q.i ⟶ functorObj j p :=
    Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p
  let objectCofan {J : Type (max u w)}
      (F : J → Dᵒᵖ ⥤ Type (max u w)) (c : Cofan F) (d : Dᵒᵖ) :
      Cofan (fun q => (F q).obj d) :=
    Cofan.mk (c.pt.obj d) (fun q => (c.inj q).app d)
  let objectCofanIsColimit {J : Type (max u w)}
      {F : J → Dᵒᵖ ⥤ Type (max u w)} {c : Cofan F}
      (hc : IsColimit c) (d : Dᵒᵖ) : IsColimit (objectCofan F c d) :=
    isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj d) F (fun q => c.inj q) hc
  let objectCofanEquiv {J : Type (max u w)}
      {F : J → Dᵒᵖ ⥤ Type (max u w)} {c : Cofan F}
      (hc : IsColimit c) (d : Dᵒᵖ) : (Σ q, (F q).obj d) ≃ c.pt.obj d :=
    CofanTypes.equivOfIsColimit
      ((Cofan.isColimit_cofanTypes_iff (objectCofan F c d)).2 ⟨objectCofanIsColimit hc d⟩)
  have objectCofanEquiv_apply {J : Type (max u w)}
      {F : J → Dᵒᵖ ⥤ Type (max u w)} {c : Cofan F}
      (hc : IsColimit c) (d : Dᵒᵖ) (q : J) (x : (F q).obj d) :
      objectCofanEquiv hc d ⟨q, x⟩ = (c.inj q).app d x := rfl
  let smallAttachment  (p : X ⟶ Y) :
      AttachCells.{max u w} j (ιFunctorObj j p) :=
    attachCellsιFunctorObjOfSmall.{max u w, s, max u w, max (u + 1) (w + 1)} j p
  have smallAttachment_cell  (p : X ⟶ Y)
      (q : Shrink.{max u w} (FunctorObjIndex j p)) :
      (smallAttachment p).cell q = originalCell p ((equivShrink.{max u w} _).symm q) := rfl
  have original_labelled_pushout
      (p : X ⟶ Y) (d : Dᵒᵖ) :
      let c := smallAttachment p
      IsPushout
        (↾fun z : Σ q : c.ι, (A (c.π q)).obj d =>
          (((equivShrink.{max u w} (FunctorObjIndex j p)).symm z.1).t).app d z.2)
        (↾fun z : Σ q : c.ι, (A (c.π q)).obj d =>
          (⟨z.1, (j (c.π z.1)).app d z.2⟩ : Σ q : c.ι, (B (c.π q)).obj d))
        ((ιFunctorObj j p).app d)
        (↾fun z : Σ q : c.ι, (B (c.π q)).obj d => (c.cell z.1).app d z.2) := by
    let c := smallAttachment p
    let e₁ := objectCofanEquiv c.isColimit₁ d
    let e₂ := objectCofanEquiv c.isColimit₂ d
    have hp := c.isPushout.map ((evaluation _ _).obj d)
    apply hp.of_iso e₁.toIso.symm (Iso.refl _) e₂.toIso.symm (Iso.refl _)
    · apply ConcreteCategory.hom_ext
      intro z
      obtain ⟨q, rfl⟩ := e₁.surjective z
      change c.g₁.app d (e₁ q) =
        (((equivShrink.{max u w} (FunctorObjIndex j p)).symm (e₁.symm (e₁ q)).1).t).app d
          (e₁.symm (e₁ q)).2
      rw [Equiv.symm_apply_apply]
      rw [objectCofanEquiv_apply (F := fun q => A (c.π q)) (c := c.cofan₁) c.isColimit₁ d q.1 q.2]
      change ((Sigma.ι (functorObjSrcFamily j p)
          ((equivShrink.{max u w} _).symm q.1) ≫ functorObjTop j p).app d) q.2 = _
      simp only [functorObjTop, Sigma.ι_comp_desc]
    · apply ConcreteCategory.hom_ext
      intro z
      obtain ⟨q, rfl⟩ := e₁.surjective z
      change e₂.symm (c.m.app d (e₁ q)) =
        ⟨(e₁.symm (e₁ q)).1, (j (c.π (e₁.symm (e₁ q)).1)).app d (e₁.symm (e₁ q)).2⟩
      rw [Equiv.symm_apply_apply]
      apply e₂.injective
      rw [Equiv.apply_symm_apply]
      rw [objectCofanEquiv_apply (F := fun q => A (c.π q)) (c := c.cofan₁) c.isColimit₁ d q.1 q.2,
        objectCofanEquiv_apply (F := fun q => B (c.π q)) (c := c.cofan₂) c.isColimit₂ d q.1
          ((j (c.π q.1)).app d q.2)]
      change ((c.cofan₁.inj q.1 ≫ c.m).app d) q.2 = _
      rw [c.hm]
      rfl
    · simp
    · apply ConcreteCategory.hom_ext
      intro z
      obtain ⟨q, rfl⟩ := e₂.surjective z
      change c.g₂.app d (e₂ q) = (c.cell (e₂.symm (e₂ q)).1).app d (e₂.symm (e₂ q)).2
      rw [Equiv.symm_apply_apply,
        objectCofanEquiv_apply (F := fun q => B (c.π q)) (c := c.cofan₂) c.isColimit₂ d q.1 q.2]
      rfl
  have smallSigmaMap_injective
      (p : X ⟶ Y) (d : Dᵒᵖ)  :
      let c := smallAttachment p
      Function.Injective (fun z : Σ q : c.ι, (A (c.π q)).obj d =>
        (⟨z.1, (j (c.π z.1)).app d z.2⟩ : Σ q : c.ι, (B (c.π q)).obj d)) := by
    dsimp only
    let c := smallAttachment p
    rintro ⟨q, a⟩ ⟨q', a'⟩ h
    obtain rfl : q = q' := congrArg Sigma.fst h
    have hm : Mono ((j (c.π q)).app d) :=
      (NatTrans.mono_iff_mono_app (j (c.π q))).mp inferInstance d
    have hi := (mono_iff_injective ((j (c.π q)).app d)).1 hm
    exact congrArg (Sigma.mk q) (hi (by simpa using h))
  let complementSigmaEquiv {J : Type (max u w)}
      {U V : J → Type (max u w)} (f : ∀ q, U q → V q) :
      (Σ q, {z : V q // z ∉ Set.range (f q)}) ≃
        {z : Σ q, V q // z ∉ Set.range (fun a : Σ q, U q => ⟨a.1, f a.1 a.2⟩)} :=
    { toFun z := ⟨⟨z.1, z.2.val⟩, by
        rintro ⟨⟨q, a⟩, h⟩
        obtain rfl : q = z.1 := congrArg Sigma.fst h
        exact z.2.property ⟨a, by simpa using h⟩⟩
      invFun z := ⟨z.val.1, z.val.2, by
        rintro ⟨a, h⟩
        exact z.property ⟨⟨z.val.1, a⟩, by simp [h]⟩⟩
      left_inv z := rfl
      right_inv z := rfl
    }
  let originalToSmall (p : X ⟶ Y) (d : Dᵒᵖ) :
      (Σ q : FunctorObjIndex j p,
        {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) ≃
      (Σ q : Shrink.{max u w} (FunctorObjIndex j p),
        {z : (B ((equivShrink.{max u w} _).symm q).i).obj d //
          z ∉ Set.range ((j ((equivShrink.{max u w} _).symm q).i).app d)}) :=
    (Equiv.sigmaCongrLeft (equivShrink.{max u w} (FunctorObjIndex j p)).symm).symm
  have original_normal_bijective
      (p : X ⟶ Y) (d : Dᵒᵖ)  :
      Function.Bijective (fun z : X.obj d ⊕ Σ q : FunctorObjIndex j p,
        {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)} =>
        z.elim ((ιFunctorObj j p).app d)
          (fun q => (originalCell p q.1).app d q.2.val)) := by
    let c := smallAttachment p
    let smallEquiv :=
      (Equiv.sumCongr (Equiv.refl _) (complementSigmaEquiv
        (fun q : c.ι => (j (c.π q)).app d))).trans
        (Types.pushoutComplementEquiv (original_labelled_pushout p d)
          (smallSigmaMap_injective p d))
    let e := (Equiv.sumCongr (Equiv.refl _) (originalToSmall p d)).trans smallEquiv
    have he : (e : _ → _) = (fun z => z.elim ((ιFunctorObj j p).app d)
        (fun q => (originalCell p q.1).app d q.2.val)) := by
      funext z
      rcases z with x | ⟨q, z, hz⟩
      · rfl
      · obtain ⟨a, ha⟩ := (originalToSmall p d).symm.surjective ⟨q, z, hz⟩
        change e (Sum.inr ⟨q, z, hz⟩) = (originalCell p q).app d z
        have hright := congrArg
          (fun a => (originalCell p a.1).app d a.2.val) ha
        rw [← hright]
        have hw := congrArg (fun a => e (Sum.inr a)) ha
        rw [← hw]
        change smallEquiv (Sum.inr ((originalToSmall p d) ((originalToSmall p d).symm a))) = _
        rw [Equiv.apply_symm_apply]
        rcases a with ⟨q, z, hz⟩
        change ((smallAttachment p).cell q).app d z = _
        rw [smallAttachment_cell]
        rfl
    rw [← he]
    exact e.bijective
  exact Equiv.ofBijective
    (fun z => z.elim ((ιFunctorObj j p).app d)
      (fun q => (Sigma.ι (functorObjTgtFamily j p) q.1 ≫ ρFunctorObj j p).app d q.2.val))
    (original_normal_bijective p d)

/-- The old branch is the actual native unit. -/
lemma presheafAttachmentEquiv_inl {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (d : Dᵒᵖ) [∀ i, Mono (j i)] (x : X.obj d) :
    presheafAttachmentEquiv j p d (Sum.inl x) = (ιFunctorObj j p).app d x := rfl

/-- The new branch uses the original full labelled cell. -/
lemma presheafAttachmentEquiv_inr {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (d : Dᵒᵖ) [∀ i, Mono (j i)]
    (q : FunctorObjIndex j p) (z : (B q.i).obj d)
    (hz : z ∉ Set.range ((j q.i).app d)) :
    presheafAttachmentEquiv j p d (Sum.inr ⟨q, z, hz⟩) =
      (Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p).app d z := rfl

/-- The original cell retains its whole prescribed top attaching map. -/
lemma presheafAttachmentEquiv_cell_boundary {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (q : FunctorObjIndex j p) :
    j q.i ≫ Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p =
      q.t ≫ ιFunctorObj j p := q.comm

/-- The original cell retains its prescribed bottom map under the right factor. -/
lemma presheafAttachmentEquiv_cell_projection {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (q : FunctorObjIndex j p) :
    (Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p) ≫ πFunctorObj j p = q.b := by
  simp [π'FunctorObj]

/-- Original Arrow maps retain the generator/complement and postcompose both label maps. -/
lemma presheafAttachmentEquiv_naturality {X Y X' Y' : Dᵒᵖ ⥤ Type (max u w)}
    {p : X ⟶ Y} {p' : X' ⟶ Y'} (τ : Arrow.mk p ⟶ Arrow.mk p')
    (d : Dᵒᵖ) [∀ i, Mono (j i)]
    (z : X.obj d ⊕ Σ q : FunctorObjIndex j p,
      {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) :
    (functorMap j τ).app d (presheafAttachmentEquiv j p d z) =
      presheafAttachmentEquiv j p' d
        (z.map (τ.left.app d) (fun q =>
          ⟨FunctorObjIndex.mk q.1.i (q.1.t ≫ τ.left) (q.1.b ≫ τ.right)
            (by
              have hτ : τ.left ≫ p' = p ≫ τ.right := by simpa only [Arrow.mk_hom] using τ.w
              rw [Category.assoc, hτ, ← Category.assoc, q.1.w, Category.assoc]), q.2⟩)) := by
  rcases z with x | ⟨q, z, hz⟩
  · simp only [Sum.map_inl, presheafAttachmentEquiv_inl]
    change ((ιFunctorObj j p ≫ functorMap j τ).app d) x =
      ((τ.left ≫ ιFunctorObj j p').app d) x
    rw [ιFunctorObj_naturality]
  · simp only [Sum.map_inr, presheafAttachmentEquiv_inr]
    have hcell := ι_functorMapTgt_assoc j τ q.i q.t q.b q.w
      (q.b ≫ τ.right) rfl (q.t ≫ τ.left) rfl (ρFunctorObj j p')
    have heq : (Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p) ≫ functorMap j τ =
        Sigma.ι (functorObjTgtFamily j p')
          (FunctorObjIndex.mk q.i (q.t ≫ τ.left) (q.b ≫ τ.right)
            (by
              have hτ : τ.left ≫ p' = p ≫ τ.right := by simpa only [Arrow.mk_hom] using τ.w
              rw [Category.assoc, hτ, ← Category.assoc, q.w, Category.assoc])) ≫
                  ρFunctorObj j p' := by
      simpa [functorMap, pushout.map, pushout.inr_desc, ρFunctorObj] using hcell
    exact ConcreteCategory.congr_hom
      (congrArg (fun f : B q.i ⟶ functorObj j p' => f.app d) heq) z

end CategoryTheory.SmallObject
