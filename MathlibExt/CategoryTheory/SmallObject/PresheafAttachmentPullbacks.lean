/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentNormalForm
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Pullbacks of the original labelled presheaf attachment

The native Arrow attachment retains each original generator square, including
its top and bottom maps, and the complementary point of that generator. Both
endpoint pullbacks glue the new labels; old points use the original left
pullback. Evaluation and the native Arrow cone compare both projections.
The span maps are arbitrary. This is the presheaf calculation used in the
Hirschhorn localization construction, with the scalar labelled normal form
reused through its canonical generic API.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w s
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.SmallObject
variable {D : Type w} [SmallCategory D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)

/-- The actual one-step Arrow attachment preserves all pullbacks of arbitrary spans. -/
theorem presheafAttachment_preservesPullbacks [∀ i, Mono (j i)] :
    PreservesLimitsOfShape WalkingCospan (SmallObject.functor j) := by
  classical
  let π₁ : Arrow (Dᵒᵖ ⥤ Type (max u w)) ⥤ Dᵒᵖ ⥤ Type (max u w) := Comma.fst _ _
  let π₂ : Arrow (Dᵒᵖ ⥤ Type (max u w)) ⥤ Dᵒᵖ ⥤ Type (max u w) := Comma.snd _ _
  have projectionPreserves
      (F : WalkingCospan ⥤ Arrow (Dᵒᵖ ⥤ Type (max u w))) :
      PreservesLimit F π₁ ∧ PreservesLimit F π₂ := by
    let leftCone := limit.cone (F ⋙ Comma.fst _ _)
    let rightCone := limit.cone (F ⋙ Comma.snd _ _)
    let leftLimit := limit.isLimit (F ⋙ Comma.fst _ _)
    let rightLimit := limit.isLimit (F ⋙ Comma.snd _ _)
    let jointCone := Comma.coneOfPreserves F leftCone rightLimit
    have jointLimit : IsLimit jointCone :=
      Comma.coneOfPreservesIsLimit F leftLimit rightLimit
    have leftMapped : IsLimit (π₁.mapCone jointCone) := by
      change IsLimit leftCone
      exact leftLimit
    have rightMapped : IsLimit (π₂.mapCone jointCone) := by
      change IsLimit rightCone
      exact rightLimit
    exact ⟨preservesLimit_of_preserves_limit_cone jointLimit leftMapped,
      preservesLimit_of_preserves_limit_cone jointLimit rightMapped⟩
  let imageLabel {P X : Arrow (Dᵒᵖ ⥤ Type (max u w))}
      (a : P ⟶ X) (q : FunctorObjIndex j P.hom) : FunctorObjIndex j X.hom :=
    ⟨q.i, q.t ≫ a.left,
        q.b ≫ a.right, by rw [Category.assoc, a.w, ← Category.assoc, q.w, Category.assoc]⟩
  let glueOriginalLabel {P X V Y : Arrow (Dᵒᵖ ⥤ Type (max u w))}
      {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
      (hLeft : IsPullback a.left b.left f.left g.left)
      (hRight : IsPullback a.right b.right f.right g.right)
      (qX : FunctorObjIndex j X.hom) (qV : FunctorObjIndex j V.hom)
      (same : imageLabel f qX = imageLabel g qV) :
      {q : FunctorObjIndex j P.hom // imageLabel a q = qX ∧ imageLabel b q = qV} := by
    classical
    rcases qX with ⟨i, tX, bX, wX⟩
    rcases qV with ⟨i', tV, bV, wV⟩
    have hi : i = i' := congrArg FunctorObjIndex.i same
    cases hi
    have components : tX ≫ f.left = tV ≫ g.left ∧ bX ≫ f.right = bV ≫ g.right := by
      simpa only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and] using same
    have ht := components.1
    have hb := components.2
    let top := hLeft.lift tX tV ht
    let bottom := hRight.lift bX bV hb
    have square : top ≫ P.hom = j i ≫ bottom := by
      apply hRight.hom_ext
      · rw [Category.assoc, ← a.w, ← Category.assoc, hLeft.lift_fst,
          wX, Category.assoc, hRight.lift_fst]
      · rw [Category.assoc, ← b.w, ← Category.assoc, hLeft.lift_snd,
          wV, Category.assoc, hRight.lift_snd]
    refine ⟨⟨i, top, bottom, square⟩, ?_, ?_⟩
    · simp [imageLabel, top, bottom]
    · simp [imageLabel, top, bottom]
  have label_joint_injective {P X V Y : Arrow (Dᵒᵖ ⥤ Type (max u w))}
      {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
      (hLeft : IsPullback a.left b.left f.left g.left)
      (hRight : IsPullback a.right b.right f.right g.right)
      {q q' : FunctorObjIndex j P.hom}
      (hX : imageLabel a q = imageLabel a q')
      (hV : imageLabel b q = imageLabel b q') : q = q' := by
    rcases q with ⟨i, t, v, wq⟩
    rcases q' with ⟨i', t', v', wq'⟩
    have hi : i = i' := congrArg FunctorObjIndex.i hX
    cases hi
    have htA : t ≫ a.left = t' ≫ a.left := by
      have h := hX
      simp only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and] at h
      exact h.1
    have htB : t ≫ b.left = t' ≫ b.left := by
      have h := hV
      simp only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and] at h
      exact h.1
    have hvA : v ≫ a.right = v' ≫ a.right := by
      have h := hX
      simp only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and] at h
      exact h.2
    have hvB : v ≫ b.right = v' ≫ b.right := by
      have h := hV
      simp only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and] at h
      exact h.2
    cases hLeft.hom_ext htA htB
    cases hRight.hom_ext hvA hvB
    rfl
  have mappedPullback_left_at {P X V Y : Arrow (Dᵒᵖ ⥤ Type (max u w))}
      {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
      (h : IsPullback a b f g)
      (hLeft : IsPullback a.left b.left f.left g.left)
      (hRight : IsPullback a.right b.right f.right g.right)
      (d : Dᵒᵖ) :
      IsPullback ((functorMap j a).app d) ((functorMap j b).app d)
        ((functorMap j f).app d) ((functorMap j g).app d) := by
    classical
    have hd := hLeft.app d
    refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · have hh := (functor j).congr_map h.w
      have hw : functorMap j a ≫ functorMap j f = functorMap j b ≫ functorMap j g := by
        rw [Functor.map_comp, Functor.map_comp] at hh
        have hw := congrArg Arrow.Hom.left hh
        change functorMap j a ≫ functorMap j f = functorMap j b ≫ functorMap j g at hw
        exact hw
      exact congrArg (fun t => t.app d) hw
    · intro z z' ⟨ha, hb⟩
      obtain ⟨q, rfl⟩ := (presheafAttachmentEquiv j P.hom d).surjective z
      obtain ⟨q', rfl⟩ := (presheafAttachmentEquiv j P.hom d).surjective z'
      erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality] at ha hb
      have hx := (presheafAttachmentEquiv j X.hom d).injective ha
      have hv := (presheafAttachmentEquiv j V.hom d).injective hb
      rcases q with x | ⟨q, z, hz⟩
      · rcases q' with x' | ⟨q', z', hz'⟩
        · have eq := Types.ext_of_isPullback hd (Sum.inl.inj hx) (Sum.inl.inj hv)
          rw [eq]
        · cases hx
      · rcases q' with x' | ⟨q', z', hz'⟩
        · cases hx
        · have hqX := congrArg Sigma.fst (Sum.inr.inj hx)
          have hqV := congrArg Sigma.fst (Sum.inr.inj hv)
          have heq := label_joint_injective hLeft hRight hqX hqV
          cases heq
          have hzEq : (⟨z, hz⟩ : {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) =
              ⟨z', hz'⟩ := by
            simpa using Sum.inr.inj hx
          cases hzEq
          rfl
    · intro zx zv heq
      obtain ⟨qx, rfl⟩ := (presheafAttachmentEquiv j X.hom d).surjective zx
      obtain ⟨qv, rfl⟩ := (presheafAttachmentEquiv j V.hom d).surjective zv
      erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality] at heq
      have hy := (presheafAttachmentEquiv j Y.hom d).injective heq
      rcases qx with x | ⟨qx, z, hz⟩
      · rcases qv with v | ⟨qv, z', hz'⟩
        · obtain ⟨p, hpX, hpV⟩ := Types.exists_of_isPullback hd x v (Sum.inl.inj hy)
          refine ⟨presheafAttachmentEquiv j P.hom d (Sum.inl p), ?_, ?_⟩
          · erw [presheafAttachmentEquiv_naturality]
            simp only [Sum.map_inl, hpX]
          · erw [presheafAttachmentEquiv_naturality]
            simp only [Sum.map_inl, hpV]
        · cases hy
      · rcases qv with v | ⟨qv, z', hz'⟩
        · cases hy
        · rcases qx with ⟨i, tX, bX, wX⟩
          rcases qv with ⟨i', tV, bV, wV⟩
          have hq := congrArg Sigma.fst (Sum.inr.inj hy)
          have hi : i = i' := congrArg FunctorObjIndex.i hq
          cases hi
          let pointLabel : (Σ q : FunctorObjIndex j Y.hom,
              {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) →
              Σ i, {z : (B i).obj d // z ∉ Set.range ((j i).app d)} :=
            fun q => ⟨q.1.i, q.2⟩
          have hzEq : (⟨z, hz⟩ : {z : (B i).obj d // z ∉ Set.range ((j i).app d)}) = ⟨z', hz'⟩ := by
            have hp := congrArg pointLabel (Sum.inr.inj hy)
            simpa only [pointLabel, imageLabel, Sigma.mk.injEq, heq_eq_eq, true_and] using hp
          cases hzEq
          let q := glueOriginalLabel hLeft hRight ⟨i, tX, bX, wX⟩ ⟨i, tV, bV, wV⟩ hq
          refine ⟨presheafAttachmentEquiv j P.hom d (Sum.inr ⟨q.val, z, hz⟩), ?_, ?_⟩
          · erw [presheafAttachmentEquiv_naturality]
            apply congrArg (fun x => presheafAttachmentEquiv j X.hom d (Sum.inr x))
            exact Sigma.ext q.property.1 (HEq.rfl)
          · erw [presheafAttachmentEquiv_naturality]
            apply congrArg (fun x => presheafAttachmentEquiv j V.hom d (Sum.inr x))
            exact Sigma.ext q.property.2 (HEq.rfl)
  have mappedPullback
      {P X V Y : Arrow (Dᵒᵖ ⥤ Type (max u w))}
      {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
      (h : IsPullback a b f g) :
      IsPullback ((SmallObject.functor j).map a) ((SmallObject.functor j).map b)
        ((SmallObject.functor j).map f) ((SmallObject.functor j).map g) := by
    let _ : PreservesLimit (cospan f g) π₁ :=
      (projectionPreserves (cospan f g)).1
    let _ : PreservesLimit (cospan f g) π₂ :=
      (projectionPreserves (cospan f g)).2
    have hLeft := h.map π₁
    have hRight := h.map π₂
    have hMappedLeft : IsPullback (functorMap j a) (functorMap j b)
        (functorMap j f) (functorMap j g) :=
      IsPullback.of_forall_isPullback_app (fun d => mappedPullback_left_at h hLeft hRight d)
    have w : (SmallObject.functor j).map a ≫ (SmallObject.functor j).map f =
        (SmallObject.functor j).map b ≫ (SmallObject.functor j).map g := by
      simpa only [Functor.map_comp] using (SmallObject.functor j).congr_map h.w
    let mappedCone := PullbackCone.mk ((SmallObject.functor j).map a)
      ((SmallObject.functor j).map b) w
    refine ⟨⟨w⟩, ⟨?_⟩⟩
    apply Comma.fstSndJointlyReflectLimit
    · exact (PullbackCone.isLimitMapConeEquiv mappedCone π₁).symm hMappedLeft.isLimit
    · exact (PullbackCone.isLimitMapConeEquiv mappedCone π₂).symm hRight.isLimit
  apply preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro X V Y f g _
  exact ⟨pullback f g, pullback.fst f g, pullback.snd f g,
    IsPullback.of_hasPullback f g, mappedPullback (IsPullback.of_hasPullback f g)⟩

end CategoryTheory.SmallObject
