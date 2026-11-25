/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentNormalForm
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Comma

/-! # Cardinal-filtered colimits of the original Arrow attachment

Both absolute endpoint-presentability conditions make each original generator
arrow presentable. The native whole-Arrow factorization and eventual equality
retain its original top and bottom maps. The labelled normal form compares the
actual mapped cocone at each site object, and native colimit reflection keeps
both original projections. This implements the presheaf calculation underlying
the Hirschhorn localization construction without a supplied preservation witness.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w s
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.SmallObject
variable {D : Type w} [SmallCategory D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)
    (μ : Cardinal.{max u w}) [Fact μ.IsRegular]

/-- The actual one-step Arrow attachment preserves μ-filtered colimits. -/
theorem presheafAttachment_isCardinalAccessible [∀ i, Mono (j i)]
    [∀ i, IsCardinalPresentable.{max u w} (A i) μ]
    [∀ i, IsCardinalPresentable.{max u w} (B i) μ] :
    (SmallObject.functor j).IsCardinalAccessible μ := by
  classical
  let π₁ : Arrow (Dᵒᵖ ⥤ Type (max u w)) ⥤ Dᵒᵖ ⥤ Type (max u w) := Arrow.leftFunc
  let π₂ : Arrow (Dᵒᵖ ⥤ Type (max u w)) ⥤ Dᵒᵖ ⥤ Type (max u w) := Arrow.rightFunc
  have arrowPresentable (i : I) :
      IsCardinalPresentable.{max u w} (Arrow.mk (j i)) μ := by
    exact Comma.isCardinalPresentable_mk
      (F₁ := 𝟭 (Dᵒᵖ ⥤ Type (max u w)))
      (F₂ := 𝟭 (Dᵒᵖ ⥤ Type (max u w))) (j i)
  let imageLabel {X Y : Arrow (Dᵒᵖ ⥤ Type (max u w))}
      (f : X ⟶ Y) (q : FunctorObjIndex j X.hom) : FunctorObjIndex j Y.hom :=
    ⟨q.i, q.t ≫ f.left, q.b ≫ f.right,
      by rw [Category.assoc, f.w, ← Category.assoc, q.w, Category.assoc]⟩
  refine { preservesColimitOfShape := fun J _ _ => ?_ }
  let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J μ
  let _ : PreservesColimitsOfShape J π₁ := inferInstance
  let _ : PreservesColimitsOfShape J π₂ := inferInstance
  refine { preservesColimit := fun {F} => ?_ }
  refine { preserves := fun {c} hc => ?_ }
  have mappedLeftAt (d : Dᵒᵖ) :
      IsColimit (((evaluation _ _).obj d).mapCocone
        (π₁.mapCocone ((SmallObject.functor j).mapCocone c))) := by
    let e : (Dᵒᵖ ⥤ Type (max u w)) ⥤ Type (max u w) := (evaluation _ _).obj d
    let c₀ := e.mapCocone (π₁.mapCocone c)
    have hc₀ : IsColimit c₀ := isColimitOfPreserves e (isColimitOfPreserves π₁ hc)
    let c₁ := e.mapCocone (π₁.mapCocone ((SmallObject.functor j).mapCocone c))
    apply Types.FilteredColimit.isColimitOf' _ c₁
    · intro x
      change (functorObj j c.pt.hom).obj d at x
      obtain ⟨r, rfl⟩ := (presheafAttachmentEquiv j c.pt.hom d).surjective x
      rcases r with x | ⟨q, z, hz⟩
      · obtain ⟨k, y, hy⟩ := Types.jointly_surjective_of_isColimit hc₀ x
        refine ⟨k, presheafAttachmentEquiv j (F.obj k).hom d (Sum.inl y), ?_⟩
        change presheafAttachmentEquiv j c.pt.hom d (Sum.inl x) =
          (functorMap j (c.ι.app k)).app d
            (presheafAttachmentEquiv j (F.obj k).hom d (Sum.inl y))
        erw [presheafAttachmentEquiv_naturality]
        exact congrArg (fun v => presheafAttachmentEquiv j c.pt.hom d (Sum.inl v)) hy.symm
      · rcases q with ⟨i, t, b, wq⟩
        let _ : IsCardinalPresentable.{max u w} (Arrow.mk (j i)) μ := arrowPresentable i
        let qArrow : Arrow.mk (j i) ⟶ c.pt := Arrow.homMk t b wq
        obtain ⟨k, α, hα⟩ := IsCardinalPresentable.exists_hom_of_isColimit μ hc qArrow
        let qk : FunctorObjIndex j (F.obj k).hom :=
          ⟨i, α.left, α.right, by simpa only [Arrow.mk_hom] using α.w⟩
        have htop : α.left ≫ (c.ι.app k).left = t := by
          have h := congrArg Arrow.Hom.left hα
          change α.left ≫ (c.ι.app k).left = t at h
          exact h
        have hbottom : α.right ≫ (c.ι.app k).right = b := by
          have h := congrArg Arrow.Hom.right hα
          change α.right ≫ (c.ι.app k).right = b at h
          exact h
        have mappedLabel : imageLabel (c.ι.app k) qk = ⟨i, t, b, wq⟩ := by
          simp only [imageLabel, qk, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and]
          exact ⟨htop, hbottom⟩
        refine ⟨k, presheafAttachmentEquiv j (F.obj k).hom d (Sum.inr ⟨qk, z, hz⟩), ?_⟩
        change presheafAttachmentEquiv j c.pt.hom d (Sum.inr ⟨⟨i, t, b, wq⟩, z, hz⟩) =
          (functorMap j (c.ι.app k)).app d
            (presheafAttachmentEquiv j (F.obj k).hom d (Sum.inr ⟨qk, z, hz⟩))
        erw [presheafAttachmentEquiv_naturality]
        apply congrArg (fun r => presheafAttachmentEquiv j c.pt.hom d (Sum.inr r))
        exact Sigma.ext mappedLabel.symm (HEq.rfl)
    · intro k x y hxy
      change (functorObj j (F.obj k).hom).obj d at x y
      change (functorMap j (c.ι.app k)).app d x =
        (functorMap j (c.ι.app k)).app d y at hxy
      obtain ⟨r, rfl⟩ := (presheafAttachmentEquiv j (F.obj k).hom d).surjective x
      obtain ⟨r', rfl⟩ := (presheafAttachmentEquiv j (F.obj k).hom d).surjective y
      erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality] at hxy
      have hnormal := (presheafAttachmentEquiv j c.pt.hom d).injective hxy
      rcases r with x | ⟨q, z, hz⟩
      · rcases r' with y | ⟨q', z', hz'⟩
        · obtain ⟨l, v, hv⟩ :=
            (Types.FilteredColimit.isColimit_eq_iff' hc₀ x y).1 (Sum.inl.inj hnormal)
          refine ⟨l, v, ?_⟩
          change (functorMap j (F.map v)).app d
              (presheafAttachmentEquiv j (F.obj k).hom d (Sum.inl x)) =
            (functorMap j (F.map v)).app d
              (presheafAttachmentEquiv j (F.obj k).hom d (Sum.inl y))
          erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality]
          exact congrArg (fun x => presheafAttachmentEquiv j (F.obj l).hom d (Sum.inl x)) hv
        · cases hnormal
      · rcases r' with y | ⟨q', z', hz'⟩
        · cases hnormal
        · rcases q with ⟨i, t, b, wq⟩
          rcases q' with ⟨i', t', b', wq'⟩
          have hlabel := congrArg Sigma.fst (Sum.inr.inj hnormal)
          have hi : i = i' := congrArg FunctorObjIndex.i hlabel
          cases hi
          let pointLabel : (Σ q : FunctorObjIndex j c.pt.hom,
              {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) →
              Σ i, {z : (B i).obj d // z ∉ Set.range ((j i).app d)} :=
            fun q => ⟨q.1.i, q.2⟩
          have hzEq : (⟨z, hz⟩ : {z : (B i).obj d // z ∉ Set.range ((j i).app d)}) = ⟨z', hz'⟩ := by
            have h := congrArg pointLabel (Sum.inr.inj hnormal)
            simpa only [pointLabel, imageLabel, Sigma.mk.injEq, heq_eq_eq, true_and] using h
          cases hzEq
          have components : t ≫ (c.ι.app k).left = t' ≫ (c.ι.app k).left ∧
              b ≫ (c.ι.app k).right = b' ≫ (c.ι.app k).right := by
            simpa only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and] using hlabel
          let qArrow : Arrow.mk (j i) ⟶ F.obj k := Arrow.homMk t b wq
          let qArrow' : Arrow.mk (j i) ⟶ F.obj k := Arrow.homMk t' b' wq'
          have wholeEquality : qArrow ≫ c.ι.app k = qArrow' ≫ c.ι.app k := by
            apply Arrow.hom_ext
            · exact components.1
            · exact components.2
          let _ : IsCardinalPresentable.{max u w} (Arrow.mk (j i)) μ := arrowPresentable i
          obtain ⟨l, v, hv⟩ := IsCardinalPresentable.exists_eq_of_isColimit' μ hc
            qArrow qArrow' wholeEquality
          have topEquality : t ≫ (F.map v).left = t' ≫ (F.map v).left := by
            have h := congrArg Arrow.Hom.left hv
            change t ≫ (F.map v).left = t' ≫ (F.map v).left at h
            exact h
          have bottomEquality : b ≫ (F.map v).right = b' ≫ (F.map v).right := by
            have h := congrArg Arrow.Hom.right hv
            change b ≫ (F.map v).right = b' ≫ (F.map v).right at h
            exact h
          have stageLabel : imageLabel (F.map v) ⟨i, t, b, wq⟩ =
              imageLabel (F.map v) ⟨i, t', b', wq'⟩ := by
            simp only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and]
            exact ⟨topEquality, bottomEquality⟩
          refine ⟨l, v, ?_⟩
          change (functorMap j (F.map v)).app d
              (presheafAttachmentEquiv j (F.obj k).hom d (Sum.inr ⟨⟨i, t, b, wq⟩, z, hz⟩)) =
            (functorMap j (F.map v)).app d
              (presheafAttachmentEquiv j (F.obj k).hom d (Sum.inr ⟨⟨i, t', b', wq'⟩, z, hz'⟩))
          erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality]
          apply congrArg (fun r => presheafAttachmentEquiv j (F.obj l).hom d (Sum.inr r))
          exact Sigma.ext stageLabel (HEq.rfl)
  have mappedLeft : IsColimit (π₁.mapCocone ((SmallObject.functor j).mapCocone c)) :=
    evaluationJointlyReflectsColimits _ mappedLeftAt
  have mappedRight : IsColimit (π₂.mapCocone ((SmallObject.functor j).mapCocone c)) := by
    change IsColimit (π₂.mapCocone c)
    exact isColimitOfPreserves π₂ hc
  exact ⟨Comma.fstSndJointlyReflectColimit mappedLeft mappedRight⟩
end CategoryTheory.SmallObject
