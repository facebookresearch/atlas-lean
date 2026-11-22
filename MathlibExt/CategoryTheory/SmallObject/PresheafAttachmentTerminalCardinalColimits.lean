/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentNormalForm
public import MathlibExt.CategoryTheory.NatTrans.TerminalArrow
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Domain-presentable terminal-arrow attachment colimits

The existing pointwise Arrow functor of the original terminal transformation
keeps each map's left component and identity right component. Its filtered
colimits follow from the identity and constant-terminal projections. Domain
presentability then factors and equalizes original top maps while the original
bottom maps remain the chosen terminal maps. The labelled normal form retains
each whole square and complementary point in the actual mapped cocone.

This is the terminal specialization of the direct presheaf calculation used
in the Hirschhorn localization/cardinality route.
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

/-- Domain presentability controls the actual terminal-arrow attachment. -/
theorem presheafAttachment_terminal_isCardinalAccessible [∀ i, Mono (j i)]
    [∀ i, IsCardinalPresentable.{max u w} (A i) μ] :
    ((terminal.arrowFunctor (Dᵒᵖ ⥤ Type (max u w)) ⋙
      SmallObject.functor j) ⋙ Arrow.leftFunc).IsCardinalAccessible μ := by
  classical
  let T := terminal.arrowFunctor (Dᵒᵖ ⥤ Type (max u w))
  let K := (T ⋙ SmallObject.functor j) ⋙ Arrow.leftFunc
  have embeddingAccessible : T.IsCardinalAccessible μ := by
    refine { preservesColimitOfShape := fun J _ _ => ?_ }
    let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J μ
    let R := (Functor.const (Dᵒᵖ ⥤ Type (max u w))).obj (⊤_ (Dᵒᵖ ⥤ Type (max u w)))
    let _ : R.IsCardinalAccessible μ := inferInstance
    let _ : PreservesColimitsOfShape J R :=
      Functor.preservesColimitsOfShape_of_isCardinalAccessible R μ J
    refine { preservesColimit := fun {F} => { preserves := fun {c} hc => ?_ } }
    have hleft : IsColimit (Arrow.leftFunc.mapCocone (T.mapCocone c)) := by
      change IsColimit c
      exact hc
    have hright : IsColimit (Arrow.rightFunc.mapCocone (T.mapCocone c)) := by
      change IsColimit (R.mapCocone c)
      exact isColimitOfPreserves R hc
    exact ⟨Comma.fstSndJointlyReflectColimit hleft hright⟩
  let imageLabel {X Y : Dᵒᵖ ⥤ Type (max u w)} (f : X ⟶ Y)
      (q : FunctorObjIndex j (terminal.from X)) : FunctorObjIndex j (terminal.from Y) :=
    ⟨q.i, q.t ≫ f, terminal.from (B q.i), terminalIsTerminal.hom_ext _ _⟩
  have native_imageLabel {X Y : Dᵒᵖ ⥤ Type (max u w)} (f : X ⟶ Y)
      (q : FunctorObjIndex j (terminal.from X)) :
      FunctorObjIndex.mk q.i (q.t ≫ (T.map f).left) (q.b ≫ (T.map f).right)
        (terminalIsTerminal.hom_ext _ _) = imageLabel f q := by
    rcases q with ⟨i, top, bottom, square⟩
    have hb : bottom = terminal.from (B i) := terminalIsTerminal.hom_ext _ _
    change FunctorObjIndex.mk i (top ≫ f) (bottom ≫ 𝟙 _) _ = imageLabel f ⟨i, top, bottom, square⟩
    simp only [Category.comp_id, imageLabel, hb]
  refine { preservesColimitOfShape := fun J _ _ => ?_ }
  let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J μ
  refine { preservesColimit := fun {F} => { preserves := fun {c} hc => ?_ } }
  let _ : T.IsCardinalAccessible μ := embeddingAccessible
  let _ : PreservesColimitsOfShape J T :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible T μ J
  have hT : IsColimit (T.mapCocone c) := isColimitOfPreserves T hc
  have hLeft : IsColimit (Arrow.leftFunc.mapCocone (T.mapCocone c)) :=
    isColimitOfPreserves Arrow.leftFunc hT
  have mappedAt (d : Dᵒᵖ) : IsColimit (((evaluation _ _).obj d).mapCocone (K.mapCocone c)) := by
    let e : (Dᵒᵖ ⥤ Type (max u w)) ⥤ Type (max u w) := (evaluation _ _).obj d
    have hOriginal : IsColimit (e.mapCocone c) := by
      change IsColimit (e.mapCocone (Arrow.leftFunc.mapCocone (T.mapCocone c)))
      exact isColimitOfPreserves e hLeft
    let mapped := e.mapCocone (K.mapCocone c)
    apply Types.FilteredColimit.isColimitOf' _ mapped
    · intro x
      change (functorObj j (terminal.from c.pt)).obj d at x
      obtain ⟨r, rfl⟩ := (presheafAttachmentEquiv j (terminal.from c.pt) d).surjective x
      rcases r with x | ⟨q, z, hz⟩
      · obtain ⟨k, y, hy⟩ := Types.jointly_surjective_of_isColimit hOriginal x
        refine ⟨k, presheafAttachmentEquiv j (terminal.from (F.obj k)) d (Sum.inl y), ?_⟩
        change presheafAttachmentEquiv j (terminal.from c.pt) d (Sum.inl x) =
          (functorMap j (T.map (c.ι.app k))).app d
            (presheafAttachmentEquiv j (terminal.from (F.obj k)) d (Sum.inl y))
        erw [presheafAttachmentEquiv_naturality]
        exact congrArg (fun x => presheafAttachmentEquiv j (terminal.from c.pt) d (Sum.inl x))
            hy.symm
      · rcases q with ⟨i, top, bottom, square⟩
        obtain ⟨k, α, hα⟩ := IsCardinalPresentable.exists_hom_of_isColimit μ hLeft top
        change α ≫ c.ι.app k = top at hα
        let qk : FunctorObjIndex j (terminal.from (F.obj k)) :=
          ⟨i, α, terminal.from (B i), terminalIsTerminal.hom_ext _ _⟩
        have labelEq : imageLabel (c.ι.app k) qk = ⟨i, top, bottom, square⟩ := by
          simp only [imageLabel, qk, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and]
          exact ⟨hα, terminalIsTerminal.hom_ext _ _⟩
        refine ⟨k, presheafAttachmentEquiv j (terminal.from (F.obj k)) d (Sum.inr ⟨qk, z, hz⟩), ?_⟩
        change presheafAttachmentEquiv j (terminal.from c.pt) d
            (Sum.inr ⟨⟨i, top, bottom, square⟩, z, hz⟩) =
          (functorMap j (T.map (c.ι.app k))).app d
            (presheafAttachmentEquiv j (terminal.from (F.obj k)) d (Sum.inr ⟨qk, z, hz⟩))
        erw [presheafAttachmentEquiv_naturality]
        apply congrArg (fun x => presheafAttachmentEquiv j (terminal.from c.pt) d (Sum.inr x))
        apply Sigma.ext
        · exact ((native_imageLabel (c.ι.app k) qk).trans labelEq).symm
        · exact HEq.rfl
    · intro k x y hxy
      change (functorObj j (terminal.from (F.obj k))).obj d at x y
      change (functorMap j (T.map (c.ι.app k))).app d x =
        (functorMap j (T.map (c.ι.app k))).app d y at hxy
      obtain ⟨r, rfl⟩ := (presheafAttachmentEquiv j (terminal.from (F.obj k)) d).surjective x
      obtain ⟨r', rfl⟩ := (presheafAttachmentEquiv j (terminal.from (F.obj k)) d).surjective y
      erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality] at hxy
      have hn := (presheafAttachmentEquiv j (terminal.from c.pt) d).injective hxy
      rcases r with x | ⟨q, z, hz⟩
      · rcases r' with y | ⟨q', z', hz'⟩
        · obtain ⟨l, v, hv⟩ :=
            (Types.FilteredColimit.isColimit_eq_iff' hOriginal x y).1 (Sum.inl.inj hn)
          refine ⟨l, v, ?_⟩
          change (functorMap j (T.map (F.map v))).app d
              (presheafAttachmentEquiv j (terminal.from (F.obj k)) d (Sum.inl x)) =
            (functorMap j (T.map (F.map v))).app d
              (presheafAttachmentEquiv j (terminal.from (F.obj k)) d (Sum.inl y))
          erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality]
          exact congrArg
              (fun x => presheafAttachmentEquiv j (terminal.from (F.obj l)) d (Sum.inl x)) hv
        · cases hn
      · rcases r' with y | ⟨q', z', hz'⟩
        · cases hn
        · rcases q with ⟨i, top, bottom, square⟩
          rcases q' with ⟨i', top', bottom', square'⟩
          have hlabel := congrArg Sigma.fst (Sum.inr.inj hn)
          have hi : i = i' := congrArg FunctorObjIndex.i hlabel
          cases hi
          let pointLabel : (Σ q : FunctorObjIndex j (terminal.from c.pt),
              {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) →
              Σ i, {z : (B i).obj d // z ∉ Set.range ((j i).app d)} := fun q => ⟨q.1.i, q.2⟩
          have hzEq : (⟨z, hz⟩ : {z : (B i).obj d // z ∉ Set.range ((j i).app d)}) = ⟨z', hz'⟩ := by
            have h := congrArg pointLabel (Sum.inr.inj hn)
            simpa only [pointLabel, T, terminal.arrowFunctor_map_left,
                terminal.arrowFunctor_map_right,
              Functor.id_map, Functor.const_obj_map, Category.comp_id,
              Sigma.mk.injEq, heq_eq_eq, true_and] using h
          cases hzEq
          have ht : top ≫ c.ι.app k = top' ≫ c.ι.app k := by
            have h := hlabel
            change FunctorObjIndex.mk i (top ≫ (T.map (c.ι.app k)).left)
                (bottom ≫ (T.map (c.ι.app k)).right) _ =
              FunctorObjIndex.mk i (top' ≫ (T.map (c.ι.app k)).left)
                (bottom' ≫ (T.map (c.ι.app k)).right) _ at h
            change FunctorObjIndex.mk i (top ≫ c.ι.app k) (bottom ≫ 𝟙 _) _ =
              FunctorObjIndex.mk i (top' ≫ c.ι.app k) (bottom' ≫ 𝟙 _) _ at h
            simp only [Category.comp_id, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and] at h
            exact h.1
          obtain ⟨l, v, hv⟩ := IsCardinalPresentable.exists_eq_of_isColimit' μ hLeft top top' ht
          change top ≫ F.map v = top' ≫ F.map v at hv
          have labelEq : imageLabel (F.map v) ⟨i, top, bottom, square⟩ =
              imageLabel (F.map v) ⟨i, top', bottom', square'⟩ := by
            simpa only [imageLabel, FunctorObjIndex.mk.injEq, heq_eq_eq, true_and, and_true]
                using hv
          refine ⟨l, v, ?_⟩
          change (functorMap j (T.map (F.map v))).app d
              (presheafAttachmentEquiv j (terminal.from (F.obj k)) d
                  (Sum.inr ⟨⟨i, top, bottom, square⟩, z, hz⟩)) =
            (functorMap j (T.map (F.map v))).app d
              (presheafAttachmentEquiv j (terminal.from (F.obj k)) d
                  (Sum.inr ⟨⟨i, top', bottom', square'⟩, z, hz'⟩))
          erw [presheafAttachmentEquiv_naturality, presheafAttachmentEquiv_naturality]
          apply congrArg
              (fun x => presheafAttachmentEquiv j (terminal.from (F.obj l)) d (Sum.inr x))
          exact Sigma.ext
            ((native_imageLabel (F.map v) ⟨i, top, bottom, square⟩).trans
              (labelEq.trans (native_imageLabel (F.map v) ⟨i, top', bottom', square'⟩).symm))
            (HEq.rfl)
  exact ⟨evaluationJointlyReflectsColimits _ mappedAt⟩
end CategoryTheory.SmallObject
