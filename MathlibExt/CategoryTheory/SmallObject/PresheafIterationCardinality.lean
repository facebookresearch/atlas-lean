/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentCardinality
public import MathlibExt.CategoryTheory.SmallObject.ConstructionComparison
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Cardinality bounds for terminal small-object factorizations

For a category equivalent to presheaves, the chosen small-object
factorization of a terminal map retains a fixed bound on the total
points of its left object. The hypotheses bound the generating sources
and targets, the starting object and the regular iteration cardinal.
Successor attachments use the terminal attachment bound; limit stages
use joint coverage of the mapped colimit.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w v uC vC l vJ
open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace CategoryTheory.SmallObject

private theorem elements_cardinal_eq_of_iso
    {D : Type w} [Category.{v} D]
    {X Y : Dᵒᵖ ⥤ Type (max u w)} (e : X ≅ Y) :
    Cardinal.mk X.Elements = Cardinal.mk Y.Elements := by
  let E : X.Elements ≃ Y.Elements :=
    { toFun := e.hom.mapElements.obj
      invFun := e.inv.mapElements.obj
      left_inv q := by
        apply Functor.Elements.ext
          (e.inv.mapElements.obj (e.hom.mapElements.obj q)) q rfl
        simpa only [NatTrans.mapElements, eqToHom_refl, Functor.map_id,
          types_id_apply, types_comp_apply] using
          ConcreteCategory.congr_hom (e.hom_inv_id_app q.obj) q.val
      right_inv q := by
        apply Functor.Elements.ext
          (e.hom.mapElements.obj (e.inv.mapElements.obj q)) q rfl
        simpa only [NatTrans.mapElements, eqToHom_refl, Functor.map_id,
          types_id_apply, types_comp_apply] using
          ConcreteCategory.congr_hom (e.inv_hom_id_app q.obj) q.val }
  exact E.cardinal_eq

private theorem elements_bound_of_isColimit
    {D : Type w} [Category.{v} D]
    {J : Type l} [Category.{vJ} J] [Small.{max u w} J]
    (H : J ⥤ Dᵒᵖ ⥤ Type (max u w)) (c : Cocone H) (hc : IsColimit c)
    (γ : Cardinal.{max u w}) (hγ : ℵ₀ ≤ γ)
    (hJ : Cardinal.mk (Shrink.{max u w} J) ≤ γ)
    (hH : ∀ j, Cardinal.mk (H.obj j).Elements ≤ γ) :
    Cardinal.mk c.pt.Elements ≤ γ := by
  classical
  let cover : (Σ j : J, (H.obj j).Elements) → c.pt.Elements := fun z =>
    Functor.elementsMk _ z.2.obj ((c.ι.app z.1).app z.2.obj z.2.val)
  have hcover : Function.Surjective cover := by
    intro q
    let E := (evaluation Dᵒᵖ (Type (max u w))).obj q.obj
    have he := isColimitOfPreserves E hc
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit he q.val
    refine ⟨⟨j, Functor.elementsMk (H.obj j) q.obj y⟩, ?_⟩
    apply Functor.Elements.ext
      (cover ⟨j, Functor.elementsMk (H.obj j) q.obj y⟩) q rfl
    simpa only [cover, E, Functor.mapCocone_pt, Functor.mapCocone_ι_app,
      Functor.const_obj_obj, evaluation_obj_obj, evaluation_obj_map,
      eqToHom_refl, Functor.map_id, types_id_apply] using hy
  let e := equivShrink.{max u w} J
  let S : Type (max u w) := Σ j : Shrink.{max u w} J, (H.obj (e.symm j)).Elements
  let r : (Σ j : J, (H.obj j).Elements) ≃ S :=
    Equiv.sigmaCongrLeft' e
  have hs : Function.Surjective (cover ∘ r.symm) := hcover.comp r.symm.surjective
  have hsum : Cardinal.mk S ≤ γ := by
    dsimp [S]
    rw [Cardinal.mk_sigma]
    calc
      _ ≤ Cardinal.sum (fun _ : Shrink.{max u w} J => γ) :=
        Cardinal.sum_le_sum _ _ (fun j => hH (e.symm j))
      _ = Cardinal.mk (Shrink.{max u w} J) * γ := Cardinal.sum_const' _ _
      _ ≤ γ := Cardinal.mul_le_of_le hγ hJ le_rfl
  exact (Cardinal.mk_le_of_surjective hs).trans hsum

private theorem original_terminal_step_bound
    {D : Type w} [Category.{v} D]
    {C : Type uC} [Category.{vC} C] [HasTerminal C]
    (I : MorphismProperty C)
    (F : C ⥤ Dᵒᵖ ⥤ Type (max u w)) [F.IsEquivalence]
    [LocallySmall.{max u w} C] [Small.{max u w} I.toSet]
    [HasPushouts C]
    [∀ {X S : C} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (FunctorObjIndex I.homFamily p)) C]
    (q : Arrow C) (eq : q.right ≅ ⊤_ C)
    (ξ : Cardinal.{max u w}) (hξ : ℵ₀ ≤ ξ)
    (hI : Cardinal.mk (Shrink.{max u w} I.toSet) ≤ ξ)
    (hA : ∀ i : I.toSet, Cardinal.mk (F.obj i.1.left).Elements ≤ ξ)
    (hB : ∀ i : I.toSet, Cardinal.mk (F.obj i.1.right).Elements ≤ ξ)
    (hq : Cardinal.mk (F.obj q.left).Elements ≤ 2 ^ ξ) :
    Cardinal.mk (F.obj (functorObj I.homFamily q.hom)).Elements ≤ 2 ^ ξ := by
  let jF := fun i : I.toSet => F.map (I.homFamily i)
  let nC : q ≅ Arrow.mk (terminal.from q.left) :=
    Arrow.isoMk (Iso.refl _) eq (terminalIsTerminal.hom_ext _ _)
  let c₁ := F.mapIso (Arrow.leftFunc.mapIso ((SmallObject.functor I.homFamily).mapIso nC))
  let c₂ := Arrow.leftFunc.mapIso
    ((functorMapIso I.homFamily F).app (Arrow.mk (terminal.from q.left)))
  let nD : Arrow.mk (F.map (terminal.from q.left)) ≅
      Arrow.mk (terminal.from (F.obj q.left)) :=
    Arrow.isoMk' _ _ (Iso.refl _) (PreservesTerminal.iso F)
      (terminalIsTerminal.hom_ext _ _)
  let c₃ := Arrow.leftFunc.mapIso ((SmallObject.functor jF).mapIso nD)
  let e : F.obj (functorObj I.homFamily q.hom) ≅
      functorObj jF (terminal.from (F.obj q.left)) := c₁ ≪≫ c₂ ≪≫ c₃
  rw [elements_cardinal_eq_of_iso e]
  exact presheafAttachment_terminal_mk_elements_le jF (F.obj q.left) ξ hξ hI hA hB hq

section OriginalFamily

variable {D : Type w} [Category.{v} D]
    {C : Type uC} [Category.{vC} C] [HasTerminal C]
    (I : MorphismProperty C) (κ : Cardinal.{max u w})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [I.IsCardinalForSmallObjectArgument κ]
    (F : C ⥤ Dᵒᵖ ⥤ Type (max u w)) [F.IsEquivalence]

/-- The original eligible small-object factorization has the fixed total-point bound.
Every stage, prefix and final cocone is the native one at this same κ and I. -/
theorem obj_terminal_mk_elements_le_of_presheaf_equivalence
    (ξ : Cardinal.{max u w}) (hξ : ℵ₀ ≤ ξ) (hκ : κ ≤ ξ)
    (hI :
      letI : MorphismProperty.IsSmall.{max u w} I := SmallObject.isSmall I κ
      Cardinal.mk (Shrink.{max u w} I.toSet) ≤ ξ)
    (hA : ∀ i : I.toSet, Cardinal.mk (F.obj i.1.left).Elements ≤ ξ)
    (hB : ∀ i : I.toSet, Cardinal.mk (F.obj i.1.right).Elements ≤ ξ)
    (X : C) (hX : Cardinal.mk (F.obj X).Elements ≤ 2 ^ ξ) :
    Cardinal.mk (F.obj (SmallObject.obj I κ (terminal.from X))).Elements ≤ 2 ^ ξ := by
  let _ : LocallySmall.{max u w} C := SmallObject.locallySmall I κ
  let _ : MorphismProperty.IsSmall.{max u w} I := SmallObject.isSmall I κ
  let _ : HasPushouts C := SmallObject.hasPushouts I κ
  let _ (A B : C) (p : A ⟶ B) :
      HasColimitsOfShape (Discrete (FunctorObjIndex I.homFamily p)) C :=
    SmallObject.hasColimitsOfShape_discrete I κ A B p
  let _ : HasIterationOfShape κ.ord.ToType C := SmallObject.hasIterationOfShape I κ
  let f := terminal.from X
  let L := SmallObject.relativeCellComplexιObj I κ f
  let _ : L.F.IsWellOrderContinuous := L.isWellOrderContinuous
  let γ : Cardinal.{max u w} := 2 ^ ξ
  have hγ : ℵ₀ ≤ γ := hξ.trans (Cardinal.cantor ξ).le
  have hκγ : κ ≤ γ := hκ.trans (Cardinal.cantor ξ).le
  have hstage : ∀ j : κ.ord.ToType, Cardinal.mk (F.obj (L.F.obj j)).Elements ≤ γ := by
    intro j
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
        have hjbot : j = ⊥ := isMin_iff_eq_bot.mp hj
        subst j
        rw [elements_cardinal_eq_of_iso (F.mapIso L.isoBot)]
        exact hX
    | succ j hj ih =>
        let q := ((SmallObject.iterationFunctor I κ).obj j).obj (Arrow.mk f)
        let e := SmallObject.relativeCellComplexιObjFObjSuccIso I κ f j
        rw [elements_cardinal_eq_of_iso (F.mapIso e)]
        change Cardinal.mk (F.obj (functorObj I.homFamily q.hom)).Elements ≤ γ
        have hq : Cardinal.mk (F.obj q.left).Elements ≤ 2 ^ ξ := by
          change Cardinal.mk (F.obj (L.F.obj j)).Elements ≤ γ
          exact ih
        exact original_terminal_step_bound I F q
          (SmallObject.iterationFunctorObjObjRightIso I κ (Arrow.mk f) j)
          ξ hξ hI hA hB hq
    | isSuccLimit j hj ih =>
        let H : Set.Iio j ⥤ C := (Set.principalSegIio j).monotone.functor ⋙ L.F
        let c : Cocone H := (Set.principalSegIio j).cocone L.F
        let _ : HasColimitsOfShape (Set.Iio j) C :=
          hasColimitsOfShape_of_isSuccLimit C j hj
        have hc : IsColimit c := L.F.isColimitOfIsWellOrderContinuous j hj
        have hindex : Cardinal.mk (Shrink.{max u w} (Set.Iio j)) ≤ γ := by
          rw [← Cardinal.mk_congr (equivShrink.{max u w} (Set.Iio j))]
          exact (Cardinal.mk_subtype_le (fun k : κ.ord.ToType => k < j)).trans
            (by simpa only [Cardinal.mk_ord_toType] using hκγ)
        exact elements_bound_of_isColimit (H ⋙ F) (F.mapCocone c)
          (isColimitOfPreserves F hc) γ hγ hindex (fun k => ih k.1 k.2)
  have hindex : Cardinal.mk (Shrink.{max u w} κ.ord.ToType) ≤ γ := by
    rw [← Cardinal.mk_congr (equivShrink.{max u w} κ.ord.ToType)]
    simpa only [Cardinal.mk_ord_toType] using hκγ
  exact elements_bound_of_isColimit (L.F ⋙ F)
    (F.mapCocone (Cocone.mk (SmallObject.obj I κ f) L.incl))
    (isColimitOfPreserves F L.isColimit) γ hγ hindex hstage

end OriginalFamily
end CategoryTheory.SmallObject
