/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Colimits

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SSet.BinaryCoproductPullback

/-- Pulling a binary cofan over one original base gives the actual binary coproduct of pullbacks. -/
def binaryPullbackIso {X₁ X₂ Y T : SSet.{u}}
    (p₁ : X₁ ⟶ Y) (p₂ : X₂ ⟶ Y) (t : T ⟶ Y) :
    pullback p₁ t ⨿ pullback p₂ t ≅ pullback (coprod.desc p₁ p₂) t := by
  let p := coprod.desc p₁ p₂
  let c : BinaryCofan X₁ X₂ := BinaryCofan.mk coprod.inl coprod.inr
  let g₁ : pullback p₁ t ⟶ pullback p t :=
    pullback.map p₁ t p t coprod.inl (𝟙 T) (𝟙 Y) (by simp [p]) (by simp)
  let g₂ : pullback p₂ t ⟶ pullback p t :=
    pullback.map p₂ t p t coprod.inr (𝟙 T) (𝟙 Y) (by simp [p]) (by simp)
  let d : BinaryCofan (pullback p₁ t) (pullback p₂ t) := BinaryCofan.mk g₁ g₂
  have h₁ : IsPullback g₁ (pullback.fst p₁ t) (pullback.fst p t) coprod.inl := by
    apply IsPullback.of_right _ (by simp [g₁, pullback.map])
      (IsPullback.of_hasPullback p t).flip
    simpa [p, g₁, pullback.map] using (IsPullback.of_hasPullback p₁ t).flip
  have h₂ : IsPullback g₂ (pullback.fst p₂ t) (pullback.fst p t) coprod.inr := by
    apply IsPullback.of_right _ (by simp [g₂, pullback.map])
      (IsPullback.of_hasPullback p t).flip
    simpa [p, g₂, pullback.map] using (IsPullback.of_hasPullback p₂ t).flip
  have hd : IsColimit d :=
    (((BinaryCofan.isVanKampen_iff c).1
      (FinitaryExtensive.vanKampen c (coprodIsCoprod X₁ X₂))) d
      (pullback.fst p₁ t) (pullback.fst p₂ t) (pullback.fst p t)
      (by simp [c, d, g₁, pullback.map])
      (by simp [c, d, g₂, pullback.map])).2 ⟨h₁, h₂⟩ |>.some
  exact (coprodIsCoprod (pullback p₁ t) (pullback p₂ t)).coconePointUniqueUpToIso hd

/-- The four original cofan projection equations of the actual distribution isomorphism. -/
theorem binaryPullbackIso_hom_legs {X₁ X₂ Y T : SSet.{u}}
    (p₁ : X₁ ⟶ Y) (p₂ : X₂ ⟶ Y) (t : T ⟶ Y) :
    (coprod.inl : pullback p₁ t ⟶ pullback p₁ t ⨿ pullback p₂ t) ≫
        (binaryPullbackIso p₁ p₂ t).hom ≫ pullback.fst (coprod.desc p₁ p₂) t =
      pullback.fst p₁ t ≫ coprod.inl ∧
    (coprod.inl : pullback p₁ t ⟶ pullback p₁ t ⨿ pullback p₂ t) ≫
        (binaryPullbackIso p₁ p₂ t).hom ≫ pullback.snd (coprod.desc p₁ p₂) t =
      pullback.snd p₁ t ∧
    (coprod.inr : pullback p₂ t ⟶ pullback p₁ t ⨿ pullback p₂ t) ≫
        (binaryPullbackIso p₁ p₂ t).hom ≫ pullback.fst (coprod.desc p₁ p₂) t =
      pullback.fst p₂ t ≫ coprod.inr ∧
    (coprod.inr : pullback p₂ t ⟶ pullback p₁ t ⨿ pullback p₂ t) ≫
        (binaryPullbackIso p₁ p₂ t).hom ≫ pullback.snd (coprod.desc p₁ p₂) t =
      pullback.snd p₂ t := by
  have h₁ : (coprod.inl : pullback p₁ t ⟶ pullback p₁ t ⨿ pullback p₂ t) ≫
      (binaryPullbackIso p₁ p₂ t).hom =
      pullback.map p₁ t (coprod.desc p₁ p₂) t coprod.inl (𝟙 T) (𝟙 Y)
        (by simp) (by simp) := by
    unfold binaryPullbackIso
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod (pullback p₁ t) (pullback p₂ t)) _ ⟨WalkingPair.left⟩
  have h₂ : (coprod.inr : pullback p₂ t ⟶ pullback p₁ t ⨿ pullback p₂ t) ≫
      (binaryPullbackIso p₁ p₂ t).hom =
      pullback.map p₂ t (coprod.desc p₁ p₂) t coprod.inr (𝟙 T) (𝟙 Y)
        (by simp) (by simp) := by
    unfold binaryPullbackIso
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod (pullback p₁ t) (pullback p₂ t)) _ ⟨WalkingPair.right⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, h₁]; simp
  · rw [← Category.assoc, h₁]; simp
  · rw [← Category.assoc, h₂]; simp
  · rw [← Category.assoc, h₂]; simp

/-- The inverse retains both aggregate cofan projections, without inventing projections onto
summands. -/
theorem binaryPullbackIso_inv_legs {X₁ X₂ Y T : SSet.{u}}
    (p₁ : X₁ ⟶ Y) (p₂ : X₂ ⟶ Y) (t : T ⟶ Y) :
    (binaryPullbackIso p₁ p₂ t).inv ≫
        coprod.desc (pullback.fst p₁ t ≫ coprod.inl) (pullback.fst p₂ t ≫ coprod.inr) =
      pullback.fst (coprod.desc p₁ p₂) t ∧
    (binaryPullbackIso p₁ p₂ t).inv ≫
        coprod.desc (pullback.snd p₁ t) (pullback.snd p₂ t) =
      pullback.snd (coprod.desc p₁ p₂) t := by
  have h := binaryPullbackIso_hom_legs p₁ p₂ t
  constructor
  · apply (cancel_epi (binaryPullbackIso p₁ p₂ t).hom).mp
    apply coprod.hom_ext <;> simp [h.1, h.2.2.1]
  · apply (cancel_epi (binaryPullbackIso p₁ p₂ t).hom).mp
    apply coprod.hom_ext <;> simp [h.2.1, h.2.2.2]

/-- Both ordinary operator conjugacies hold for the same arbitrary w and original target map. -/
theorem binaryPullbackIso_operator {X₁ X₂ Y U V : SSet.{u}}
    (p₁ : X₁ ⟶ Y) (p₂ : X₂ ⟶ Y) (w : U ⟶ V) (v : V ⟶ Y) :
    let c₁ := pullback.map p₁ (w ≫ v) p₁ v (𝟙 X₁) w (𝟙 Y) (by simp) (by simp)
    let c₂ := pullback.map p₂ (w ≫ v) p₂ v (𝟙 X₂) w (𝟙 Y) (by simp) (by simp)
    let c := pullback.map (coprod.desc p₁ p₂) (w ≫ v) (coprod.desc p₁ p₂) v
      (𝟙 (X₁ ⨿ X₂)) w (𝟙 Y) (by simp) (by simp)
    coprod.map c₁ c₂ ≫ (binaryPullbackIso p₁ p₂ v).hom =
      (binaryPullbackIso p₁ p₂ (w ≫ v)).hom ≫ c ∧
    (binaryPullbackIso p₁ p₂ (w ≫ v)).inv ≫ coprod.map c₁ c₂ =
      c ≫ (binaryPullbackIso p₁ p₂ v).inv := by
  dsimp only
  have h : coprod.map
      (pullback.map p₁ (w ≫ v) p₁ v (𝟙 X₁) w (𝟙 Y) (by simp) (by simp))
      (pullback.map p₂ (w ≫ v) p₂ v (𝟙 X₂) w (𝟙 Y) (by simp) (by simp)) ≫
        (binaryPullbackIso p₁ p₂ v).hom =
      (binaryPullbackIso p₁ p₂ (w ≫ v)).hom ≫
        pullback.map (coprod.desc p₁ p₂) (w ≫ v) (coprod.desc p₁ p₂) v
          (𝟙 (X₁ ⨿ X₂)) w (𝟙 Y) (by simp) (by simp) := by
    have hU := binaryPullbackIso_hom_legs p₁ p₂ (w ≫ v)
    have hV := binaryPullbackIso_hom_legs p₁ p₂ v
    apply coprod.hom_ext
    · apply pullback.hom_ext
      · simp [Category.assoc, hV.1, hU.1]
      · simp [Category.assoc, hV.2.1]
        simpa only [Category.assoc] using (congrArg (fun k => k ≫ w) hU.2.1).symm
    · apply pullback.hom_ext
      · simp [Category.assoc, hV.2.2.1, hU.2.2.1]
      · simp [Category.assoc, hV.2.2.2]
        simpa only [Category.assoc] using (congrArg (fun k => k ≫ w) hU.2.2.2).symm
  refine ⟨h, ?_⟩
  apply (cancel_epi (binaryPullbackIso p₁ p₂ (w ≫ v)).hom).mp
  apply (cancel_mono (binaryPullbackIso p₁ p₂ v).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The actual whole Arrow comparison is the binary coproduct of both component comparisons. -/
def binaryComparisonArrowIso {X₁ X₂ Y U V : SSet.{u}}
    (p₁ : X₁ ⟶ Y) (p₂ : X₂ ⟶ Y) (w : U ⟶ V) (v : V ⟶ Y) :
    Arrow.mk (coprod.map
      (pullback.map p₁ (w ≫ v) p₁ v (𝟙 X₁) w (𝟙 Y) (by simp) (by simp))
      (pullback.map p₂ (w ≫ v) p₂ v (𝟙 X₂) w (𝟙 Y) (by simp) (by simp))) ≅
    Arrow.mk (pullback.map (coprod.desc p₁ p₂) (w ≫ v) (coprod.desc p₁ p₂) v
      (𝟙 (X₁ ⨿ X₂)) w (𝟙 Y) (by simp) (by simp)) :=
  Arrow.isoMk (binaryPullbackIso p₁ p₂ (w ≫ v)) (binaryPullbackIso p₁ p₂ v)
    (binaryPullbackIso_operator p₁ p₂ w v).1.symm

/-- Both actual binary summand squares of a coproduct map are pullbacks. -/
theorem binaryCoproductSquares {X₁ X₂ Y₁ Y₂ : SSet.{u}}
    (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂) :
    IsPullback coprod.inl p₁ (coprod.map p₁ p₂) coprod.inl ∧
    IsPullback coprod.inr p₂ (coprod.map p₁ p₂) coprod.inr :=
  (((BinaryCofan.isVanKampen_iff (BinaryCofan.mk
      (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂) coprod.inr)).1
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod Y₁ Y₂)))
      (BinaryCofan.mk (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) coprod.inr)
      p₁ p₂ (coprod.map p₁ p₂) (by simp) (by simp)).1
        ⟨coprodIsCoprod X₁ X₂⟩

/-- Every original represented simplex chooses one binary summand before any operator is
selected. -/
theorem simplex_coprod_factor {Y₁ Y₂ : SSet.{u}} (n : ℕ)
    (b : (Δ[n] : SSet.{u}) ⟶ Y₁ ⨿ Y₂) :
    (∃ β : (Δ[n] : SSet.{u}) ⟶ Y₁, β ≫ coprod.inl = b) ∨
    (∃ β : (Δ[n] : SSet.{u}) ⟶ Y₂, β ≫ coprod.inr = b) := by
  let ev : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌)
  let c : BinaryCofan (ev.obj Y₁) (ev.obj Y₂) := BinaryCofan.mk
    (ev.map (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂)) (ev.map coprod.inr)
  have hc : IsColimit c := isColimitOfHasBinaryCoproductOfPreservesColimit ev Y₁ Y₂
  obtain ⟨⟨j⟩, z, hz⟩ := Types.jointly_surjective_of_isColimit hc (SSet.yonedaEquiv b)
  cases j with
  | left =>
    change (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂).app (Opposite.op ⦋n⦌) z =
      SSet.yonedaEquiv b at hz
    left; refine ⟨SSet.yonedaEquiv.symm z, ?_⟩
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp,
      SSet.yonedaEquiv.apply_symm_apply] using hz
  | right =>
    change (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂).app (Opposite.op ⦋n⦌) z =
      SSet.yonedaEquiv b at hz
    right; refine ⟨SSet.yonedaEquiv.symm z, ?_⟩
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp,
      SSet.yonedaEquiv.apply_symm_apply] using hz

end SSet.BinaryCoproductPullback
