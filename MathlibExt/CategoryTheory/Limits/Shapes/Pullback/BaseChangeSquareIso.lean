/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Full base change of an original pullback square

The native pasted square supplies the complete isomorphism of original
pullbacks, retaining both forward/inverse projection equations and
naturality in every supplied original base map. Category object and
morphism universes remain independent.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.Limits.IsPullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {P X E Y : C} {r : P ⟶ X} {q : P ⟶ E} {p : X ⟶ Y} {e : E ⟶ Y}

/-- The SAME native pullback square after its entire supplied original base map. -/
def baseChangeSquareIso (H : IsPullback r q p e) {T : C}
    (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) : pullback q β ≅ pullback p b := by
  have h : IsPullback (pullback.fst q β ≫ r) (pullback.snd q β) p b := by
    simpa only [hb] using (IsPullback.of_hasPullback q β).paste_horiz H
  exact h.isoPullback

@[reassoc]
lemma baseChangeSquareIso_hom_fst (H : IsPullback r q p e) {T : C}
    (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) :
    (baseChangeSquareIso H β b hb).hom ≫ pullback.fst p b = pullback.fst q β ≫ r := by
  simp only [baseChangeSquareIso, IsPullback.isoPullback_hom_fst]

@[reassoc]
lemma baseChangeSquareIso_hom_snd (H : IsPullback r q p e) {T : C}
    (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) :
    (baseChangeSquareIso H β b hb).hom ≫ pullback.snd p b = pullback.snd q β := by
  simp only [baseChangeSquareIso, IsPullback.isoPullback_hom_snd]

/-- The SAME full inverse preserves the entire original first projection. -/
@[reassoc]
lemma baseChangeSquareIso_inv_fst (H : IsPullback r q p e) {T : C}
    (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) :
    (baseChangeSquareIso H β b hb).inv ≫ (pullback.fst q β ≫ r) = pullback.fst p b := by
  rw [← baseChangeSquareIso_hom_fst H β b hb, Iso.inv_hom_id_assoc]

/-- The SAME full inverse preserves the entire original second projection. -/
@[reassoc]
lemma baseChangeSquareIso_inv_snd (H : IsPullback r q p e) {T : C}
    (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) :
    (baseChangeSquareIso H β b hb).inv ≫ pullback.snd q β = pullback.snd p b := by
  rw [← baseChangeSquareIso_hom_snd H β b hb, Iso.inv_hom_id_assoc]

/-- Every whole original base-map square commutes through both native isomorphisms. -/
lemma baseChangeSquareIso_natural (H : IsPullback r q p e) {T T' : C}
    (β : T ⟶ E) (b : T ⟶ Y) (hb : β ≫ e = b) (a : T' ⟶ T) :
    (baseChangeSquareIso H (a ≫ β) (a ≫ b) (by rw [Category.assoc, hb])).hom ≫
        pullback.map p (a ≫ b) p b (𝟙 X) a (𝟙 Y) (by simp) (by simp) =
      pullback.map q (a ≫ β) q β (𝟙 P) a (𝟙 E) (by simp) (by simp) ≫
        (baseChangeSquareIso H β b hb).hom := by
  apply pullback.hom_ext
  · simp only [pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id,
      baseChangeSquareIso_hom_fst, pullback.lift_fst_assoc]
  · simp only [pullback.map, Category.assoc, pullback.lift_snd,
      baseChangeSquareIso_hom_snd, baseChangeSquareIso_hom_snd_assoc]

end CategoryTheory.Limits.IsPullback
