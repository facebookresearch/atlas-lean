/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Pullback stability of sharp maps

Sharp maps of simplicial sets remain sharp after pullback along an arbitrary base map. The proof uses explicit isomorphisms between nested and composite pullbacks, with both projection equations and naturality for every map between test objects.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SSet.SharpComparisonDraft
namespace SSet.SharpPullbackClosure

/-- The original nested pullback is the pullback over the composite base map. -/
def nestedPullbackIso {X B A T : SSet.{u}}
    (p : X ⟶ B) (a : A ⟶ B) (t : T ⟶ A) :
    pullback (pullback.snd p a) t ≅ pullback p (t ≫ a) :=
  ((IsPullback.of_hasPullback (pullback.snd p a) t).paste_horiz
    (IsPullback.of_hasPullback p a)).isoPullback

/-- Both original forward projections of that SAME chosen isomorphism. -/
theorem nestedPullbackIso_hom_legs {X B A T : SSet.{u}}
    (p : X ⟶ B) (a : A ⟶ B) (t : T ⟶ A) :
    (nestedPullbackIso p a t).hom ≫ pullback.fst p (t ≫ a) =
        pullback.fst (pullback.snd p a) t ≫ pullback.fst p a ∧
      (nestedPullbackIso p a t).hom ≫ pullback.snd p (t ≫ a) =
        pullback.snd (pullback.snd p a) t :=
  ⟨((IsPullback.of_hasPullback (pullback.snd p a) t).paste_horiz
      (IsPullback.of_hasPullback p a)).isoPullback_hom_fst,
    ((IsPullback.of_hasPullback (pullback.snd p a) t).paste_horiz
      (IsPullback.of_hasPullback p a)).isoPullback_hom_snd⟩

/-- Both DIRECT inverse projections, including the actual lift into the
original pullback p,a, not only its composite projection into X. -/
theorem nestedPullbackIso_inv_legs {X B A T : SSet.{u}}
    (p : X ⟶ B) (a : A ⟶ B) (t : T ⟶ A) :
    (nestedPullbackIso p a t).inv ≫ pullback.fst (pullback.snd p a) t =
      pullback.lift (pullback.fst p (t ≫ a)) (pullback.snd p (t ≫ a) ≫ t)
        (by simpa only [Category.assoc] using (pullback.condition (f := p) (g := t ≫ a))) ∧
    (nestedPullbackIso p a t).inv ≫ pullback.snd (pullback.snd p a) t =
      pullback.snd p (t ≫ a) := by
  let H := (IsPullback.of_hasPullback (pullback.snd p a) t).paste_horiz
    (IsPullback.of_hasPullback p a)
  have hF : (nestedPullbackIso p a t).inv ≫
      (pullback.fst (pullback.snd p a) t ≫ pullback.fst p a) =
      pullback.fst p (t ≫ a) := H.isoPullback_inv_fst
  have hS : (nestedPullbackIso p a t).inv ≫ pullback.snd (pullback.snd p a) t =
      pullback.snd p (t ≫ a) := H.isoPullback_inv_snd
  constructor
  · apply pullback.hom_ext
    · calc
        ((nestedPullbackIso p a t).inv ≫ pullback.fst (pullback.snd p a) t) ≫
            pullback.fst p a =
          (nestedPullbackIso p a t).inv ≫
            (pullback.fst (pullback.snd p a) t ≫ pullback.fst p a) :=
          Category.assoc _ _ _
        _ = pullback.fst p (t ≫ a) := hF
        _ = _ := (pullback.lift_fst _ _ _).symm
    · calc
        ((nestedPullbackIso p a t).inv ≫ pullback.fst (pullback.snd p a) t) ≫
            pullback.snd p a =
          (nestedPullbackIso p a t).inv ≫
            (pullback.fst (pullback.snd p a) t ≫ pullback.snd p a) :=
          Category.assoc _ _ _
        _ = (nestedPullbackIso p a t).inv ≫
            (pullback.snd (pullback.snd p a) t ≫ t) := by rw [pullback.condition]
        _ = ((nestedPullbackIso p a t).inv ≫ pullback.snd (pullback.snd p a) t) ≫ t :=
          (Category.assoc _ _ _).symm
        _ = pullback.snd p (t ≫ a) ≫ t := by rw [hS]
        _ = _ := (pullback.lift_snd _ _ _).symm
  · exact hS

/-- Naturality for EVERY original operator w, without a weakness premise.
The SAME w and original p,a,v occur on both ordinary pullback maps. -/
theorem nestedPullbackIso_operator {X B A U V : SSet.{u}}
    (p : X ⟶ B) (a : A ⟶ B) (w : U ⟶ V) (v : V ⟶ A) :
    pullback.map (pullback.snd p a) (w ≫ v) (pullback.snd p a) v
        (𝟙 (pullback p a)) w (𝟙 A) (by simp) (by simp) ≫
      (nestedPullbackIso p a v).hom =
    (nestedPullbackIso p a (w ≫ v)).hom ≫
      pullback.map p ((w ≫ v) ≫ a) p (v ≫ a)
        (𝟙 X) w (𝟙 B) (by simp) (by simp [Category.assoc]) ∧
    (nestedPullbackIso p a (w ≫ v)).inv ≫
      pullback.map (pullback.snd p a) (w ≫ v) (pullback.snd p a) v
        (𝟙 (pullback p a)) w (𝟙 A) (by simp) (by simp) =
    pullback.map p ((w ≫ v) ≫ a) p (v ≫ a)
        (𝟙 X) w (𝟙 B) (by simp) (by simp [Category.assoc]) ≫
      (nestedPullbackIso p a v).inv := by
  have h : pullback.map (pullback.snd p a) (w ≫ v) (pullback.snd p a) v
      (𝟙 (pullback p a)) w (𝟙 A) (by simp) (by simp) ≫
        (nestedPullbackIso p a v).hom =
      (nestedPullbackIso p a (w ≫ v)).hom ≫
        pullback.map p ((w ≫ v) ≫ a) p (v ≫ a)
          (𝟙 X) w (𝟙 B) (by simp) (by simp [Category.assoc]) := by
    apply pullback.hom_ext
    · simp [nestedPullbackIso, pullback.map, Category.assoc]
    · simp [nestedPullbackIso, pullback.map, Category.assoc]
  refine ⟨h, ?_⟩
  apply (cancel_epi (nestedPullbackIso p a (w ≫ v)).hom).mp
  apply (cancel_mono (nestedPullbackIso p a v).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h

/-- Whole Arrow transport keeps the original test object T as codomain. -/
def nestedPullbackArrowIso {X B A T : SSet.{u}}
    (p : X ⟶ B) (a : A ⟶ B) (t : T ⟶ A) :
    Arrow.mk (pullback.snd (pullback.snd p a) t) ≅
      Arrow.mk (pullback.snd p (t ≫ a)) :=
  Arrow.isoMk (nestedPullbackIso p a t) (Iso.refl _) (by
    change (nestedPullbackIso p a t).hom ≫ pullback.snd p (t ≫ a) =
      pullback.snd (pullback.snd p a) t ≫ (𝟙 T)
    rw [Category.comp_id]
    exact (nestedPullbackIso_hom_legs p a t).2)

/-- Actual base-change closure of the comparison-based Sharp predicate.
This is distinct from the existing SharpBaseChange p conversion theorem. -/
theorem sharp_pullback_snd {X B A : SSet.{u}}
    (p : X ⟶ B) (a : A ⟶ B) (hp : Sharp p) :
    Sharp (pullback.snd p a) := by
  apply sharp_of_baseChange (pullback.snd p a)
  intro U V w v hw
  let mq := pullback.map (pullback.snd p a) (w ≫ v) (pullback.snd p a) v
    (𝟙 (pullback p a)) w (𝟙 A) (by simp) (by simp)
  let mp := pullback.map p ((w ≫ v) ≫ a) p (v ≫ a)
    (𝟙 X) w (𝟙 B) (by simp) (by simp [Category.assoc])
  have hmp : WeakEquivalence mp := by
    let mr := pullback.map p (w ≫ (v ≫ a)) p (v ≫ a)
      (𝟙 X) w (𝟙 B) (by simp) (by simp)
    let c : pullback p ((w ≫ v) ≫ a) ≅ pullback p (w ≫ (v ≫ a)) :=
      pullback.congrHom (f₁ := p) (f₂ := p) rfl (Category.assoc w v a)
    have hc : mp = c.hom ≫ mr := by
      apply pullback.hom_ext
      · simp only [mp, mr, c, pullback.congrHom_hom, Category.assoc,
          pullback.lift_fst, Category.comp_id]
      · simp only [mp, mr, c, pullback.congrHom_hom, Category.assoc,
          pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
    have hr : WeakEquivalence mr := Sharp.baseChange p hp U V w (v ≫ a) hw
    let _ := hr
    rw [hc]
    infer_instance
  have hmap : mq ≫ (nestedPullbackIso p a v).hom =
      (nestedPullbackIso p a (w ≫ v)).hom ≫ mp := (nestedPullbackIso_operator p a w v).1
  let _ : WeakEquivalence mp := hmp
  have hcomp : WeakEquivalence (mq ≫ (nestedPullbackIso p a v).hom) := by
    rw [hmap]
    infer_instance
  let _ := hcomp
  exact weakEquivalence_of_postcomp mq (nestedPullbackIso p a v).hom

end SSet.SharpPullbackClosure
