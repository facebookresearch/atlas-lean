/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Under
public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantUnderObjects
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Strict inverses and complete relative homotopies under a source

Structural cofibrations from the common source make the original objects
cofibrant in its Under category. All original TopCat targets are fibrant by
their singular Kan complexes. Whitehead there gives a strict inverse of the
given weak comparison. The actual compact-open path object has constant
paths on the entire source image, so both inverse families fix that image.
This is the shared implementation of the based Whitehead theorem: its
PUnit/constant-map specialization retains both singleton-relative families.

The interface is on the actual common carrier category. It requires the
structural cofibrations of the two given source maps, and does not treat an
arbitrary plus map as a cofibration.
-/

public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open scoped TopCat.modelCategory

universe u

namespace TopCat

/-- The selected strict inverse and both full source-image relative families
for the actual original comparison map. -/
structure SourceRelativeInverseData {S Y Z : TopCat.{u}}
    (i : S ⟶ Y) (j : S ⟶ Z) (f : Y ⟶ Z) where
  /-- The actual strict inverse under the common source. -/
  inverse : Z ⟶ Y
  /-- The original forward map has its given strict source triangle. -/
  forward_source : i ≫ f = j
  /-- The chosen inverse has its strict source triangle. -/
  inverse_source : j ≫ inverse = i
  /-- The full inverse family on Y fixes every point in the image of i. -/
  leftHomotopy : ContinuousMap.HomotopyRel (f ≫ inverse).hom
    (𝟙 Y : Y ⟶ Y).hom (Set.range i)
  /-- The full inverse family on Z fixes every point in the image of j. -/
  rightHomotopy : ContinuousMap.HomotopyRel (inverse ≫ f).hom
    (𝟙 Z : Z ⟶ Z).hom (Set.range j)

private theorem sourceUnder_cofibrant {S : TopCat.{u}} (X : Under S)
    [Cofibration X.hom] : IsCofibrant X := by
  have hi : Cofibration (Under.mkIdInitial.to X) := by
    apply (cofibrations_under_iff S _).mpr
    simpa only [Under.mkIdInitial_to_right] using (inferInstance : Cofibration X.hom)
  exact (isCofibrant_iff_of_isInitial (Under.mkIdInitial.to X) Under.mkIdInitial).mpr hi

private theorem sourcePathConstant_weak (Y : TopCat.{u}) :
    TopCat.weakHomotopyEquivalences (TopCat.pathConstant Y) := by
  have hcomp : TopCat.weakHomotopyEquivalences
      (TopCat.pathConstant Y ≫ TopCat.pathEvalZero Y) := by
    rw [TopCat.pathConstant_evalZero]
    exact TopCat.weakHomotopyEquivalences.of_isIso _
  exact TopCat.weakHomotopyEquivalences.of_postcomp _ _
    (TopCat.pathEvalZero_mem_weakHomotopyEquivalences Y) hcomp

private def sourceUnderPathObject {S : TopCat.{u}} (X : Under S) : PathObject X where
  P := Under.mk (X.hom ≫ TopCat.pathConstant X.right)
  p₀ := Under.homMk (TopCat.pathEvalZero X.right) (by
    change (X.hom ≫ TopCat.pathConstant X.right) ≫ TopCat.pathEvalZero X.right = X.hom
    rw [Category.assoc, TopCat.pathConstant_evalZero, Category.comp_id])
  p₁ := Under.homMk (TopCat.pathEvalOne X.right) (by
    change (X.hom ≫ TopCat.pathConstant X.right) ≫ TopCat.pathEvalOne X.right = X.hom
    rw [Category.assoc, TopCat.pathConstant_evalOne, Category.comp_id])
  ι := Under.homMk (TopCat.pathConstant X.right) rfl
  ι_p₀ := by
    apply Under.UnderMorphism.ext
    exact TopCat.pathConstant_evalZero X.right
  ι_p₁ := by
    apply Under.UnderMorphism.ext
    exact TopCat.pathConstant_evalOne X.right
  weakEquivalence_ι := by
    apply (weakEquivalences_under_iff S _).mpr
    exact (weakEquivalence_iff _).mpr (sourcePathConstant_weak X.right)

private theorem sourceUnderPathObject_good {S : TopCat.{u}} (X : Under S) :
    (sourceUnderPathObject X).IsGood := by
  let P := sourceUnderPathObject X
  let F := Under.forget S
  let e : F.obj (X ⨯ X) ≅ X.right ⨯ X.right := PreservesLimitPair.iso F X X
  have he₀ : e.hom ≫ prod.fst = (prod.fst : X ⨯ X ⟶ X).right := by
    rw [show e.hom = prodComparison F X X from PreservesLimitPair.iso_hom F X X]
    exact (prodComparison_fst F X X).trans Under.forget_map
  have he₁ : e.hom ≫ prod.snd = (prod.snd : X ⨯ X ⟶ X).right := by
    rw [show e.hom = prodComparison F X X from PreservesLimitPair.iso_hom F X X]
    exact (prodComparison_snd F X X).trans Under.forget_map
  have hp₀ : P.p₀.right = TopCat.pathEvalZero X.right := rfl
  have hp₁ : P.p₁.right = TopCat.pathEvalOne X.right := rfl
  have h : P.p.right ≫ e.hom = TopCat.pathEndpoints X.right := by
    apply prod.hom_ext
    · rw [Category.assoc, he₀]
      have h₀ := congrArg Under.Hom.right P.p_fst
      rw [Under.comp_right] at h₀
      rw [h₀, hp₀]
      exact (prod.lift_fst (TopCat.pathEvalZero X.right)
        (TopCat.pathEvalOne X.right)).symm
    · rw [Category.assoc, he₁]
      have h₁ := congrArg Under.Hom.right P.p_snd
      rw [Under.comp_right] at h₁
      rw [h₁, hp₁]
      exact (prod.lift_snd (TopCat.pathEvalZero X.right)
        (TopCat.pathEvalOne X.right)).symm
  let _ : Fibration (P.p.right ≫ e.hom) := by
    rw [h]
    exact TopCat.modelCategory.pathEndpoints_fibration X.right
  have hp : Fibration P.p.right := by
    have heq : P.p.right = (P.p.right ≫ e.hom) ≫ e.inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [heq]
    infer_instance
  exact ⟨(fibrations_under_iff S P.p).mpr hp⟩

private def continuousSourceRelativeHomotopy {S : TopCat.{u}}
    {X Y : Under S} {f g : X ⟶ Y}
    (H : (sourceUnderPathObject Y).RightHomotopy f g) :
    ContinuousMap.HomotopyRel f.right.hom g.right.hom (Set.range X.hom) := by
  let hC : C(X.right, C(TopCat.I.{u}, Y.right)) := H.h.right.hom
  have wC : X.hom ≫ H.h.right = Y.hom ≫ TopCat.pathConstant Y.right := Under.w H.h
  have wF : X.hom ≫ f.right = Y.hom := Under.w f
  have h₀ : H.h.right ≫ TopCat.pathEvalZero Y.right = f.right := by
    have h := congrArg Under.Hom.right H.h₀
    rw [Under.comp_right] at h
    exact h
  have h₁ : H.h.right ≫ TopCat.pathEvalOne Y.right = g.right := by
    have h := congrArg Under.Hom.right H.h₁
    rw [Under.comp_right] at h
    exact h
  refine
    { toFun := fun z => hC z.2 ((TopCat.I.homeomorph.{u}).symm z.1)
      continuous_toFun := continuous_eval.comp
        ((hC.continuous.comp continuous_snd).prodMk
          ((TopCat.I.homeomorph.{u}).symm.continuous.comp continuous_fst))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro z
    have ht : (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) =
        (0 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => hC z t) ht).trans
      (ConcreteCategory.congr_hom h₀ z)
  · intro z
    have ht : (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => hC z t) ht).trans
      (ConcreteCategory.congr_hom h₁ z)
  · intro t z hz
    obtain ⟨s, rfl⟩ := hz
    have hFixed : hC (X.hom s) = ContinuousMap.const TopCat.I.{u} (Y.hom s) :=
      ConcreteCategory.congr_hom wC s
    have hEnd : f.right (X.hom s) = Y.hom s := ConcreteCategory.congr_hom wF s
    change hC (X.hom s) ((TopCat.I.homeomorph.{u}).symm t) = f.right (X.hom s)
    rw [hFixed]
    exact hEnd.symm

/-- A weak comparison with its original strict source square and structural
source cofibrations has a strict inverse and both entire-image relative
inverse families. Fibrancy is derived for every actual target; no inverse,
relative family, CW outcome or condition on an arbitrary plus map is supplied. -/
def sourceRelativeInverseOfWeak {S Y Z : TopCat.{u}} (i : S ⟶ Y) (j : S ⟶ Z)
    [Cofibration i] [Cofibration j] (f : Y ⟶ Z)
    (hSource : i ≫ f = j) (hWeak : TopCat.weakHomotopyEquivalences f) :
    SourceRelativeInverseData i j f := by
  let A : Under S := Under.mk i
  let B : Under S := Under.mk j
  let F : A ⟶ B := Under.homMk f hSource
  let _ : Cofibration A.hom := by
    change Cofibration i
    infer_instance
  let _ : Cofibration B.hom := by
    change Cofibration j
    infer_instance
  let _ : IsCofibrant A := sourceUnder_cofibrant A
  let _ : IsCofibrant B := sourceUnder_cofibrant B
  let _ : IsFibrant A := (isFibrant_under_iff S A).mpr
    (SSet.RealizationCWUpgrade.allTopCatObjectsFibrant Y)
  let _ : IsFibrant B := (isFibrant_under_iff S B).mpr
    (SSet.RealizationCWUpgrade.allTopCatObjectsFibrant Z)
  let _ : WeakEquivalence F := by
    apply (weakEquivalences_under_iff S F).mpr
    exact (weakEquivalence_iff f).mpr hWeak
  let w := RightHomotopyClass.whitehead F
  let G := Classical.choose w
  have hLeft : RightHomotopyRel (F ≫ G) (𝟙 A) := (Classical.choose_spec w).1
  have hRight : RightHomotopyRel (G ≫ F) (𝟙 B) := (Classical.choose_spec w).2
  let _ : (sourceUnderPathObject A).IsGood := sourceUnderPathObject_good A
  let _ : (sourceUnderPathObject B).IsGood := sourceUnderPathObject_good B
  let HL := continuousSourceRelativeHomotopy (hLeft.rightHomotopy (sourceUnderPathObject A))
  let HR := continuousSourceRelativeHomotopy (hRight.rightHomotopy (sourceUnderPathObject B))
  exact
    { inverse := G.right
      forward_source := hSource
      inverse_source := Under.w G
      leftHomotopy := HL
      rightHomotopy := HR }

end TopCat

end
