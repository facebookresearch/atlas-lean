/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRows
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionElementsContraction

import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Weak equivalence of the simplex-resolution augmentation

The augmentation of the simplex resolution is a realization weak
equivalence.  In each fixed inner degree, the Elements contraction supplies
a simplicial homotopy inverse.  The terminal-weight row comparisons identify
these degreewise augmentations with the rows of the Bousfield--Kan
augmentation, and the row-to-diagonal theorem then gives the result on the
simplicial diagonal.

This file proves only the weak-equivalence property of the augmentation.  It
makes no Quillen Theorem A, Waldhausen additivity, loop-space, or spectrum
claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty Opposite Simplicial

open scoped Simplicial

universe u

namespace SSet

/-- In every fixed inner degree, the simplex-resolution augmentation is a
realization weak equivalence. -/
theorem simplexResolutionDegreeAugmentation_mem_realizationWeakEquivalences
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    realizationWeakEquivalences
      (simplexResolutionDegreeAugmentation p a) := by
  let f := simplexResolutionDegreeAugmentation p a
  let g := simplexResolutionDegreeSection p a
  have hfg : SSet.Homotopy (f ≫ g) (𝟙 _) :=
    simplexResolutionDegreeAugmentationSectionHomotopy p a
  have hgf : SSet.Homotopy (g ≫ f) (𝟙 _) := by
    rw [simplexResolutionDegreeSection_comp_augmentation]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
    exact SSet.RelativeMorphism.Homotopy.refl _
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (simplexResolutionDegreeAugmentation p a))
  exact TopCat.mem_of_eq_toFun
    (SSet.realizedHomotopyEquiv _ _ f g hfg hgf) rfl

/-- For the simplex-pullback cocone, the augmentation transported from the
terminal-weight row is exactly the fixed-degree Elements augmentation. -/
theorem terminalWeightDegreeAugmentation_simplexPullbackCocone
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    terminalWeightDegreeAugmentation (simplexPullbackCocone p) a =
      simplexResolutionDegreeAugmentation p a := by
  ext b z
  induction b using Opposite.rec with
  | _ b =>
      induction b using SimplexCategory.rec with
      | _ n =>
          rcases z with ⟨s, x, w⟩
          let q : StrictOrdinaryWeightedBar.WIdx (SimplexIndex Y)
              (CategoryBar.replUnit (SimplexIndex Y)) n := ⟨s, w⟩
          have h := ConcreteCategory.congr_hom
            (terminalWeightReplIncl_comp_degreeAugmentation
              (simplexPullbackCocone p) a n q) x
          have hApply := CategoryTheory.comp_apply
            (terminalWeightReplIncl (simplexPullbackDiagram p) a n q)
            ((terminalWeightDegreeAugmentation
              (simplexPullbackCocone p) a).app
                (Opposite.op (SimplexCategory.mk n))) x
          have h' := hApply.symm.trans h
          calc
            (terminalWeightDegreeAugmentation
                (simplexPullbackCocone p) a).app
                  (Opposite.op (SimplexCategory.mk n)) ⟨s, x, w⟩ =
                (pullback.fst p s.left.hom).app a x := by
              have hIncl :
                  terminalWeightReplIncl
                      (simplexPullbackDiagram p) a n q x =
                    (⟨s, x, w⟩ : CategoryBar.replObj
                      (SimplexIndex Y) (simplexPullbackDegree p a) n) := by
                rfl
              rw [hIncl] at h'
              exact h'
            _ = (simplexResolutionDegreeAugmentation p a).app
                (Opposite.op (SimplexCategory.mk n)) ⟨s, x, w⟩ :=
              (simplexResolutionDegreeAugmentation_app_apply
                p a n s x w).symm

/-- Every inner row of the Bousfield--Kan augmentation for the
simplex-pullback cocone is a realization weak equivalence. -/
theorem simplexResolutionWbarAugmentation_inner_row_mem
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    realizationWeakEquivalences
      ((simplicialTransposeFunctor.map
        (wbarAugmentation (simplexPullbackCocone p))).app a) := by
  have hDegree : realizationWeakEquivalences
      (terminalWeightDegreeAugmentation (simplexPullbackCocone p) a) := by
    rw [terminalWeightDegreeAugmentation_simplexPullbackCocone]
    exact simplexResolutionDegreeAugmentation_mem_realizationWeakEquivalences p a
  have hRow : realizationWeakEquivalences
      (wbarRowAugmentation (simplexPullbackCocone p) a) := by
    rw [← terminalWeightRowIso_hom_comp_degreeAugmentation]
    exact RespectsIso.precomp realizationWeakEquivalences
      (terminalWeightRowIso (simplexPullbackDiagram p) a).hom _ hDegree
  let eTarget :
      ((SimplicialObject.const SSet.{u}).obj Z ⋙
          (evaluation SimplexCategoryᵒᵖ (Type u)).obj a) ≅
        (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) :=
    Functor.constComp SimplexCategoryᵒᵖ Z
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj a)
  have hComparison :
      ((wbarRowEvaluationIso (simplexPullbackDiagram p) a).hom ≫
          wbarRowAugmentation (simplexPullbackCocone p) a) =
        ((simplicialTransposeFunctor.map
            (wbarAugmentation (simplexPullbackCocone p))).app a ≫
          eTarget.hom) := by
    unfold StrictOrdinaryWeightedBar.wbarSimplicial
    rw [wbarRowEvaluationIso_hom_comp_rowAugmentation]
    apply SSet.hom_ext
    intro b
    change ((wbarAugmentation (simplexPullbackCocone p)).app b).app a =
      ((simplicialTransposeFunctor.map
          (wbarAugmentation (simplexPullbackCocone p))).app a).app b ≫
        eTarget.hom.app b
    rw [simplicialTranspose_map_app]
    dsimp only [eTarget]
    rw [Functor.constComp_hom_app]
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hEvaluated : realizationWeakEquivalences
      ((wbarRowEvaluationIso (simplexPullbackDiagram p) a).hom ≫
        wbarRowAugmentation (simplexPullbackCocone p) a) :=
    RespectsIso.precomp realizationWeakEquivalences
      (wbarRowEvaluationIso (simplexPullbackDiagram p) a).hom _ hRow
  rw [hComparison] at hEvaluated
  exact (realizationWeakEquivalences.cancel_right_of_respectsIso
    _ eTarget.hom).mp hEvaluated

/-- The canonical augmentation from the simplex resolution to its source is
a realization weak equivalence. -/
theorem simplexResolutionAugmentation_mem_realizationWeakEquivalences
    {Z Y : SSet.{u}} (p : Z ⟶ Y) :
    realizationWeakEquivalences (simplexResolutionAugmentation p) := by
  unfold simplexResolutionAugmentation bkAugmentation
  apply RespectsIso.postcomp realizationWeakEquivalences
    (diagonalConstIso Z).hom
  exact simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    (wbarAugmentation (simplexPullbackCocone p))
    (fun n => simplexResolutionWbarAugmentation_inner_row_mem p
      (Opposite.op (SimplexCategory.mk n)))

end SSet

end
