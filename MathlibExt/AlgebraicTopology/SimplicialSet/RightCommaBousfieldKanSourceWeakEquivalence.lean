/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKan
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanContraction
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionElementsContraction
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Fixed-degree contraction for the right-comma BK source map

In a fixed inner degree, the category of elements of the right-comma nerve
diagram projects to the discrete type of simplices of the source nerve.  A
canonical section places a source chain over its final image object, with
identity final comma arrow.  The last comma arrow gives a natural contraction
from section-after-projection to the identity.

The induced nerve projection is therefore a simplicial homotopy equivalence
and a realization weak equivalence.  It is identified with the
terminal-weight row augmentation, so every fixed row is a realization weak
equivalence.  The inner-row diagonal theorem then proves the source-total map
a realization weak equivalence.  Combined with the conditional target-total
theorem and the global simplicial homotopy, this gives the corresponding
conditional weak-equivalence theorem for `nerveMap F`.

No comma-contractibility hypothesis, homotopy-fiber comparison, or
Quillen-Theorem-B claim is supplied here.
-/

@[expose] public section

noncomputable section

open CategoryTheory MorphismProperty Opposite Simplicial

namespace SSet

universe u

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

/-- A small-hom discrete category on the fixed-degree source chains. -/
abbrev rightCommaDegreeSmallDiscrete (C : Type u) [Category.{0} C]
    (n : ℕ) :=
  ShrinkHoms (Discrete (ComposableArrows C n))

/-- Its nerve, in the ambient simplicial-set universe. -/
abbrev rightCommaDegreeSmallNerve (C : Type u) [Category.{0} C]
    (n : ℕ) : SSet.{u} :=
  nerve.{0, u} (rightCommaDegreeSmallDiscrete C n)

/-- The fixed-degree projection with its discrete target's homs shrunk to
the small universe. -/
noncomputable def rightCommaDegreePiSmall (F : C ⥤ D) (n : ℕ) :
    (rightCommaDegreeCoefficient F n).Elements ⥤
      rightCommaDegreeSmallDiscrete C n :=
  rightCommaDegreePi F n ⋙
    ShrinkHoms.functor.{0} (Discrete (ComposableArrows C n))

/-- The canonical section of the small-hom fixed-degree projection. -/
noncomputable def rightCommaDegreeSigmaSmall (F : C ⥤ D) (n : ℕ) :
    rightCommaDegreeSmallDiscrete C n ⥤
      (rightCommaDegreeCoefficient F n).Elements :=
  ShrinkHoms.inverse.{0} (Discrete (ComposableArrows C n)) ⋙
    rightCommaDegreeSigma F n

/-- The small-hom section followed by the small-hom projection is strictly
the identity. -/
theorem rightCommaDegreeSigmaSmall_comp_piSmall (F : C ⥤ D) (n : ℕ) :
    rightCommaDegreeSigmaSmall F n ⋙ rightCommaDegreePiSmall F n =
      𝟭 (rightCommaDegreeSmallDiscrete C n) := by
  calc
    rightCommaDegreeSigmaSmall F n ⋙ rightCommaDegreePiSmall F n =
        ShrinkHoms.inverse.{0} (Discrete (ComposableArrows C n)) ⋙
          (rightCommaDegreeSigma F n ⋙ rightCommaDegreePi F n) ⋙
            ShrinkHoms.functor.{0} (Discrete (ComposableArrows C n)) := by
      simp only [rightCommaDegreeSigmaSmall, rightCommaDegreePiSmall,
        Functor.assoc]
    _ = ShrinkHoms.inverse.{0} (Discrete (ComposableArrows C n)) ⋙
          ShrinkHoms.functor.{0} (Discrete (ComposableArrows C n)) := by
      rw [rightCommaDegreeSigma_comp_pi]
      rfl
    _ = 𝟭 (rightCommaDegreeSmallDiscrete C n) := by
      refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro x y f
      exact Shrink.ext (Subsingleton.elim _ _)

/-- The inverse unit comparing the ordinary and small-hom discrete source
categories. -/
noncomputable def rightCommaDegreeShrinkUnitInv
    (C : Type u) [Category.{0} C] (n : ℕ) :
    ShrinkHoms.functor.{0} (Discrete (ComposableArrows C n)) ⋙
        ShrinkHoms.inverse.{0} (Discrete (ComposableArrows C n)) ⟶
      𝟭 (Discrete (ComposableArrows C n)) :=
  (ShrinkHoms.equivalence.{0}
    (Discrete (ComposableArrows C n))).unitIso.inv

/-- The raw final-arrow contraction transported through the small-hom
discrete model. -/
noncomputable def rightCommaDegreeSigmaPiSmallToId
    (F : C ⥤ D) (n : ℕ) :
    rightCommaDegreePiSmall F n ⋙ rightCommaDegreeSigmaSmall F n ⟶
      𝟭 (rightCommaDegreeCoefficient F n).Elements := by
  let α := Functor.whiskerRight
    (Functor.whiskerLeft (rightCommaDegreePi F n)
      (rightCommaDegreeShrinkUnitInv C n))
    (rightCommaDegreeSigma F n)
  have h := α ≫ rightCommaDegreeSigmaPiToId F n
  simpa only [rightCommaDegreePiSmall, rightCommaDegreeSigmaSmall,
    Functor.assoc, Functor.comp_id] using h

/-- A chain in the small-hom discrete source category is canonically its
value at vertex zero. -/
noncomputable def rightCommaDegreeSmallNerveObjEquiv
    (C : Type u) [Category.{0} C] (n : ℕ)
    (a : SimplexCategoryᵒᵖ) :
    (rightCommaDegreeSmallNerve C n).obj a ≃ ComposableArrows C n where
  toFun F := (ShrinkHoms.fromShrinkHoms (F.obj 0)).as
  invFun x := (Functor.const (Fin (a.unop.len + 1))).obj
    (ShrinkHoms.toShrinkHoms (Discrete.mk x))
  left_inv F := by
    fapply CategoryTheory.Functor.ext
    · intro i
      apply Discrete.ext
      let f : ShrinkHoms.fromShrinkHoms (F.obj 0) ⟶
          ShrinkHoms.fromShrinkHoms (F.obj i) :=
        (equivShrink _).symm (F.map (homOfLE (Fin.zero_le i)))
      exact f.eq
    · intro i j f
      exact Shrink.ext (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- The small-hom discrete source-chain nerve is the constant simplicial set
on source chains. -/
noncomputable def rightCommaDegreeSmallNerveIso
    (C : Type u) [Category.{0} C] (n : ℕ) :
    rightCommaDegreeSmallNerve C n ≅
      (Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C n) :=
  NatIso.ofComponents
    (fun a => (rightCommaDegreeSmallNerveObjEquiv C n a).toIso) (by
      intro a b k
      apply ConcreteCategory.hom_ext
      intro F
      let f : ShrinkHoms.fromShrinkHoms (F.obj 0) ⟶
          ShrinkHoms.fromShrinkHoms (F.obj (k.unop.toOrderHom 0)) :=
        (equivShrink _).symm
          (F.map (homOfLE (Fin.zero_le (k.unop.toOrderHom 0))))
      exact f.eq.symm)

@[simp]
theorem rightCommaDegreePiSmall_obj_as (F : C ⥤ D) (n : ℕ)
    (e : (rightCommaDegreeCoefficient F n).Elements) :
    (ShrinkHoms.fromShrinkHoms ((rightCommaDegreePiSmall F n).obj e)).as =
      e.val ⋙ rightCommaProjectionFunctor F e.obj :=
  rfl

/-- Homotopy from projection followed by its canonical section to the
identity on the fixed-degree Elements nerve. -/
noncomputable def rightCommaDegreePiSigmaHomotopy (F : C ⥤ D) (n : ℕ) :
    SSet.Homotopy
      (nerveMap (rightCommaDegreePiSmall F n) ≫
        nerveMap (rightCommaDegreeSigmaSmall F n))
      (𝟙 (nerve (rightCommaDegreeCoefficient F n).Elements)) := by
  simpa only [CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_id] using
    CategoryTheory.NatTrans.nerveHomotopy
      (rightCommaDegreeSigmaPiSmallToId F n)

/-- Homotopy from section followed by projection to the identity on the
discrete source-chain nerve. -/
noncomputable def rightCommaDegreeSigmaPiHomotopy (F : C ⥤ D) (n : ℕ) :
    SSet.Homotopy
      (nerveMap (rightCommaDegreeSigmaSmall F n) ≫
        nerveMap (rightCommaDegreePiSmall F n))
      (𝟙 (rightCommaDegreeSmallNerve C n)) := by
  rw [CategoryTheory.nerveMap_comp,
    rightCommaDegreeSigmaSmall_comp_piSmall,
    CategoryTheory.nerveMap_id]
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
    (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
  exact SSet.RelativeMorphism.Homotopy.refl _

/-- Realized homotopy equivalence induced by the fixed-degree Elements
projection. -/
noncomputable def rightCommaDegreePiRealizedHomotopyEquiv
    (F : C ⥤ D) (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (rightCommaDegreeCoefficient F n).Elements))
      (SSet.toTop.obj (rightCommaDegreeSmallNerve C n)) :=
  SSet.realizedHomotopyEquiv _ _
    (nerveMap (rightCommaDegreePiSmall F n))
    (nerveMap (rightCommaDegreeSigmaSmall F n))
    (rightCommaDegreePiSigmaHomotopy F n)
    (rightCommaDegreeSigmaPiHomotopy F n)

/-- The nerve of the fixed-degree Elements projection is a realization weak
equivalence. -/
theorem rightCommaDegreePi_mem_realizationWeakEquivalences
    (F : C ⥤ D) (n : ℕ) :
    realizationWeakEquivalences
      (nerveMap (rightCommaDegreePiSmall F n)) := by
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (nerveMap (rightCommaDegreePiSmall F n)))
  exact TopCat.mem_of_eq_toFun
    (rightCommaDegreePiRealizedHomotopyEquiv F n) rfl

/-- Fixed-degree projection expressed through the replacement/Elements
comparison and the discrete-nerve comparison. -/
noncomputable def rightCommaDegreeAugmentation (F : C ⥤ D) (n : ℕ) :
    CategoryBar.simplicialReplacement (rightCommaDegreeCoefficient F n) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C n) :=
  (CategoryBar.replNerveSimplicialIso
      (rightCommaDegreeCoefficient F n)).hom ≫
    nerveMap (rightCommaDegreePiSmall F n) ≫
      (rightCommaDegreeSmallNerveIso C n).hom

/-- On a replacement summand, the fixed-degree projection forgets the comma
arrows and retains the underlying source chain. -/
theorem rightCommaDegreeAugmentation_app_apply
    (F : C ⥤ D) (n m : ℕ) (s : ComposableArrows D m)
    (X : (rightCommaDegreeCoefficient F n).obj s.left) (w : PUnit) :
    (rightCommaDegreeAugmentation F n).app (op ⦋m⦌) ⟨s, X, w⟩ =
      X ⋙ rightCommaProjectionFunctor F s.left := by
  let L := rightCommaDegreeCoefficient F n
  have he :
      ((CategoryBar.replElementsEquiv D L m ⟨s, X, w⟩).obj 0) =
        L.elementsMk s.left X := by
    refine Functor.Elements.ext _ _ rfl ?_
    change L.map (eqToHom rfl) (L.map (s.map' 0 0) X) = X
    rw [eqToHom_refl, s.map'_self 0 (Nat.zero_le m)]
    have hId (Y : L.obj s.left) : L.map (𝟙 s.left) Y = Y :=
      ConcreteCategory.congr_hom (L.map_id s.left) Y
    exact (hId _).trans (hId X)
  change (ShrinkHoms.fromShrinkHoms
      ((rightCommaDegreePiSmall F n).obj
        ((CategoryBar.replElementsEquiv D L m ⟨s, X, w⟩).obj 0))).as = _
  rw [he, rightCommaDegreePiSmall_obj_as]

/-- The transported terminal-weight row augmentation is exactly the
replacement/Elements projection. -/
theorem terminalWeightDegreeAugmentation_rightCommaProjection
    (F : C ⥤ D) (n : ℕ) :
    terminalWeightDegreeAugmentation
        (rightCommaProjection F) (op ⦋n⦌) =
      rightCommaDegreeAugmentation F n := by
  ext a Z
  obtain ⟨⟨m⟩⟩ := a
  rcases Z with ⟨s, X, w⟩
  let p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) m := ⟨s, w⟩
  have hAug := ConcreteCategory.congr_hom
    (terminalWeightReplIncl_comp_degreeAugmentation
      (rightCommaProjection F) (op ⦋n⦌) m p) X
  change (terminalWeightDegreeAugmentation
      (rightCommaProjection F) (op ⦋n⦌)).app (op ⦋m⦌)
        ⟨s, X, w⟩ =
    (rightCommaDegreeAugmentation F n).app (op ⦋m⦌) ⟨s, X, w⟩
  exact hAug.trans (rightCommaDegreeAugmentation_app_apply F n m s X w).symm

/-- Every fixed-degree terminal-weight row augmentation of the right-comma
projection is a realization weak equivalence. -/
theorem terminalWeightDegreeAugmentation_rightCommaProjection_mem
    (F : C ⥤ D) (n : ℕ) :
    realizationWeakEquivalences
      (terminalWeightDegreeAugmentation
        (rightCommaProjection F) (op ⦋n⦌)) := by
  rw [terminalWeightDegreeAugmentation_rightCommaProjection]
  unfold rightCommaDegreeAugmentation
  have hRepl : realizationWeakEquivalences
      (CategoryBar.replNerveSimplicialIso
        (rightCommaDegreeCoefficient F n)).hom :=
    realizationWeakEquivalences.of_isIso _
  have hPi : realizationWeakEquivalences
      (nerveMap (rightCommaDegreePiSmall F n)) :=
    rightCommaDegreePi_mem_realizationWeakEquivalences F n
  have hReplPi : realizationWeakEquivalences
      ((CategoryBar.replNerveSimplicialIso
        (rightCommaDegreeCoefficient F n)).hom ≫
        nerveMap (rightCommaDegreePiSmall F n)) :=
    realizationWeakEquivalences.comp_mem _ _ hRepl hPi
  have hDisc : realizationWeakEquivalences
      (rightCommaDegreeSmallNerveIso C n).hom :=
    realizationWeakEquivalences.of_isIso _
  change realizationWeakEquivalences
    ((CategoryBar.replNerveSimplicialIso
        (rightCommaDegreeCoefficient F n)).hom ≫
      (nerveMap (rightCommaDegreePiSmall F n) ≫
        (rightCommaDegreeSmallNerveIso C n).hom))
  rw [← Category.assoc]
  exact realizationWeakEquivalences.comp_mem _ _ hReplPi hDisc

/-- Every inner row of the weighted-bar augmentation induced by the
right-comma projection is a realization weak equivalence. -/
theorem rightCommaWbarAugmentation_inner_row_mem
    (F : C ⥤ D) (n : ℕ) :
    realizationWeakEquivalences
      ((simplicialTransposeFunctor.map
        (wbarAugmentation (rightCommaProjection F))).app (op ⦋n⦌)) := by
  have hDegree : realizationWeakEquivalences
      (terminalWeightDegreeAugmentation
        (rightCommaProjection F) (op ⦋n⦌)) :=
    terminalWeightDegreeAugmentation_rightCommaProjection_mem F n
  have hRow : realizationWeakEquivalences
      (wbarRowAugmentation (rightCommaProjection F) (op ⦋n⦌)) := by
    rw [← terminalWeightRowIso_hom_comp_degreeAugmentation]
    exact RespectsIso.precomp realizationWeakEquivalences
      (terminalWeightRowIso (rightCommaNerveDiagram F) (op ⦋n⦌)).hom _ hDegree
  let eTarget :
      ((SimplicialObject.const SSet.{u}).obj (nerve C) ⋙
          (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌)) ≅
        (Functor.const SimplexCategoryᵒᵖ).obj
          ((nerve C).obj (op ⦋n⦌)) :=
    Functor.constComp SimplexCategoryᵒᵖ (nerve C)
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌))
  have hComparison :
      ((wbarRowEvaluationIso
          (rightCommaNerveDiagram F) (op ⦋n⦌)).hom ≫
        wbarRowAugmentation (rightCommaProjection F) (op ⦋n⦌)) =
      ((simplicialTransposeFunctor.map
          (wbarAugmentation (rightCommaProjection F))).app (op ⦋n⦌) ≫
        eTarget.hom) := by
    unfold StrictOrdinaryWeightedBar.wbarSimplicial
    rw [wbarRowEvaluationIso_hom_comp_rowAugmentation]
    apply SSet.hom_ext
    intro a
    change ((wbarAugmentation (rightCommaProjection F)).app a).app (op ⦋n⦌) =
      ((simplicialTransposeFunctor.map
          (wbarAugmentation (rightCommaProjection F))).app (op ⦋n⦌)).app a ≫
        eTarget.hom.app a
    rw [simplicialTranspose_map_app]
    dsimp only [eTarget]
    rw [Functor.constComp_hom_app]
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hEvaluated : realizationWeakEquivalences
      ((wbarRowEvaluationIso
          (rightCommaNerveDiagram F) (op ⦋n⦌)).hom ≫
        wbarRowAugmentation (rightCommaProjection F) (op ⦋n⦌)) :=
    RespectsIso.precomp realizationWeakEquivalences
      (wbarRowEvaluationIso
        (rightCommaNerveDiagram F) (op ⦋n⦌)).hom _ hRow
  rw [hComparison] at hEvaluated
  exact (realizationWeakEquivalences.cancel_right_of_respectsIso
    _ eTarget.hom).mp hEvaluated

/-- The Bousfield--Kan source-total projection of the right-comma diagram is
unconditionally a realization weak equivalence. -/
theorem rightCommaTotalToSource_mem_realizationWeakEquivalences
    (F : C ⥤ D) :
    realizationWeakEquivalences (rightCommaTotalToSource F) := by
  unfold rightCommaTotalToSource bkAugmentation
  apply RespectsIso.postcomp realizationWeakEquivalences
    (diagonalConstIso (nerve C)).hom
  exact simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    (wbarAugmentation (rightCommaProjection F))
    (fun n => rightCommaWbarAugmentation_inner_row_mem F n)

/-- Conditional right-comma Quillen-A conclusion: if every comma-to-point
component is a realization weak equivalence, then so is `nerveMap F`. -/
theorem nerveMap_mem_realizationWeakEquivalences_of_rightComma
    (F : C ⥤ D)
    (hPoint : ∀ d, realizationWeakEquivalences
      ((rightCommaToPoint F).app d)) :
    realizationWeakEquivalences (nerveMap F) := by
  have hSource : realizationWeakEquivalences
      (rightCommaTotalToSource F) :=
    rightCommaTotalToSource_mem_realizationWeakEquivalences F
  have hComposite : realizationWeakEquivalences
      (rightCommaTotalToSource F ≫ nerveMap F) :=
    rightCommaTotalToSource_comp_nerveMap_mem_realizationWeakEquivalences
      F hPoint
  exact realizationWeakEquivalences.of_precomp
    (rightCommaTotalToSource F) (nerveMap F) hSource hComposite

end SSet

end
