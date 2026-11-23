/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanContraction
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRows
import MathlibExt.CategoryTheory.CategoryBar.ElementsComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveDiscreteIso
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Common-universe realization equivalence of the right-comma source map

For arbitrary object and morphism universes, the original Bousfield--Kan
source augmentation of the right-comma diagram is a realization weak
equivalence. In each inner degree, the actual Elements category projects
to the ordinary discrete category on the original source chains. Its
canonical section and final-arrow contraction give inverse nerve homotopies
in the maximum universe.

The replacement/Elements and discrete-nerve comparisons identify this
projection with the original terminal-weight row augmentation on every
weighted summand. The inner-row diagonal theorem then applies to the
original source-total map, including degree zero.

This proof follows the retained Category0 construction and the project-authored
common-universe source specification. It supplies no chain quasi-isomorphism,
coefficient, spectral, localization or Q=+ comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory MorphismProperty Opposite Simplicial

namespace SSet

universe u v w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The final-arrow contraction gives the projection-then-section homotopy
on the actual Elements nerve. -/
private def sourceDegreePiSigmaHomotopy (F : C ⥤ D) (n : ℕ) :
    SSet.Homotopy
      (nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n) ≫
        nerveMapHomDown.{max u v w, max u v w, max v w} (rightCommaDegreeSigma F n))
      (𝟙 (nerve (rightCommaDegreeCoefficient F n).Elements)) := by
  let H :=
    CategoryTheory.NatTrans.nerveHomotopyHomDown.{max u v w, max v w, max v w}
      (rightCommaDegreeSigmaPiToId F n)
  refine { h := H.h, h₀ := ?_, h₁ := ?_, rel := H.rel }
  · exact H.h₀.trans (by
      ext Δ X
      rfl)
  · exact H.h₁.trans (by
      ext Δ X
      rfl)

/-- The strict section-then-projection identity gives the other homotopy
on the ordinary discrete source-chain nerve. -/
private def sourceDegreeSigmaPiHomotopy (F : C ⥤ D) (n : ℕ) :
    SSet.Homotopy
      (nerveMapHomDown.{max u v w, max u v w, max v w} (rightCommaDegreeSigma F n) ≫
        nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n))
      (𝟙 (nerve (Discrete (ComposableArrows C n)))) := by
  rw [CategoryTheory.nerveMapHomDown_comp.{max u v w, max u v w, max v w, max u v w},
    rightCommaDegreeSigma_comp_pi,
    CategoryTheory.nerveMapHomDown_id.{max u v w, max u v w}]
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
    (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
  exact SSet.RelativeMorphism.Homotopy.refl _

/-- The raw Elements projection realizes to a weak homotopy equivalence. -/
private theorem sourceDegreePi_mem_realizationWeakEquivalences
    (F : C ⥤ D) (n : ℕ) :
    realizationWeakEquivalences
      (nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n)) := by
  change TopCat.weakHomotopyEquivalences.{max u v w}
    (SSet.toTop.map
      (nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n)))
  exact TopCat.mem_of_eq_toFun
    (SSet.realizedHomotopyEquiv _ _
      (nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n))
      (nerveMapHomDown.{max u v w, max u v w, max v w} (rightCommaDegreeSigma F n))
      (sourceDegreePiSigmaHomotopy F n)
      (sourceDegreeSigmaPiHomotopy F n)) rfl

/-- The fixed-degree augmentation through the actual Elements category and
ordinary discrete category on the original source chains. -/
private def sourceDegreeAugmentation (F : C ⥤ D) (n : ℕ) :
    CategoryBar.simplicialReplacement (rightCommaDegreeCoefficient F n) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C n) :=
  (CategoryBar.replNerveSimplicialIso
      (rightCommaDegreeCoefficient F n)).hom ≫
    nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n) ≫
      (nerveDiscreteIso (ComposableArrows C n)).hom

/-- Every replacement summand retains exactly its original source chain. -/
private theorem sourceDegreeAugmentation_app_apply
    (F : C ⥤ D) (n m : ℕ) (s : ComposableArrows D m)
    (Y : (rightCommaDegreeCoefficient F n).obj s.left) (t : PUnit) :
    (sourceDegreeAugmentation F n).app (op ⦋m⦌) ⟨s, Y, t⟩ =
      Y ⋙ rightCommaProjectionFunctor.{u, v, w} F s.left := by
  let L := rightCommaDegreeCoefficient F n
  have he :
      ((CategoryBar.replElementsEquiv D L m ⟨s, Y, t⟩).obj 0) =
        L.elementsMk s.left Y := by
    refine Functor.Elements.ext _ _ rfl ?_
    change L.map (eqToHom rfl) (L.map (s.map' 0 0) Y) = Y
    rw [eqToHom_refl, s.map'_self 0 (Nat.zero_le m)]
    have hId (X : L.obj s.left) : L.map (𝟙 s.left) X = X :=
      ConcreteCategory.congr_hom (L.map_id s.left) X
    exact (hId _).trans (hId Y)
  change ((rightCommaDegreePi F n).obj
      ((CategoryBar.replElementsEquiv D L m ⟨s, Y, t⟩).obj 0)).as = _
  rw [he, rightCommaDegreePi_obj_as]
  apply Functor.hext
  · intro i
    rfl
  · intro i j g
    apply heq_of_eq
    rfl

/-- The actual transported terminal-weight augmentation is this same
fixed-degree source projection. -/
private theorem sourceDegreeAugmentation_eq
    (F : C ⥤ D) (n : ℕ) :
    terminalWeightDegreeAugmentation
        (rightCommaProjection.{u, v, w} F) (op ⦋n⦌) =
      sourceDegreeAugmentation F n := by
  ext a Z
  obtain ⟨⟨m⟩⟩ := a
  rcases Z with ⟨s, Y, t⟩
  let p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) m := ⟨s, t⟩
  have hAug := ConcreteCategory.congr_hom
    (terminalWeightReplIncl_comp_degreeAugmentation
      (rightCommaProjection.{u, v, w} F) (op ⦋n⦌) m p) Y
  change (terminalWeightDegreeAugmentation
      (rightCommaProjection.{u, v, w} F) (op ⦋n⦌)).app (op ⦋m⦌)
        ⟨s, Y, t⟩ =
    (sourceDegreeAugmentation F n).app (op ⦋m⦌) ⟨s, Y, t⟩
  exact hAug.trans (sourceDegreeAugmentation_app_apply F n m s Y t).symm

/-- Every fixed-degree terminal-weight source augmentation realizes weakly. -/
private theorem sourceDegreeAugmentation_mem_realizationWeakEquivalences
    (F : C ⥤ D) (n : ℕ) :
    realizationWeakEquivalences
      (terminalWeightDegreeAugmentation
        (rightCommaProjection.{u, v, w} F) (op ⦋n⦌)) := by
  rw [sourceDegreeAugmentation_eq]
  unfold sourceDegreeAugmentation
  have hRepl : realizationWeakEquivalences
      (CategoryBar.replNerveSimplicialIso
        (rightCommaDegreeCoefficient F n)).hom :=
    realizationWeakEquivalences.of_isIso _
  have hPi : realizationWeakEquivalences
      (nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n)) :=
    sourceDegreePi_mem_realizationWeakEquivalences F n
  have hReplPi : realizationWeakEquivalences
      ((CategoryBar.replNerveSimplicialIso
        (rightCommaDegreeCoefficient F n)).hom ≫
        nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n)) :=
    realizationWeakEquivalences.comp_mem _ _ hRepl hPi
  have hDisc : realizationWeakEquivalences
      (nerveDiscreteIso (ComposableArrows C n)).hom :=
    realizationWeakEquivalences.of_isIso _
  change realizationWeakEquivalences
    ((CategoryBar.replNerveSimplicialIso
        (rightCommaDegreeCoefficient F n)).hom ≫
      (nerveMapHomDown.{max u v w, max v w, max u v w} (rightCommaDegreePi F n) ≫
        (nerveDiscreteIso (ComposableArrows C n)).hom))
  rw [← Category.assoc]
  exact realizationWeakEquivalences.comp_mem _ _ hReplPi hDisc

/-- The canonical row comparison identifies each actual inner row with the
fixed-degree source augmentation. -/
private theorem sourceWbarAugmentation_inner_row_mem
    (F : C ⥤ D) (n : ℕ) :
    realizationWeakEquivalences
      ((simplicialTransposeFunctor.map
        (wbarAugmentation (rightCommaProjection.{u, v, w} F))).app (op ⦋n⦌)) := by
  have hDegree : realizationWeakEquivalences
      (terminalWeightDegreeAugmentation
        (rightCommaProjection.{u, v, w} F) (op ⦋n⦌)) :=
    sourceDegreeAugmentation_mem_realizationWeakEquivalences F n
  have hRow : realizationWeakEquivalences
      (wbarRowAugmentation (rightCommaProjection.{u, v, w} F) (op ⦋n⦌)) := by
    rw [← terminalWeightRowIso_hom_comp_degreeAugmentation]
    exact RespectsIso.precomp realizationWeakEquivalences
      (terminalWeightRowIso (rightCommaNerveDiagram.{max u w, max v w, u} F) (op ⦋n⦌)).hom _ hDegree
  let eTarget :
      ((SimplicialObject.const SSet.{max u v w}).obj (nerve C) ⋙
          (evaluation SimplexCategoryᵒᵖ (Type (max u v w))).obj (op ⦋n⦌)) ≅
        (Functor.const SimplexCategoryᵒᵖ).obj
          ((nerve C).obj (op ⦋n⦌)) :=
    Functor.constComp SimplexCategoryᵒᵖ (nerve C)
      ((evaluation SimplexCategoryᵒᵖ (Type (max u v w))).obj (op ⦋n⦌))
  have hComparison :
      ((wbarRowEvaluationIso
          (rightCommaNerveDiagram.{max u w, max v w, u} F) (op ⦋n⦌)).hom ≫
        wbarRowAugmentation (rightCommaProjection.{u, v, w} F) (op ⦋n⦌)) =
      ((simplicialTransposeFunctor.map
          (wbarAugmentation (rightCommaProjection.{u, v, w} F))).app (op ⦋n⦌) ≫
        eTarget.hom) := by
    unfold StrictOrdinaryWeightedBar.wbarSimplicial
    rw [wbarRowEvaluationIso_hom_comp_rowAugmentation]
    apply SSet.hom_ext
    intro a
    change ((wbarAugmentation (rightCommaProjection.{u, v, w} F)).app a).app (op ⦋n⦌) =
      ((simplicialTransposeFunctor.map
          (wbarAugmentation (rightCommaProjection.{u, v, w} F))).app (op ⦋n⦌)).app a ≫
        eTarget.hom.app a
    rw [simplicialTranspose_map_app]
    dsimp only [eTarget]
    rw [Functor.constComp_hom_app]
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hEvaluated : realizationWeakEquivalences
      ((wbarRowEvaluationIso
          (rightCommaNerveDiagram.{max u w, max v w, u} F) (op ⦋n⦌)).hom ≫
        wbarRowAugmentation (rightCommaProjection.{u, v, w} F) (op ⦋n⦌)) :=
    RespectsIso.precomp realizationWeakEquivalences
      (wbarRowEvaluationIso
        (rightCommaNerveDiagram.{max u w, max v w, u} F) (op ⦋n⦌)).hom _ hRow
  rw [hComparison] at hEvaluated
  exact (realizationWeakEquivalences.cancel_right_of_respectsIso
    _ eTarget.hom).mp hEvaluated

/-- The original Bousfield--Kan source-total projection of the right-comma
diagram is a realization weak equivalence for arbitrary object and morphism
universes, with values in their maximum. -/
theorem rightCommaTotalToSource_mem_realizationWeakEquivalences_commonUniverse
    (F : C ⥤ D) :
    realizationWeakEquivalences (rightCommaTotalToSource.{u, v, w} F) := by
  unfold rightCommaTotalToSource bkAugmentation
  apply RespectsIso.postcomp realizationWeakEquivalences
    (diagonalConstIso (nerve C)).hom
  exact simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    (wbarAugmentation (rightCommaProjection.{u, v, w} F))
    (fun n => sourceWbarAugmentation_inner_row_mem F n)

end SSet

end
