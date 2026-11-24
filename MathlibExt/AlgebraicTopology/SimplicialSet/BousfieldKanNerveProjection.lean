/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointFiberComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialRows
public import MathlibExt.CategoryTheory.NerveCommonHom
public import MathlibExt.CategoryTheory.CategoryBar.ElementsComparison
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# The original Bousfield--Kan nerve projection on every outer operator

The original fixed-row elements comparison supplies the same full
indexing-chain projection. Its naturality records every outer scalar
operator, including identity operators and faces with degenerate targets.
Both the elements and skeletal comparisons use this shared formula.
-/

@[expose] public section

noncomputable section
universe u v

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet

/-- The entire fixed-inner-degree BK row is the original nerve of its coefficient elements. -/
def bkFixedRowIso {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) :
    simplicialRow (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) a ≅
      nerve (wbarDegreeCoefficient D a).Elements :=
  wbarRowEvaluationIso D a ≪≫ terminalWeightRowIso D a ≪≫
    CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)

/-- The actual fixed-inner-degree BK projection retains the original indexing chain. -/
def bkFixedRowProjection {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) :
    simplicialRow (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) a
      ⟶ nerve J :=
  (bkFixedRowIso D a).hom ≫
    nerveMapCommonHom.{u, v, 0} (Functor.Elements.π (wbarDegreeCoefficient D a))

/-- Each original weighted summand projects to its whole original indexing chain. -/
theorem bkFixedRowProjection_wbarIncl
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ)
    (n : ℕ) (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app a ≫
      (bkFixedRowProjection D a).app (op ⦋n⦌) = ↾fun _ => p.1 := by
  apply ConcreteCategory.hom_ext
  intro x
  change (nerveMapCommonHom.{u, v, 0} (Functor.Elements.π (wbarDegreeCoefficient D a))).app (op ⦋n⦌)
      ((CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)).hom.app (op ⦋n⦌)
        ((terminalWeightRowIso D a).hom.app (op ⦋n⦌)
          ((wbarRowEvaluationIso D a).hom.app (op ⦋n⦌)
            ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app a x)))) = p.1
  have he := ConcreteCategory.congr_hom (wbarRowEvaluationIso_hom_app D a (op ⦋n⦌))
    ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app a x)
  have hi := ConcreteCategory.congr_hom (wbarRowIncl_eq_wbarIncl_app D a n p) x
  have he' : (wbarRowEvaluationIso D a).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app a x) =
        wbarRowIncl D a n p x := he.trans hi.symm
  have ht := ConcreteCategory.congr_hom (terminalWeightRowIso_hom_rowIncl D a n p) x
  have het : (terminalWeightRowIso D a).hom.app (op ⦋n⦌)
      ((wbarRowEvaluationIso D a).hom.app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app a x)) =
      terminalWeightReplIncl D a n p x :=
    (congrArg (fun y => (terminalWeightRowIso D a).hom.app (op ⦋n⦌) y) he').trans ht
  have hf :
      (nerveMapCommonHom.{u, v, 0} (Functor.Elements.π (wbarDegreeCoefficient D a))).app (op ⦋n⦌)
      ((CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)).hom.app (op ⦋n⦌)
        (terminalWeightReplIncl D a n p x)) = p.1 := by
    obtain ⟨s, w⟩ := p
    change PUnit at w
    cases w
    rfl
  exact (congrArg (fun y =>
    (nerveMapCommonHom.{u, v, 0} (Functor.Elements.π (wbarDegreeCoefficient D a))).app (op ⦋n⦌)
      ((CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)).hom.app (op ⦋n⦌) y))
      het).trans hf

/-- On the diagonal the fixed-row projection is the same original BK nerve projection. -/
theorem bkFixedRowProjection_diagonal
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkFixedRowProjection D (op ⦋n⦌)).app (op ⦋n⦌) =
      (bkHocolimToNerve D).app (op ⦋n⦌) := by
  let F : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n → SSet.{max u v} :=
    fun p => D.obj p.1.left
  apply (cancel_epi (sigmaObjIso F (op ⦋n⦌)).inv).mp
  apply Sigma.hom_ext
  intro p
  have hι := ι_comp_sigmaObjIso_inv F (op ⦋n⦌) p
  have hl : Sigma.ι (fun s => (F s).obj (op ⦋n⦌)) p ≫ (sigmaObjIso F (op ⦋n⦌)).inv ≫
      (bkFixedRowProjection D (op ⦋n⦌)).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
        (bkFixedRowProjection D (op ⦋n⦌)).app (op ⦋n⦌) :=
    (Category.assoc _ _ _).symm.trans (congrArg
      (fun f => f ≫ (bkFixedRowProjection D (op ⦋n⦌)).app (op ⦋n⦌)) hι)
  have hr : Sigma.ι (fun s => (F s).obj (op ⦋n⦌)) p ≫ (sigmaObjIso F (op ⦋n⦌)).inv ≫
      (bkHocolimToNerve D).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
        (bkHocolimToNerve D).app (op ⦋n⦌) :=
    (Category.assoc _ _ _).symm.trans (congrArg
      (fun f => f ≫ (bkHocolimToNerve D).app (op ⦋n⦌)) hι)
  have hb : (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      (bkHocolimToNerve D).app (op ⦋n⦌) = ↾fun _ => p.1 := by
    apply ConcreteCategory.hom_ext
    intro x
    change (bkPointIsoNerve J).hom.app (op ⦋n⦌)
      ((bkHocolimMap (bkDiagramToPoint D)).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)) = p.1
    have hm := ConcreteCategory.congr_hom (bkHocolimMap_app_mk_ι (bkDiagramToPoint D) n p) x
    have hp := ConcreteCategory.congr_hom (bkPointIsoNerve_hom_wbarIncl (J := J) n p)
      (((bkDiagramToPoint D).app p.1.left).app (op ⦋n⦌) x)
    exact (congrArg (fun y => (bkPointIsoNerve J).hom.app (op ⦋n⦌) y) hm).trans hp
  exact hl.trans ((bkFixedRowProjection_wbarIncl D (op ⦋n⦌) n p).trans hb.symm) |>.trans hr.symm

/-- The original BK projection of an actual outer reindexing retains the
reindexed base chain. This includes faces whose target chain degenerates. -/
theorem bkHocolimToNerve_outerMap_wbarIncl
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋m⦌)) :
    (bkHocolimToNerve D).app (op ⦋m⦌)
        (((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map θ.op).app
          (op ⦋m⦌)
          ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋m⦌) x)) =
      (nerve J).map θ.op p.1 := by
  let z := (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋m⦌) x
  have hn := (bkFixedRowProjection D (op ⦋m⦌)).naturality_apply θ.op z
  have hv := ConcreteCategory.congr_hom (bkFixedRowProjection_wbarIncl D (op ⦋m⦌) n p) x
  have hd := ConcreteCategory.congr_hom (bkFixedRowProjection_diagonal D m)
    (((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map θ.op).app
      (op ⦋m⦌) z)
  exact hd.symm.trans
    (hn.trans (congrArg (fun c : ComposableArrows J n => (nerve J).map θ.op c) hv))

end SSet
