/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRowsOf
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataEvaluation
import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Terminal-weight rows of the Bousfield--Kan bar

The universe-general implementation is `SSet.BousfieldKanRowsOf` in
`BousfieldKanTerminalWeightRowsOf`. This module preserves the historical
inferable `SSet.{max uJ vJ}` API by explicit specialization of the additional
scalar universe to zero. All original objects, maps, face and degeneracy
laws, inverse comparisons and weighted augmentation equations retain their
full statements and delegate to that single shared proof core.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe uJ vJ

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- Evaluation of an `SSet`-valued diagram in one inner simplicial degree.
For the simplex-pullback diagram this is definitionally the coefficient
functor named `simplexPullbackDegree` in the BK3a layer. -/
abbrev wbarDegreeCoefficient (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) : J ⥤ Type (max uJ vJ) :=
  BousfieldKanRowsOf.wbarDegreeCoefficient.{uJ, vJ, 0} D a

@[simp]
theorem wbarDegreeCoefficient_obj (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (j : J) :
    (wbarDegreeCoefficient D a).obj j = (D.obj j).obj a :=
  BousfieldKanRowsOf.wbarDegreeCoefficient_obj.{uJ, vJ, 0} D a j

@[simp]
theorem wbarDegreeCoefficient_map_apply (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) {j k : J} (f : j ⟶ k)
    (x : (D.obj j).obj a) :
    (wbarDegreeCoefficient D a).map f x = (D.map f).app a x :=
  BousfieldKanRowsOf.wbarDegreeCoefficient_map_apply.{uJ, vJ, 0} D a f x

/-- Simplicial data obtained by evaluating every weighted-bar coefficient in
the fixed inner degree `a`. -/
noncomputable abbrev wbarRowData (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) : SimplicialObject.Data (Type (max uJ vJ)) :=
  BousfieldKanRowsOf.wbarRowData.{uJ, vJ, 0} D a

/-- The fixed-inner-degree row of the terminal-weight weighted bar. -/
noncomputable abbrev wbarRow (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) : SSet.{max uJ vJ} :=
  BousfieldKanRowsOf.wbarRow.{uJ, vJ, 0} D a

/-- Canonical comparison between evaluating the promoted weighted bar and
promoting its evaluated data. -/
noncomputable def wbarRowEvaluationIso (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) :
    (StrictOrdinaryWeightedBar.wbarData
          (CategoryBar.replUnit J) D).toSimplicialObject ⋙
        (evaluation SimplexCategoryᵒᵖ (Type (max uJ vJ))).obj a ≅
      wbarRow D a :=
  BousfieldKanRowsOf.wbarRowEvaluationIso.{uJ, vJ, 0} D a

@[simp]
theorem wbarRowEvaluationIso_hom_app (D : J ⥤ SSet.{max uJ vJ})
    (a b : SimplexCategoryᵒᵖ) :
    (wbarRowEvaluationIso D a).hom.app b = 𝟙 _ :=
  BousfieldKanRowsOf.wbarRowEvaluationIso_hom_app.{uJ, vJ, 0} D a b

@[simp]
theorem wbarRowEvaluationIso_inv_app (D : J ⥤ SSet.{max uJ vJ})
    (a b : SimplexCategoryᵒᵖ) :
    (wbarRowEvaluationIso D a).inv.app b = 𝟙 _ :=
  BousfieldKanRowsOf.wbarRowEvaluationIso_inv_app.{uJ, vJ, 0} D a b

@[simp]
theorem wbarRowData_obj (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (wbarRowData D a).obj n =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D n).obj a :=
  BousfieldKanRowsOf.wbarRowData_obj.{uJ, vJ, 0} D a n

@[simp]
theorem wbarRow_obj_mk (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (wbarRow D a).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D n).obj a :=
  BousfieldKanRowsOf.wbarRow_obj_mk.{uJ, vJ, 0} D a n

theorem wbarRow_map_δ (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) {n : ℕ} (i : Fin (n + 2)) :
    (wbarRow D a).map (SimplexCategory.δ i).op =
      (StrictOrdinaryWeightedBar.wbarδ
        (CategoryBar.replUnit J) D n i).app a :=
  BousfieldKanRowsOf.wbarRow_map_δ.{uJ, vJ, 0} D a i

theorem wbarRow_map_σ (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) {n : ℕ} (i : Fin (n + 1)) :
    (wbarRow D a).map (SimplexCategory.σ i).op =
      (StrictOrdinaryWeightedBar.wbarσ
        (CategoryBar.replUnit J) D n i).app a :=
  BousfieldKanRowsOf.wbarRow_map_σ.{uJ, vJ, 0} D a i

/-- Reassociation which moves the terminal weight out of the weighted index
and into the right coefficient of the ordinary category bar. -/
def terminalWeightSigmaEquiv (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (Σ p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n,
      (D.obj p.1.left).obj a) ≃
      CategoryBar.replObj J (wbarDegreeCoefficient D a) n :=
  BousfieldKanRowsOf.terminalWeightSigmaEquiv.{uJ, vJ, 0} D a n

@[simp]
theorem terminalWeightSigmaEquiv_apply (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) {n : ℕ}
    (s : ComposableArrows J n) (w : PUnit) (x : (D.obj s.left).obj a) :
    terminalWeightSigmaEquiv D a n ⟨⟨s, w⟩, x⟩ =
      (⟨s, x, w⟩ : CategoryBar.replObj J
        (wbarDegreeCoefficient D a) n) :=
  BousfieldKanRowsOf.terminalWeightSigmaEquiv_apply.{uJ, vJ, 0} D a s w x

@[simp]
theorem terminalWeightSigmaEquiv_symm_apply (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) {n : ℕ}
    (s : ComposableArrows J n) (w : PUnit) (x : (D.obj s.left).obj a) :
    (terminalWeightSigmaEquiv D a n).symm
        (⟨s, x, w⟩ : CategoryBar.replObj J
          (wbarDegreeCoefficient D a) n) =
      ⟨⟨s, w⟩, x⟩ :=
  BousfieldKanRowsOf.terminalWeightSigmaEquiv_symm_apply.{uJ, vJ, 0} D a s w x

/-- Inclusion of one evaluated coefficient in the ordinary simplicial-
replacement degree, retaining the chain and terminal weight. -/
def terminalWeightReplIncl (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (D.obj p.1.left).obj a ⟶
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).obj n :=
  BousfieldKanRowsOf.terminalWeightReplIncl.{uJ, vJ, 0} D a n p

@[simp↓]
theorem terminalWeightReplIncl_apply (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj a) :
    terminalWeightReplIncl D a n p x =
      (⟨p.1, x, p.2⟩ : CategoryBar.replObj J
        (wbarDegreeCoefficient D a) n) :=
  BousfieldKanRowsOf.terminalWeightReplIncl_apply.{uJ, vJ, 0} D a n p x

/-- Inclusion of one evaluated coefficient into a weighted-bar row.  It is
the explicit evaluated coproduct inclusion followed by the inverse
`sigmaObjIso`. -/
@[no_expose]
noncomputable def wbarRowIncl (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (D.obj p.1.left).obj a ⟶ (wbarRowData D a).obj n :=
  BousfieldKanRowsOf.wbarRowIncl.{uJ, vJ, 0} D a n p

/-- The explicit row inclusion is the evaluation of `wbarIncl`. -/
theorem wbarRowIncl_eq_wbarIncl_app (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app a :=
  BousfieldKanRowsOf.wbarRowIncl_eq_wbarIncl_app.{uJ, vJ, 0} D a n p

/-- Degreewise terminal-weight comparison. -/
@[no_expose]
noncomputable def terminalWeightRowDegreeIso (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (wbarRowData D a).obj n ≅
      (CategoryBar.simplicialReplacementData
        (wbarDegreeCoefficient D a)).obj n :=
  BousfieldKanRowsOf.terminalWeightRowDegreeIso.{uJ, vJ, 0} D a n

/-- Computation of the degree comparison on the explicit evaluated row
inclusion. -/
@[reassoc]
theorem terminalWeightRowDegreeIso_hom_rowIncl
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p ≫ (terminalWeightRowDegreeIso D a n).hom =
      terminalWeightReplIncl D a n p :=
  BousfieldKanRowsOf.terminalWeightRowDegreeIso_hom_rowIncl.{uJ, vJ, 0} D a n p

/-- A weighted summand is sent to the same chain and coefficient, with its
terminal weight moved to the category-bar right coefficient. -/
@[reassoc]
theorem terminalWeightRowDegreeIso_hom_ι
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app a ≫
      (terminalWeightRowDegreeIso D a n).hom =
      terminalWeightReplIncl D a n p :=
  BousfieldKanRowsOf.terminalWeightRowDegreeIso_hom_ι.{uJ, vJ, 0} D a n p

@[simp↓]
theorem terminalWeightRowDegreeIso_hom_ι_apply
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj a) :
    (terminalWeightRowDegreeIso D a n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app a x) =
      (⟨p.1, x, p.2⟩ : CategoryBar.replObj J
        (wbarDegreeCoefficient D a) n) :=
  BousfieldKanRowsOf.terminalWeightRowDegreeIso_hom_ι_apply.{uJ, vJ, 0} D a n p x

theorem terminalWeightFaceZero_compat
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ 0 =
      (wbarRowData D a).δ 0 ≫
        (terminalWeightRowDegreeIso D a n).hom :=
  BousfieldKanRowsOf.terminalWeightFaceZero_compat.{uJ, vJ, 0} D a n

theorem terminalWeightFaceLast_compat
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ (Fin.last (n + 1)) =
      (wbarRowData D a).δ (Fin.last (n + 1)) ≫
        (terminalWeightRowDegreeIso D a n).hom :=
  BousfieldKanRowsOf.terminalWeightFaceLast_compat.{uJ, vJ, 0} D a n

theorem terminalWeightFaceInner_compat
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) {n : ℕ}
    (q : Fin n) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ q.castSucc.succ =
      (wbarRowData D a).δ q.castSucc.succ ≫
        (terminalWeightRowDegreeIso D a n).hom :=
  BousfieldKanRowsOf.terminalWeightFaceInner_compat.{uJ, vJ, 0} D a q

theorem terminalWeightFace_compat
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ)
    {n : ℕ} (i : Fin (n + 2)) :
    (terminalWeightRowDegreeIso D a (n + 1)).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).δ i =
      (wbarRowData D a).δ i ≫
        (terminalWeightRowDegreeIso D a n).hom :=
  BousfieldKanRowsOf.terminalWeightFace_compat.{uJ, vJ, 0} D a i

theorem terminalWeightDegeneracy_compat
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ)
    {n : ℕ} (i : Fin (n + 1)) :
    (terminalWeightRowDegreeIso D a n).hom ≫
        (CategoryBar.simplicialReplacementData
          (wbarDegreeCoefficient D a)).σ i =
      (wbarRowData D a).σ i ≫
        (terminalWeightRowDegreeIso D a (n + 1)).hom :=
  BousfieldKanRowsOf.terminalWeightDegeneracy_compat.{uJ, vJ, 0} D a i

/-- Data-level terminal-weight row comparison. -/
noncomputable def terminalWeightRowDataIso (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) :
    wbarRowData D a ≅
      CategoryBar.simplicialReplacementData (wbarDegreeCoefficient D a) :=
  BousfieldKanRowsOf.terminalWeightRowDataIso.{uJ, vJ, 0} D a

/-- The data presentation of simplicial replacement is canonically its
packaged simplicial set. -/
noncomputable def terminalWeightReplacementIso (L : J ⥤ Type (max uJ vJ)) :
    (CategoryBar.simplicialReplacementData L).toSimplicialObject ≅
      CategoryBar.simplicialReplacement L :=
  BousfieldKanRowsOf.terminalWeightReplacementIso.{uJ, vJ, 0} L

@[simp]
theorem terminalWeightReplacementIso_hom_app_mk
    (L : J ⥤ Type (max uJ vJ)) (n : ℕ) :
    (terminalWeightReplacementIso L).hom.app (op ⦋n⦌) = 𝟙 _ :=
  BousfieldKanRowsOf.terminalWeightReplacementIso_hom_app_mk.{uJ, vJ, 0} L n

@[simp]
theorem terminalWeightReplacementIso_inv_app_mk
    (L : J ⥤ Type (max uJ vJ)) (n : ℕ) :
    (terminalWeightReplacementIso L).inv.app (op ⦋n⦌) = 𝟙 _ :=
  BousfieldKanRowsOf.terminalWeightReplacementIso_inv_app_mk.{uJ, vJ, 0} L n

/-- Simplicial comparison between a fixed inner weighted-bar row and the
ordinary simplicial replacement of the evaluated diagram. -/
noncomputable def terminalWeightRowIso (D : J ⥤ SSet.{max uJ vJ})
    (a : SimplexCategoryᵒᵖ) :
    wbarRow D a ≅
      CategoryBar.simplicialReplacement (wbarDegreeCoefficient D a) :=
  BousfieldKanRowsOf.terminalWeightRowIso.{uJ, vJ, 0} D a

@[simp]
theorem terminalWeightRowIso_hom_app_mk
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowIso D a).hom.app (op ⦋n⦌) =
      (terminalWeightRowDegreeIso D a n).hom :=
  BousfieldKanRowsOf.terminalWeightRowIso_hom_app_mk.{uJ, vJ, 0} D a n

@[simp]
theorem terminalWeightRowIso_inv_app_mk
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ) :
    (terminalWeightRowIso D a).inv.app (op ⦋n⦌) =
      (terminalWeightRowDegreeIso D a n).inv :=
  BousfieldKanRowsOf.terminalWeightRowIso_inv_app_mk.{uJ, vJ, 0} D a n

/-- The simplicial row comparison has the expected value on every explicit
evaluated row inclusion. -/
@[reassoc]
theorem terminalWeightRowIso_hom_rowIncl
    (D : J ⥤ SSet.{max uJ vJ}) (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p ≫
        (terminalWeightRowIso D a).hom.app (op ⦋n⦌) =
      terminalWeightReplIncl D a n p :=
  BousfieldKanRowsOf.terminalWeightRowIso_hom_rowIncl.{uJ, vJ, 0} D a n p

/-- Data-level evaluation of the BK1 weighted-bar augmentation. -/
noncomputable def wbarRowAugmentationData
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    wbarRowData D a ⟶ SimplicialObject.Data.constData (Z.obj a) :=
  BousfieldKanRowsOf.wbarRowAugmentationData.{uJ, vJ, 0} τ a

@[simp]
theorem wbarRowAugmentationData_app
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ)
    (n : ℕ) :
    (wbarRowAugmentationData τ a).app n =
      (StrictOrdinaryWeightedBar.wbarDesc
        (CategoryBar.replUnit J) D n
          (fun p => τ.app p.1.left)).app a :=
  BousfieldKanRowsOf.wbarRowAugmentationData_app.{uJ, vJ, 0} τ a n

/-- The BK1 weighted-bar augmentation evaluated in a fixed inner degree. -/
noncomputable def wbarRowAugmentation {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    wbarRow D a ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) :=
  BousfieldKanRowsOf.wbarRowAugmentation.{uJ, vJ, 0} τ a

/-- Evaluating the weighted-bar augmentation agrees strictly with the
augmentation of the evaluated row. -/
@[reassoc]
theorem wbarRowEvaluationIso_hom_comp_rowAugmentation
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    (wbarRowEvaluationIso D a).hom ≫ wbarRowAugmentation τ a =
      Functor.whiskerRight (wbarAugmentation τ)
        ((evaluation SimplexCategoryᵒᵖ (Type (max uJ vJ))).obj a) :=
  BousfieldKanRowsOf.wbarRowEvaluationIso_hom_comp_rowAugmentation.{uJ, vJ, 0} τ a

/-- The corresponding augmentation on the ordinary simplicial replacement,
defined by transporting the evaluated BK1 augmentation across the row iso. -/
noncomputable def terminalWeightDegreeAugmentation
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    CategoryBar.simplicialReplacement (wbarDegreeCoefficient D a) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) :=
  BousfieldKanRowsOf.terminalWeightDegreeAugmentation.{uJ, vJ, 0} τ a

/-- The evaluated BK1 augmentation is exactly the row comparison followed by
the transported degree augmentation. -/
@[reassoc]
theorem terminalWeightRowIso_hom_comp_degreeAugmentation
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ) :
    (terminalWeightRowIso D a).hom ≫
        terminalWeightDegreeAugmentation τ a =
      wbarRowAugmentation τ a :=
  BousfieldKanRowsOf.terminalWeightRowIso_hom_comp_degreeAugmentation.{uJ, vJ, 0} τ a

/-- Exact evaluation of the row augmentation on every weighted summand. -/
@[reassoc]
theorem wbarRowAugmentation_ι
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ)
    (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) D n p).app a ≫
      (wbarRowAugmentation τ a).app (op ⦋n⦌) =
      (τ.app p.1.left).app a :=
  BousfieldKanRowsOf.wbarRowAugmentation_ι.{uJ, vJ, 0} τ a n p

/-- Exact row-augmentation formula using the explicit evaluated row
inclusion. -/
@[reassoc]
theorem wbarRowAugmentation_rowIncl
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z) (a : SimplexCategoryᵒᵖ)
    (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    wbarRowIncl D a n p ≫
        (wbarRowAugmentation τ a).app (op ⦋n⦌) =
      (τ.app p.1.left).app a :=
  BousfieldKanRowsOf.wbarRowAugmentation_rowIncl.{uJ, vJ, 0} τ a n p

/-- The transported degree augmentation projects an explicit replacement
summand through the cocone map at the left endpoint of its chain. -/
@[reassoc]
theorem terminalWeightReplIncl_comp_degreeAugmentation
    {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}
    (τ : D ⟶ (Functor.const J).obj Z)
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J
      (CategoryBar.replUnit J) n) :
    terminalWeightReplIncl D a n p ≫
        (terminalWeightDegreeAugmentation τ a).app (op ⦋n⦌) =
      (τ.app p.1.left).app a :=
  BousfieldKanRowsOf.terminalWeightReplIncl_comp_degreeAugmentation.{uJ, vJ, 0} τ a n p

end SSet

end
