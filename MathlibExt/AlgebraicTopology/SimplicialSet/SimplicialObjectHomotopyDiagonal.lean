/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyMapNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal

/-!
# Original combinatorial homotopies on the diagonal

Evaluate the original SSet-valued combinatorial homotopy at each inner
degree, use its actual cylinder adapter, and take the matching original
outer degree. Whole-cylinder naturality supplies the inner operator law;
the adapter supplies the outer operator law. Both original axes remain
in the resulting actual diagonal interval homotopy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Homotopy

variable {X Y : SimplicialObject SSet.{u}} {f g : X ⟶ Y}

/-- The original inner-degree evaluation of the whole combinatorial homotopy. -/
def innerEvaluation (H : SimplicialObject.Homotopy f g) (k : SimplexCategoryᵒᵖ) :=
  H.whiskerRight (SSet.evaluation.obj k)

/-- An original inner operator acts on every original outer row. -/
def innerOperator (W : SimplicialObject SSet.{u})
    {a b : SimplexCategoryᵒᵖ} (q : a ⟶ b) :
    ((SimplicialObject.whiskering SSet.{u} (Type u)).obj (SSet.evaluation.obj a)).obj W ⟶
      ((SimplicialObject.whiskering SSet.{u} (Type u)).obj (SSet.evaluation.obj b)).obj W where
  app k := (W.obj k).map q
  naturality k l p := ((W.map p).naturality q).symm

/-- The literal original diagonal-cylinder value retains the original inner evaluation. -/
def diagonalHomotopyMapApp (H : SimplicialObject.Homotopy f g) (n : SimplexCategoryᵒᵖ) :
    (SSet.simplicialDiagonalFunctor.obj X ⊗ (Δ[1] : SSet.{u})).obj n ⟶
      (SSet.simplicialDiagonalFunctor.obj Y).obj n :=
  ((innerEvaluation H n).toSSetHomotopyMap).app n

/-- The whole original combinatorial homotopy defines an actual diagonal interval-cylinder map. -/
def diagonalHomotopyMap (H : SimplicialObject.Homotopy f g) :
    (SSet.simplicialDiagonalFunctor.obj X ⊗ (Δ[1] : SSet.{u})) ⟶
      SSet.simplicialDiagonalFunctor.obj Y where
  app := diagonalHomotopyMapApp H
  naturality a b q := by
    have hg : innerOperator X q ≫
        ((SimplicialObject.whiskering SSet.{u} (Type u)).obj (SSet.evaluation.obj b)).map g =
      ((SimplicialObject.whiskering SSet.{u} (Type u)).obj (SSet.evaluation.obj a)).map g ≫
        innerOperator Y q := by
      apply NatTrans.ext
      funext k
      exact (g.app k).naturality q
    have hh (n : ℕ) (i : Fin (n + 1)) :
        (innerOperator X q).app (op (SimplexCategory.mk n)) ≫ (innerEvaluation H b).h i =
      (innerEvaluation H a).h i ≫ (innerOperator Y q).app (op (SimplexCategory.mk (n + 1))) :=
      (H.h i).naturality q
    have inner := toSSetHomotopyMap_naturality (innerEvaluation H a) (innerEvaluation H b)
      (innerOperator X q) (innerOperator Y q) hg hh
    have outer := ((innerEvaluation H a).toSSetHomotopyMap).naturality q
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨x, t⟩
    have hi := types_congr_hom (congrArg (fun p => p.app b) inner)
      ((X.map q).app a x, (Δ[1] : SSet.{u}).map q t)
    have ho := types_congr_hom outer (x, t)
    change ((innerEvaluation H b).toSSetHomotopyMap.app b)
        ((X.map q).app b ((X.obj a).map q x), (Δ[1] : SSet.{u}).map q t) =
      (Y.map q).app b ((Y.obj a).map q
        ((innerEvaluation H a).toSSetHomotopyMap.app a (x, t)))
    have hn := types_congr_hom ((X.map q).naturality q) x
    change (X.map q).app b ((X.obj a).map q x) =
      (X.obj b).map q ((X.map q).app a x) at hn
    rw [hn]
    change (innerEvaluation H b).toSSetHomotopyMap.app b
        ((X.obj b).map q ((X.map q).app a x), (Δ[1] : SSet.{u}).map q t) =
      (Y.obj b).map q ((innerEvaluation H a).toSSetHomotopyMap.app b
        ((X.map q).app a x, (Δ[1] : SSet.{u}).map q t)) at hi
    change (innerEvaluation H a).toSSetHomotopyMap.app b
        ((X.map q).app a x, (Δ[1] : SSet.{u}).map q t) =
      (Y.map q).app a ((innerEvaluation H a).toSSetHomotopyMap.app a (x, t)) at ho
    have hy := types_congr_hom ((Y.map q).naturality q)
      ((innerEvaluation H a).toSSetHomotopyMap.app a (x, t))
    exact hi.trans ((congrArg (fun v => (Y.obj b).map q v) ho).trans hy.symm)

end CategoryTheory.SimplicialObject.Homotopy
