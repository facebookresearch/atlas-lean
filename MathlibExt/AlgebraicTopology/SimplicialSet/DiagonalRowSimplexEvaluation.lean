/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.EquifibredDiagonalPullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Whole original row-simplex evaluation into the diagonal

An original ordinal simplex and a whole element of the corresponding row
evaluate to the original diagonal by the operator represented by that
simplex. The map retains every scalar degree, every original operator and
the complete coefficient-map naturality. Its vertex restrictions are the
existing original row-vertex-to-diagonal maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.EquifibredDiagonal

/-- The complete original ordinal simplex evaluates its whole row element into the diagonal. -/
def rowSimplexEvaluation (W : SimplicialObject SSet.{u}) (n : SimplexCategory) :
    (W.obj (op n) ⊗ SSet.stdSimplex.obj n) ⟶ SSet.simplicialDiagonalFunctor.obj W where
  app e := ↾fun z => (W.map (SSet.stdSimplex.objEquiv z.2).op).app e z.1
  naturality a b f := by
    ext z
    rcases z with ⟨x, t⟩
    let alpha := SSet.stdSimplex.objEquiv t
    have h := ConcreteCategory.congr_hom ((W.map alpha.op).naturality f) x
    have hm : SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj n).map f t) = f.unop ≫ alpha := rfl
    change (W.map (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.obj n).map f t)).op).app b
        ((W.obj (op n)).map f x) = _
    rw [hm, op_comp, W.map_comp]
    exact congrArg (fun y => (W.map f).app b y) h

/-- Every scalar degree keeps the same original simplex operator and whole original row element. -/
theorem rowSimplexEvaluation_app (W : SimplicialObject SSet.{u}) (n : SimplexCategory)
    (e : SimplexCategoryᵒᵖ) (x : (W.obj (op n)).obj e) (t : (SSet.stdSimplex.{u}.obj n).obj e) :
    (rowSimplexEvaluation W n).app e (x, t) =
      (W.map (SSet.stdSimplex.objEquiv t).op).app e x := rfl

/-- The original row-simplex evaluation respects the entire original coefficient transformation. -/
theorem rowSimplexEvaluation_naturality {W V : SimplicialObject SSet.{u}} (p : W ⟶ V)
    (n : SimplexCategory) :
    ((p.app (op n)) ⊗ₘ 𝟙 (SSet.stdSimplex.obj n)) ≫ rowSimplexEvaluation V n =
      rowSimplexEvaluation W n ≫ SSet.simplicialDiagonalFunctor.map p := by
  apply NatTrans.ext
  funext e
  apply ConcreteCategory.hom_ext
  intro z
  rcases z with ⟨x, t⟩
  have hp := congrArg (fun q => q.app e) (p.naturality (SSet.stdSimplex.objEquiv t).op)
  change (V.map (SSet.stdSimplex.objEquiv t).op).app e ((p.app (op n)).app e x) =
    (p.app e).app e ((W.map (SSet.stdSimplex.objEquiv t).op).app e x)
  exact (types_congr_hom hp x).symm

/-- The same complete coend relation holds for every original ordinal operator. -/
theorem rowSimplexEvaluation_operator (W : SimplicialObject SSet.{u})
    {n m : SimplexCategory} (f : n ⟶ m) :
    ((W.map f.op) ⊗ₘ 𝟙 (SSet.stdSimplex.obj n)) ≫ rowSimplexEvaluation W n =
      (𝟙 (W.obj (op m)) ⊗ₘ SSet.stdSimplex.map f) ≫ rowSimplexEvaluation W m := by
  ext e z
  rcases z with ⟨x, t⟩
  have hm : SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map f).app e t) =
      SSet.stdSimplex.objEquiv t ≫ f := rfl
  change (W.map (SSet.stdSimplex.objEquiv t).op).app e ((W.map f.op).app e x) = _
  rw [← types_comp_apply, ← NatTrans.comp_app, ← W.map_comp, ← op_comp, ← hm]
  rfl

end SSet.EquifibredDiagonal
