/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.FreeRepresentableCells
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! # Public original free-evaluation contract tests -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits SimplicialPresheaf Opposite

attribute [local instance] SimplicialPresheaf.freeEvaluationHomCoproducts

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

example {d d' d'' : D} (f : d ⟶ d') (g : d' ⟶ d'') :
    freeEvaluationFunctor.map (f ≫ g) = freeEvaluationFunctor.map f ≫
      freeEvaluationFunctor.map g :=
  freeEvaluationFunctor.map_comp f g

example {d d' : D} (f : d ⟶ d') :
    freeEvaluationFunctor.map f ≫ (freeEvaluationScalarIso.app d').hom =
      (freeEvaluationScalarIso.app d).hom ≫ (discreteYoneda ⋙ scalarTensor).map f :=
  freeEvaluationScalarIso.hom.naturality f

example (d : D) {K L : SSet.{u}} (j : K ⟶ L) :
    (freeEvaluationFunctor.obj d).map j ≫ (freeEvaluationScalarIso.app d).hom.app L =
      (freeEvaluationScalarIso.app d).hom.app K ≫
        (scalarTensor.obj (discreteYoneda.obj d)).map j :=
  (freeEvaluationScalarIso.app d).hom.naturality j

example (d : D) (K : SSet.{u}) (e : Dᵒᵖ) (h : op d ⟶ e)
    (Δ : SimplexCategoryᵒᵖ) (k : K.obj Δ) :
    (((freeEvaluationScalarIso.app d).hom.app K).app e).app Δ
        ((Sigma.ι (fun _ : op d ⟶ e => K) h).app Δ k) =
      ((discreteYonedaObjEquiv d e Δ).symm h.unop, k) :=
  freeEvaluationScalarIso_hom_ι d K e h Δ k

example (d : D) (K : SSet.{u}) (e : Dᵒᵖ) (Δ : SimplexCategoryᵒᵖ)
    (x : ((discreteYoneda.obj d).obj e).obj Δ) (k : K.obj Δ) :
    (((freeEvaluationScalarIso.app d).inv.app K).app e).app Δ (x, k) =
      (Sigma.ι (fun _ : op d ⟶ e => K) (discreteYonedaObjEquiv d e Δ x).op).app Δ k :=
  freeEvaluationScalarIso_inv_value d K e Δ x k

example (d : D) (K : SSet.{u}) :
    (evaluationAdjunctionRight SSet.{u} (op d)).unit.app K ≫
        ((evaluation Dᵒᵖ SSet.{u}).obj (op d)).map
          ((freeEvaluationScalarIso.app d).hom.app K) =
      (discreteYonedaScalarAdjunction d).unit.app K :=
  (freeEvaluationScalarIso_unit d K).1

example (d : D) (Z : SimplicialPresheaf.{u} D) :
    (freeEvaluationScalarIso.app d).inv.app (Z.obj (op d)) ≫
        (evaluationAdjunctionRight SSet.{u} (op d)).counit.app Z =
      (discreteYonedaScalarAdjunction d).counit.app Z :=
  (freeEvaluationScalarIso_counit d Z).2

example (d : D) (n : ℕ) :
    Arrow.mk ((freeEvaluationFunctor.obj d).map (SSet.boundary.{u} n).ι) ≅
      Arrow.mk ((scalarTensor.obj (discreteYoneda.obj d)).map (SSet.boundary.{u} n).ι) :=
  freeScalarArrowIso d (SSet.boundary.{u} n).ι

example (d : D) {K L : SSet.{u}} (j : K ⟶ L) :
    (freeScalarArrowIso d j).hom.left = (freeEvaluationScalarIso.app d).hom.app K ∧
      (freeScalarArrowIso d j).hom.right = (freeEvaluationScalarIso.app d).hom.app L ∧
      (freeScalarArrowIso d j).inv.left = (freeEvaluationScalarIso.app d).inv.app K ∧
      (freeScalarArrowIso d j).inv.right = (freeEvaluationScalarIso.app d).inv.app L :=
  freeScalarArrowIso_legs d j
