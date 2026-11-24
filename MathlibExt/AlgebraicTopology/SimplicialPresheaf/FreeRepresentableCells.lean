/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-! # Original free evaluation and representable scalar cells

The native Hom-indexed coproduct left adjoint is compared with the actual
discrete representable scalar tensor. The original index, site, scalar and
simplex maps, both adjunction directions and both Arrow endpoints are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D] [smallD : Small.{u} D]
  [localD : LocallySmall.{u} D]

omit smallD in
/-- The original Hom coproducts are obtained only from their genuine working-size smallness. -/
local instance freeEvaluationHomCoproducts :
    ∀ a b : Dᵒᵖ, HasCoproductsOfShape (a ⟶ b) SSet.{u} := by
  intro a b
  let : Small.{u} (a ⟶ b) := inferInstance
  let : HasCoproducts.{u} SSet.{u} := inferInstance
  exact hasCoproductsOfShape_of_small SSet.{u} (a ⟶ b)

/-- The native free evaluation functors, with their original representing-object maps. -/
def freeEvaluationFunctor : D ⥤ (SSet.{u} ⥤ SimplicialPresheaf.{u} D) where
  obj d := evaluationLeftAdjoint SSet.{u} (op d)
  map {d d'} θ :=
    { app K :=
        { app e := Sigma.desc (fun h : op d ⟶ e =>
            Sigma.ι (fun _ : op d' ⟶ e => K) (θ.op ≫ h))
          naturality e e' f := by
            apply Sigma.hom_ext
            intro h
            simp [evaluationLeftAdjoint, Category.assoc] }
      naturality K K' k := by
        apply NatTrans.ext
        funext e
        apply Sigma.hom_ext
        intro h
        simp [evaluationLeftAdjoint, Category.assoc] }
  map_id d := by
    apply NatTrans.ext
    funext K
    apply NatTrans.ext
    funext e
    apply Sigma.hom_ext
    intro h
    simp [evaluationLeftAdjoint]
  map_comp f g := by
    apply NatTrans.ext
    funext K
    apply NatTrans.ext
    funext e
    apply Sigma.hom_ext
    intro h
    simp [evaluationLeftAdjoint, Cofan.mk_ι_app, Category.assoc]

omit smallD in
/-- The original index map reindexes an actual native summand by precomposition. -/
private theorem freeMap_summand {d d' : D} (θ : d ⟶ d') (K : SSet.{u})
    (e : Dᵒᵖ) (h : op d ⟶ e) :
    Sigma.ι (fun _ : op d ⟶ e => K) h ≫
        ((freeEvaluationFunctor.map θ).app K).app e =
      Sigma.ι (fun _ : op d' ⟶ e => K) (θ.op ≫ h) := by
  change Sigma.ι (fun _ : op d ⟶ e => K) h ≫
    Sigma.desc (fun h : op d ⟶ e => Sigma.ι (fun _ : op d' ⟶ e => K) (θ.op ≫ h)) = _
  simp

/-- The fixed component is exactly uniqueness of the two original left adjoints. -/
private def freeComponentIso (d : D) :
    evaluationLeftAdjoint SSet.{u} (op d) ≅ scalarTensor.obj (discreteYoneda.obj d) :=
  (evaluationAdjunctionRight SSet.{u} (op d)).leftAdjointUniq
    (discreteYonedaScalarAdjunction d)

omit smallD in
/-- The comparison on an actual original coproduct summand is its represented scalar unit. -/
private theorem freeComponentIso_summand (d : D) (K : SSet.{u})
    (e : Dᵒᵖ) (h : op d ⟶ e) :
    Sigma.ι (fun _ : op d ⟶ e => K) h ≫ ((freeComponentIso d).hom.app K).app e =
      (discreteYonedaScalarAdjunction d).unit.app K ≫
        ((scalarTensor.obj (discreteYoneda.obj d)).obj K).map h := by
  have hu := (evaluationAdjunctionRight SSet.{u} (op d)).unit_leftAdjointUniq_hom_app
    (discreteYonedaScalarAdjunction d) K
  change Sigma.ι (fun _ : op d ⟶ op d => K) (𝟙 _) ≫
    ((freeComponentIso d).hom.app K).app (op d) =
      (discreteYonedaScalarAdjunction d).unit.app K at hu
  calc
    _ = Sigma.ι (fun _ : op d ⟶ op d => K) (𝟙 _) ≫
        ((evaluationLeftAdjoint SSet.{u} (op d)).obj K).map h ≫
          ((freeComponentIso d).hom.app K).app e := by
      simp [evaluationLeftAdjoint]
    _ = Sigma.ι (fun _ : op d ⟶ op d => K) (𝟙 _) ≫
        ((freeComponentIso d).hom.app K).app (op d) ≫
          ((scalarTensor.obj (discreteYoneda.obj d)).obj K).map h := by
      exact congrArg
        (fun f : ((evaluationLeftAdjoint SSet.{u} (op d)).obj K).obj (op d) ⟶
            ((scalarTensor.obj (discreteYoneda.obj d)).obj K).obj e =>
          (show K ⟶ ((evaluationLeftAdjoint SSet.{u} (op d)).obj K).obj (op d) from
            Sigma.ι (fun _ : op d ⟶ op d => K) (𝟙 _)) ≫ f)
        (((freeComponentIso d).hom.app K).naturality h)
    _ = _ := by
      exact (Category.assoc
        (show K ⟶ ((evaluationLeftAdjoint SSet.{u} (op d)).obj K).obj (op d) from
          Sigma.ι (fun _ : op d ⟶ op d => K) (𝟙 _))
        (((freeComponentIso d).hom.app K).app (op d))
        (((scalarTensor.obj (discreteYoneda.obj d)).obj K).map h)).symm.trans
          (congrArg (fun f : K ⟶
              ((scalarTensor.obj (discreteYoneda.obj d)).obj K).obj (op d) =>
            f ≫ ((scalarTensor.obj (discreteYoneda.obj d)).obj K).map h) hu)

omit smallD in
/-- Every actual summand is the original shrink-Hom label paired with its scalar value. -/
private theorem freeComponentIso_value (d : D) (K : SSet.{u}) (e : Dᵒᵖ)
    (h : op d ⟶ e) (Δ : SimplexCategoryᵒᵖ) (k : K.obj Δ) :
    (((freeComponentIso d).hom.app K).app e).app Δ
        ((Sigma.ι (fun _ : op d ⟶ e => K) h).app Δ k) =
      ((discreteYonedaObjEquiv d e Δ).symm h.unop, k) := by
  have hs := congrArg (fun f : K ⟶
      ((scalarTensor.obj (discreteYoneda.obj d)).obj K).obj e => f.app Δ k)
    (freeComponentIso_summand d K e h)
  calc
    _ = (((scalarTensor.obj (discreteYoneda.obj d)).obj K).map h).app Δ
        (((discreteYonedaScalarAdjunction d).unit.app K).app Δ k) := hs
    _ = _ := by
      change (((discreteYoneda.obj d).map h).app Δ
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d)), k) = _
      apply Prod.ext
      · apply (discreteYonedaObjEquiv d e Δ).injective
        rw [discreteYoneda_obj_map]
        simp
      · rfl

/-- One whole original-index natural isomorphism to the representable scalar tensor. -/
def freeEvaluationScalarIso :
    freeEvaluationFunctor (D := D) ≅ discreteYoneda ⋙ scalarTensor :=
  NatIso.ofComponents (fun d =>
    (evaluationAdjunctionRight SSet.{u} (op d)).leftAdjointUniq
      (discreteYonedaScalarAdjunction d)) (by
    intro d d' θ
    apply NatTrans.ext
    funext K
    apply NatTrans.ext
    funext e
    apply Sigma.hom_ext
    intro h
    have hs := congrArg
      (fun f : K ⟶ ((evaluationLeftAdjoint SSet.{u} (op d')).obj K).obj e =>
        f ≫ ((freeComponentIso d').hom.app K).app e)
      (freeMap_summand θ K e h)
    calc
      _ = Sigma.ι (fun _ : op d' ⟶ e => K) (θ.op ≫ h) ≫
          ((freeComponentIso d').hom.app K).app e :=
        (Category.assoc
          (show K ⟶ ((evaluationLeftAdjoint SSet.{u} (op d)).obj K).obj e from
            Sigma.ι (fun _ : op d ⟶ e => K) h)
          (((freeEvaluationFunctor.map θ).app K).app e)
          (((freeComponentIso d').hom.app K).app e)).symm.trans hs
      _ = _ := by
        ext Δ k
        change (((freeComponentIso d').hom.app K).app e).app Δ
            ((Sigma.ι (fun _ : op d' ⟶ e => K) (θ.op ≫ h)).app Δ k) =
          (((scalarTensor.map (discreteYoneda.map θ)).app K).app e).app Δ
            ((((freeComponentIso d).hom.app K).app e).app Δ
              ((Sigma.ι (fun _ : op d ⟶ e => K) h).app Δ k))
        rw [freeComponentIso_value, freeComponentIso_value]
        change ((discreteYonedaObjEquiv d' e Δ).symm (θ.op ≫ h).unop, k) =
          ((((discreteYoneda.map θ).app e).app Δ
            ((discreteYonedaObjEquiv d e Δ).symm h.unop)), k)
        apply Prod.ext
        · apply (discreteYonedaObjEquiv d' e Δ).injective
          rw [discreteYoneda_map_app]
          simp
        · rfl)

omit smallD in
/-- The forward comparison retains every original Hom-indexed coproduct injection. -/
theorem freeEvaluationScalarIso_hom_ι (d : D) (K : SSet.{u}) (e : Dᵒᵖ)
    (h : op d ⟶ e) (Δ : SimplexCategoryᵒᵖ) (k : K.obj Δ) :
    (((freeEvaluationScalarIso.app d).hom.app K).app e).app Δ
        ((Sigma.ι (fun _ : op d ⟶ e => K) h).app Δ k) =
      ((discreteYonedaObjEquiv d e Δ).symm h.unop, k) :=
  freeComponentIso_value d K e h Δ k

omit smallD in
/-- The inverse comparison decodes the same original representing Hom and scalar value. -/
theorem freeEvaluationScalarIso_inv_value (d : D) (K : SSet.{u}) (e : Dᵒᵖ)
    (Δ : SimplexCategoryᵒᵖ) (x : ((discreteYoneda.obj d).obj e).obj Δ) (k : K.obj Δ) :
    (((freeEvaluationScalarIso.app d).inv.app K).app e).app Δ (x, k) =
      (Sigma.ι (fun _ : op d ⟶ e => K)
        (discreteYonedaObjEquiv d e Δ x).op).app Δ k := by
  let h : op d ⟶ e := (discreteYonedaObjEquiv d e Δ x).op
  have hv := freeEvaluationScalarIso_hom_ι d K e h Δ k
  have he : (discreteYonedaObjEquiv d e Δ).symm h.unop = x := by simp [h]
  rw [he] at hv
  have hi := congrArg (fun f : (evaluationLeftAdjoint SSet.{u} (op d)).obj K ⟶
      (evaluationLeftAdjoint SSet.{u} (op d)).obj K => (f.app e).app Δ
        ((Sigma.ι (fun _ : op d ⟶ e => K) h).app Δ k))
    ((freeEvaluationScalarIso.app d).app K).hom_inv_id
  change (((freeEvaluationScalarIso.app d).inv.app K).app e).app Δ
      ((((freeEvaluationScalarIso.app d).hom.app K).app e).app Δ
        ((Sigma.ι (fun _ : op d ⟶ e => K) h).app Δ k)) = _ at hi
  rw [hv] at hi
  exact hi

omit smallD in
/-- Both original adjunction units use this same comparison and its inverse. -/
theorem freeEvaluationScalarIso_unit (d : D) (K : SSet.{u}) :
    (evaluationAdjunctionRight SSet.{u} (op d)).unit.app K ≫
        ((evaluation Dᵒᵖ SSet.{u}).obj (op d)).map
          ((freeEvaluationScalarIso.app d).hom.app K) =
      (discreteYonedaScalarAdjunction d).unit.app K ∧
    (discreteYonedaScalarAdjunction d).unit.app K ≫
        ((evaluation Dᵒᵖ SSet.{u}).obj (op d)).map
          ((freeEvaluationScalarIso.app d).inv.app K) =
      (evaluationAdjunctionRight SSet.{u} (op d)).unit.app K := by
  refine ⟨?_, ?_⟩
  · exact (evaluationAdjunctionRight SSet.{u} (op d)).unit_leftAdjointUniq_hom_app
      (discreteYonedaScalarAdjunction d) K
  · change (discreteYonedaScalarAdjunction d).unit.app K ≫
      ((evaluation Dᵒᵖ SSet.{u}).obj (op d)).map
        (((evaluationAdjunctionRight SSet.{u} (op d)).leftAdjointUniq
          (discreteYonedaScalarAdjunction d)).inv.app K) = _
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact (discreteYonedaScalarAdjunction d).unit_leftAdjointUniq_hom_app
      (evaluationAdjunctionRight SSet.{u} (op d)) K

omit smallD in
/-- Both original adjunction counits retain the same forward and inverse comparisons. -/
theorem freeEvaluationScalarIso_counit (d : D) (Z : SimplicialPresheaf.{u} D) :
    (freeEvaluationScalarIso.app d).hom.app (Z.obj (op d)) ≫
        (discreteYonedaScalarAdjunction d).counit.app Z =
      (evaluationAdjunctionRight SSet.{u} (op d)).counit.app Z ∧
    (freeEvaluationScalarIso.app d).inv.app (Z.obj (op d)) ≫
        (evaluationAdjunctionRight SSet.{u} (op d)).counit.app Z =
      (discreteYonedaScalarAdjunction d).counit.app Z := by
  refine ⟨?_, ?_⟩
  · exact (evaluationAdjunctionRight SSet.{u} (op d)).leftAdjointUniq_hom_app_counit
      (discreteYonedaScalarAdjunction d) Z
  · change ((evaluationAdjunctionRight SSet.{u} (op d)).leftAdjointUniq
      (discreteYonedaScalarAdjunction d)).inv.app (Z.obj (op d)) ≫
        (evaluationAdjunctionRight SSet.{u} (op d)).counit.app Z = _
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact (discreteYonedaScalarAdjunction d).leftAdjointUniq_hom_app_counit
      (evaluationAdjunctionRight SSet.{u} (op d)) Z

/-- The comparison is an entire original Arrow isomorphism for every scalar map. -/
def freeScalarArrowIso (d : D) {K L : SSet.{u}} (j : K ⟶ L) :
    Arrow.mk ((freeEvaluationFunctor.obj d).map j) ≅
      Arrow.mk ((scalarTensor.obj (discreteYoneda.obj d)).map j) :=
  Arrow.isoMk ((freeEvaluationScalarIso.app d).app K)
    ((freeEvaluationScalarIso.app d).app L)
    ((freeEvaluationScalarIso.app d).hom.naturality j).symm

omit smallD in
/-- All four Arrow legs are the original comparison components, in both directions. -/
theorem freeScalarArrowIso_legs (d : D) {K L : SSet.{u}} (j : K ⟶ L) :
    (freeScalarArrowIso d j).hom.left = (freeEvaluationScalarIso.app d).hom.app K ∧
      (freeScalarArrowIso d j).hom.right = (freeEvaluationScalarIso.app d).hom.app L ∧
      (freeScalarArrowIso d j).inv.left = (freeEvaluationScalarIso.app d).inv.app K ∧
      (freeScalarArrowIso d j).inv.right = (freeEvaluationScalarIso.app d).inv.app L := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end SimplicialPresheaf
