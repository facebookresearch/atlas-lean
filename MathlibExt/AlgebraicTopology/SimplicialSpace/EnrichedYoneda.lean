/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.PointwiseHom
public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps

import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Pointwise enriched Yoneda for simplicial spaces

The pointwise/end mapping simplicial set out of the discrete outer
representable `F[n]` is naturally isomorphic to outer level `n`. The forward
map is the end projection at `[n]` evaluated at the identity outer simplex.

This is a raw enriched-Yoneda calculation. It makes no Reedy, derived,
Segal, locality, weak-equivalence, or localization claim, and it does not
identify the pointwise mapping object with the canonical outer
`SimplicialCategory.sHom`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalCategory

namespace SSet.Rezk

private noncomputable abbrev pointwiseHom
    (X Y : SimplicialObject SSet.{u}) : SSet.{u} :=
  (SSet.simplicialSpacePointwiseHom.obj (op X)).obj Y

/-- The identity outer simplex as a point of the discrete representable in
outer degree `n`. -/
noncomputable def representableIdentityPoint (n : ℕ) :
    𝟙_ SSet.{u} ⟶ (representable.{u} n).obj (op ⦋n⦌) where
  app _ := ↾fun _ ↦ SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)
  naturality _ _ _ := rfl

private noncomputable def representablePoint (n : ℕ)
    (j : SimplexCategoryᵒᵖ) (σ : (Δ[n] : SSet.{u}).obj j) :
    𝟙_ SSet.{u} ⟶ (representable.{u} n).obj j where
  app _ := ↾fun _ ↦ σ
  naturality _ _ _ := rfl

private theorem representableIdentityPoint_map (n : ℕ)
    (j : SimplexCategoryᵒᵖ) (σ : (Δ[n] : SSet.{u}).obj j) :
    representableIdentityPoint.{u} n ≫
        (representable.{u} n).map (SSet.stdSimplex.objEquiv σ).op =
      representablePoint n j σ := by
  ext a x
  change SSet.stdSimplex.objEquiv.symm
    (SSet.stdSimplex.objEquiv σ ≫ 𝟙 ⦋n⦌) = σ
  rw [Category.comp_id, Equiv.symm_apply_apply]

private theorem representableIdentityPoint_index {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) :
    representableIdentityPoint.{u} m ≫
        (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map f)).app (op ⦋m⦌) =
      representableIdentityPoint.{u} n ≫
        (representable.{u} n).map f.op := by
  ext a x
  rfl

private noncomputable def internalHomEvaluateAt {A B : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ A) : (ihom A).obj B ⟶ B :=
  (λ_ _).inv ≫ p ▷ (ihom A).obj B ≫ (ihom.ev A).app B

private noncomputable def tensorPoint {A Y : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ A) : Y ⟶ A ⊗ Y :=
  (λ_ Y).inv ≫ p ▷ Y

private theorem tensorPoint_uncurry {A B Y : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ A) (q : Y ⟶ (ihom A).obj B) :
    tensorPoint p ≫ MonoidalClosed.uncurry q =
      q ≫ internalHomEvaluateAt p := by
  unfold tensorPoint internalHomEvaluateAt
  rw [MonoidalClosed.uncurry_eq,
    MonoidalCategory.leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc]
  simp only [Category.assoc]

private theorem representableTensorPoint_apply
    (n : ℕ) (j a : SimplexCategoryᵒᵖ)
    (σ : (Δ[n] : SSet.{u}).obj j) (Y : SSet.{u}) (y : Y.obj a) :
    (tensorPoint (representablePoint n j σ)).app a y = (σ, y) :=
  rfl

private theorem pointwiseHomπ_uncurry_apply
    (n : ℕ) (W : SimplicialObject SSet.{u})
    (j a : SimplexCategoryᵒᵖ)
    (σ : (Δ[n] : SSet.{u}).obj j)
    (h : (pointwiseHom (representable.{u} n) W).obj a) :
    (MonoidalClosed.uncurry
        (SSet.simplicialSpacePointwiseHomπ
          (representable.{u} n) W j)).app a (σ, h) =
      ((SSet.simplicialSpacePointwiseHomπ
        (representable.{u} n) W j ≫
        internalHomEvaluateAt (representablePoint n j σ)).app a) h := by
  have hc := tensorPoint_uncurry (representablePoint n j σ)
    (SSet.simplicialSpacePointwiseHomπ (representable.{u} n) W j)
  have hc_a := NatTrans.congr_app hc a
  have hc_h := ConcreteCategory.congr_hom hc_a h
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply,
    representableTensorPoint_apply] using hc_h

private theorem internalHomEvaluateAt_map {A B B' : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ A) (g : B ⟶ B') :
    (ihom A).map g ≫ internalHomEvaluateAt p =
      internalHomEvaluateAt p ≫ g := by
  unfold internalHomEvaluateAt
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc]
  simp only [Category.assoc]
  rw [ihom.ev_naturality]

private theorem internalHomEvaluateAt_pre {A B X : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ B) (f : B ⟶ A) :
    (pre f).app X ≫ internalHomEvaluateAt p =
      internalHomEvaluateAt (p ≫ f) := by
  unfold internalHomEvaluateAt
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc]
  rw [id_tensor_pre_app_comp_ev, comp_whiskerRight]
  simp only [Category.assoc]

private theorem pointwiseHomπ_evaluate_naturality
    (X Y : SimplicialObject SSet.{u}) {i j : SimplexCategoryᵒᵖ}
    (f : i ⟶ j) (p : 𝟙_ SSet.{u} ⟶ X.obj i) :
    SSet.simplicialSpacePointwiseHomπ X Y i ≫
        internalHomEvaluateAt p ≫ Y.map f =
      SSet.simplicialSpacePointwiseHomπ X Y j ≫
        internalHomEvaluateAt (p ≫ X.map f) := by
  calc
    _ = SSet.simplicialSpacePointwiseHomπ X Y i ≫
        (ihom (X.obj i)).map (Y.map f) ≫
          internalHomEvaluateAt p := by
      rw [internalHomEvaluateAt_map]
    _ = SSet.simplicialSpacePointwiseHomπ X Y j ≫
        (pre (X.map f)).app (Y.obj j) ≫
          internalHomEvaluateAt p := by
      rw [← Category.assoc,
        SSet.simplicialSpacePointwiseHomπ_outer, Category.assoc]
    _ = _ := by
      rw [internalHomEvaluateAt_pre]

private noncomputable def pointwiseYonedaEvaluation (n : ℕ)
    (W : SimplicialObject SSet.{u}) :
    pointwiseHom (representable.{u} n) W ⟶ W.obj (op ⦋n⦌) :=
  SSet.simplicialSpacePointwiseHomπ
      (representable.{u} n) W (op ⦋n⦌) ≫
    internalHomEvaluateAt (representableIdentityPoint.{u} n)

private noncomputable def pointwiseYonedaComponent (n : ℕ)
    (W : SimplicialObject SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    (representable.{u} n).obj j ⊗ W.obj (op ⦋n⦌) ⟶ W.obj j where
  app a := ↾fun z ↦
    (W.map (SSet.stdSimplex.objEquiv z.1).op).app a z.2
  naturality a b f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, x⟩
    exact ConcreteCategory.congr_hom
      ((W.map (SSet.stdSimplex.objEquiv σ).op).naturality f) x

private theorem pointwiseYonedaComponent_apply
    (n : ℕ) (W : SimplicialObject SSet.{u})
    (j a : SimplexCategoryᵒᵖ) {Z : SSet.{u}}
    (q : Z ⟶ W.obj (op ⦋n⦌))
    (σ : (Δ[n] : SSet.{u}).obj j) (z : Z.obj a) :
    (((representable.{u} n).obj j ◁ q ≫
        pointwiseYonedaComponent n W j).app a) (σ, z) =
      ((q ≫ W.map (SSet.stdSimplex.objEquiv σ).op).app a) z :=
  rfl

private noncomputable def pointwiseYonedaCurriedComponent (n : ℕ)
    (W : SimplicialObject SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    W.obj (op ⦋n⦌) ⟶
      (ihom ((representable.{u} n).obj j)).obj (W.obj j) :=
  MonoidalClosed.curry (pointwiseYonedaComponent n W j)

private theorem pointwiseYonedaCurriedComponent_condition (n : ℕ)
    (W : SimplicialObject SSet.{u}) {i j : SimplexCategoryᵒᵖ}
    (f : i ⟶ j) :
    pointwiseYonedaCurriedComponent n W i ≫
        (ihom ((representable.{u} n).obj i)).map (W.map f) =
      pointwiseYonedaCurriedComponent n W j ≫
        (pre ((representable.{u} n).map f)).app (W.obj j) := by
  unfold pointwiseYonedaCurriedComponent
  rw [← MonoidalClosed.curry_natural_right,
    MonoidalClosed.curry_pre_app]
  congr 1
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, x⟩
  change (W.map (SSet.stdSimplex.objEquiv σ).op ≫ W.map f).app a x = _
  rw [← W.map_comp]
  rfl

private noncomputable def pointwiseYonedaCoevaluation (n : ℕ)
    (W : SimplicialObject SSet.{u}) :
    W.obj (op ⦋n⦌) ⟶ pointwiseHom (representable.{u} n) W := by
  letI : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  letI : ∀ (A B : SimplicialObject SSet.{u}),
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} A B :=
    inferInstance
  change W.obj (op ⦋n⦌) ⟶
    Enriched.FunctorCategory.enrichedHom SSet.{u}
      (representable.{u} n) W
  exact end_.lift
    (fun j ↦ pointwiseYonedaCurriedComponent n W j)
    (fun i j f ↦ by
      rw [Enriched.FunctorCategory.diagram_obj_map,
        Enriched.FunctorCategory.diagram_map_app,
        MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      exact pointwiseYonedaCurriedComponent_condition n W f)

private theorem pointwiseYonedaCoevaluation_π (n : ℕ)
    (W : SimplicialObject SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    pointwiseYonedaCoevaluation n W ≫
        SSet.simplicialSpacePointwiseHomπ
          (representable.{u} n) W j =
      pointwiseYonedaCurriedComponent n W j := by
  unfold pointwiseYonedaCoevaluation
    SSet.simplicialSpacePointwiseHomπ
  change end_.lift _ _ ≫ end_.π _ j = _
  apply end_.lift_π

private theorem pointwiseYonedaCoevaluation_evaluation (n : ℕ)
    (W : SimplicialObject SSet.{u}) :
    pointwiseYonedaCoevaluation n W ≫
        pointwiseYonedaEvaluation n W =
      𝟙 (W.obj (op ⦋n⦌)) := by
  unfold pointwiseYonedaEvaluation
  rw [← Category.assoc, pointwiseYonedaCoevaluation_π]
  unfold pointwiseYonedaCurriedComponent internalHomEvaluateAt
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro x
  simp only [Functor.whiskeringRight_obj_obj, Functor.comp_obj,
    NatTrans.comp_app, Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj,
    Monoidal.leftUnitor_inv_app, Functor.const_obj_obj,
    Monoidal.whiskerRight_app, ConcreteCategory.comp_apply,
    NatTrans.id_app, id_apply]
  change (W.map (𝟙 (op ⦋n⦌))).app a x = x
  simp

private theorem pointwiseYonedaEvaluation_coevaluation (n : ℕ)
    (W : SimplicialObject SSet.{u}) :
    pointwiseYonedaEvaluation n W ≫
        pointwiseYonedaCoevaluation n W =
      𝟙 (pointwiseHom (representable.{u} n) W) := by
  apply SSet.simplicialSpacePointwiseHom_hom_ext
  intro j
  rw [Category.assoc, pointwiseYonedaCoevaluation_π, Category.id_comp]
  unfold pointwiseYonedaCurriedComponent
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, h⟩
  let f : op ⦋n⦌ ⟶ j := (SSet.stdSimplex.objEquiv σ).op
  have he := pointwiseHomπ_evaluate_naturality
    (representable.{u} n) W f (representableIdentityPoint.{u} n)
  have he_a := NatTrans.congr_app he a
  have he_h := ConcreteCategory.congr_hom he_a h
  rw [pointwiseYonedaComponent_apply,
    pointwiseHomπ_uncurry_apply]
  rw [← representableIdentityPoint_map n j σ]
  exact he_h

/-- The pointwise enriched-Yoneda isomorphism for the discrete outer
representable. -/
@[no_expose]
noncomputable def pointwiseYonedaIso (n : ℕ)
    (W : SimplicialObject SSet.{u}) :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{u} n))).obj W) ≅ W.obj (op ⦋n⦌) where
  hom := pointwiseYonedaEvaluation n W
  inv := pointwiseYonedaCoevaluation n W
  hom_inv_id := pointwiseYonedaEvaluation_coevaluation n W
  inv_hom_id := pointwiseYonedaCoevaluation_evaluation n W

/-- The forward Yoneda map is the selected end projection in degree `n`,
evaluated at the identity outer simplex. -/
theorem pointwiseYonedaIso_hom_projection (n : ℕ)
    (W : SimplicialObject SSet.{u}) :
    (pointwiseYonedaIso n W).hom =
      SSet.simplicialSpacePointwiseHomπ
          (representable.{u} n) W (op ⦋n⦌) ≫
        (λ_ _).inv ≫
        representableIdentityPoint.{u} n ▷
          (ihom ((representable.{u} n).obj (op ⦋n⦌))).obj
            (W.obj (op ⦋n⦌)) ≫
        (ihom.ev ((representable.{u} n).obj (op ⦋n⦌))).app
          (W.obj (op ⦋n⦌)) := by
  unfold pointwiseYonedaIso pointwiseYonedaEvaluation
    internalHomEvaluateAt
  rfl

/-- Naturality of pointwise enriched Yoneda in the target simplicial space. -/
theorem pointwiseYonedaIso_naturality_target (n : ℕ)
    {W W' : SimplicialObject SSet.{u}} (q : W ⟶ W') :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{u} n))).map q) ≫
        (pointwiseYonedaIso n W').hom =
      (pointwiseYonedaIso n W).hom ≫ q.app (op ⦋n⦌) := by
  unfold pointwiseYonedaIso pointwiseYonedaEvaluation
  rw [← Category.assoc,
    SSet.simplicialSpacePointwiseHomπ_map_target]
  rw [Category.assoc, internalHomEvaluateAt_map]
  simp only [Category.assoc]

/-- Contravariant naturality along a map of representable outer simplexes. -/
theorem pointwiseYonedaIso_naturality_index {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (W : SimplicialObject SSet.{u}) :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map f)))).app W) ≫
        (pointwiseYonedaIso m W).hom =
      (pointwiseYonedaIso n W).hom ≫ W.map f.op := by
  unfold pointwiseYonedaIso pointwiseYonedaEvaluation
  rw [← Category.assoc,
    SSet.simplicialSpacePointwiseHomπ_map_source]
  rw [Category.assoc, internalHomEvaluateAt_pre]
  rw [representableIdentityPoint_index f]
  symm
  exact pointwiseHomπ_evaluate_naturality
    (representable.{u} n) W f.op (representableIdentityPoint.{u} n)

/-- Under pointwise enriched Yoneda, restriction to a consecutive outer edge
is the corresponding outer structure map. -/
theorem pointwiseYonedaIso_consecutiveEdge (n : ℕ) (i : Fin n)
    (W : SimplicialObject SSet.{u}) :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i))))).app W) ≫
        (pointwiseYonedaIso 1 W).hom =
      (pointwiseYonedaIso n W).hom ≫
        W.map (SimplexCategory.mkOfSucc i).op :=
  pointwiseYonedaIso_naturality_index (SimplexCategory.mkOfSucc i) W

end SSet.Rezk

end
