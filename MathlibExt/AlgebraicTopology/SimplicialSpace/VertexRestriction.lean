/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.EnrichedYoneda
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Vertex coproducts and original inner restrictions

The constant finite vertex object and its literal simplex inclusions give the
original inner mapping comparison with the product of zero levels. Restriction
fibrations use the named Reedy and Kan models.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace

/-- The mapping functor restricts the actual inner enrichment to discrete outer sources. -/
def discreteSourceMapping (W : SimplicialSpace.{u}) : SSet.{u}ᵒᵖ ⥤ SSet.{u} :=
  (SSet.simplicialSpaceDiscrete ⋙ ofSimplicialObject).op ⋙ innerHomFunctor.flip.obj W

/-- Actual inner mapping out of a discrete representable is its original outer level. -/
def discreteYonedaIso (W : SimplicialSpace.{u}) (n : ℕ) :
    (discreteSourceMapping W).obj (op (Δ[n] : SSet.{u})) ≅ W.diagram.obj (op ⦋n⦌) :=
  SSet.Rezk.pointwiseYonedaIso n W.diagram

/-- The representable comparison retains every original face and degeneracy. -/
theorem discreteYonedaIso_naturality_index (W : SimplicialSpace.{u}) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) :
    (discreteSourceMapping W).map (SSet.stdSimplex.map f).op ≫
        (discreteYonedaIso W m).hom =
      (discreteYonedaIso W n).hom ≫ W.diagram.map f.op :=
  SSet.Rezk.pointwiseYonedaIso_naturality_index f W.diagram

namespace VertexRestriction

/-- The constant simplicial set of the original vertices, in the same universe. -/
abbrev vertexObject (k : ℕ) : SSet.{u} :=
  (SimplicialObject.const (Type u)).obj (ULift.{u} (Fin (k + 1)))

private def zeroSimplex (m : SimplexCategoryᵒᵖ) : (Δ[0] : SSet.{u}).obj m :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.const m.unop ⦋0⦌ 0)

/-- The literal coproduct injection of one original vertex from Δ[0]. -/
def vertexInjection (k : ℕ) (i : Fin (k + 1)) :
    (Δ[0] : SSet.{u}) ⟶ vertexObject k where
  app _ := ↾fun _ => ULift.up i
  naturality _ _ _ := rfl

/-- The original vertices included as constant simplices of Δ[k]. -/
def vertexInclusion (k : ℕ) : vertexObject.{u} k ⟶ (Δ[k] : SSet.{u}) where
  app m := ↾fun x => SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.const m.unop ⦋k⦌ x.down)
  naturality m m' f := by
    ext x
    apply SSet.stdSimplex.objEquiv.injective
    ext j
    rfl

/-- The constant-simplex vertex inclusion is injective at every simplicial level. -/
theorem vertexInclusion_mono (k : ℕ) : Mono (vertexInclusion.{u} k) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  apply (CategoryTheory.mono_iff_injective ((vertexInclusion.{u} k).app m)).mpr
  intro a b h
  apply ULift.ext
  have h0 := congrArg (fun t : (Δ[k] : SSet.{u}).obj m =>
    (SSet.stdSimplex.objEquiv t).toOrderHom (0 : Fin (m.unop.len + 1))) h
  change a.down = b.down at h0
  exact h0

/-- Each coproduct injection is the corresponding original simplex vertex map. -/
theorem vertexInjection_inclusion (k : ℕ) (i : Fin (k + 1)) :
    vertexInjection.{u} k i ≫ vertexInclusion k =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i) := by
  ext m x
  apply SSet.stdSimplex.objEquiv.injective
  ext j
  rfl

private def vertexCofan (k : ℕ) : Cofan (fun _ : Fin (k + 1) => (Δ[0] : SSet.{u})) :=
  Cofan.mk (vertexObject k) (vertexInjection k)

private def vertexCofanDesc (k : ℕ)
    (c : Cofan (fun _ : Fin (k + 1) => (Δ[0] : SSet.{u}))) :
    vertexObject k ⟶ c.pt where
  app m := ↾fun x => (c.inj x.down).app m (zeroSimplex m)
  naturality m m' f := by
    ext x
    change (c.inj x.down).app m' (zeroSimplex m') =
      c.pt.map f ((c.inj x.down).app m (zeroSimplex m))
    have h := types_congr_hom ((c.inj x.down).naturality f) (zeroSimplex m)
    have hp : (Δ[0] : SSet.{u}).map f (zeroSimplex m) = zeroSimplex m' := by
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      exact DFunLike.ext _ _ (fun _ => (Subsingleton.elim _ _ : (_ : Fin 1) = _))
    simpa only [types_comp_apply, hp] using h

/-- The original vertex injections form a colimiting finite coproduct cocone. -/
def vertexCofanIsColimit (k : ℕ) :
    IsColimit (Cofan.mk (vertexObject.{u} k) (vertexInjection k)) := by
  change IsColimit (vertexCofan.{u} k)
  refine Cofan.IsColimit.mk _ (vertexCofanDesc k) ?_ ?_
  · intro c i
    ext m x
    have hx : x = zeroSimplex m := by
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      exact DFunLike.ext _ _ (fun _ => (Subsingleton.elim _ _ : (_ : Fin 1) = _))
    subst x
    rfl
  · intro c f h
    ext m x
    change f.app m x = (c.inj x.down).app m (zeroSimplex m)
    have hm := types_congr_hom
      (congrArg (fun t => t.app m) (h x.down)) (zeroSimplex m)
    change f.app m x = (c.inj x.down).app m (zeroSimplex m) at hm
    exact hm

private theorem discretePreservesFiniteCoproducts :
    PreservesFiniteCoproducts SSet.simplicialSpaceDiscrete.{u} where
  preserves n := ⟨fun {K} => ⟨fun c {hc} => ⟨by
    apply evaluationJointlyReflectsColimits _ (fun k => ?_)
    change IsColimit
      ((((evaluation _ _).obj k ⋙ SimplicialObject.const (Type u)).mapCocone c))
    exact isColimitOfPreserves _ hc⟩⟩⟩

private theorem flipInnerPreservesFiniteProducts (W : SimplicialSpace.{u}) :
    PreservesFiniteProducts (innerHomFunctor.flip.obj W) where
  preserves n := by
    letI : PreservesColimitsOfShape (Discrete (Fin n))ᵒᵖ
        (innerHomFunctor.flip.obj W).rightOp :=
      innerHom_rightOp_preservesColimitsOfShape (Discrete (Fin n))ᵒᵖ W
    exact preservesLimitsOfShape_of_rightOp (J := Discrete (Fin n))
      (innerHomFunctor.flip.obj W)

private def vertexMappingFanIsLimit (W : SimplicialSpace.{u}) (k : ℕ) :
    IsLimit (Fan.mk ((discreteSourceMapping W).obj (op (vertexObject k)))
      (fun i : Fin (k + 1) =>
        (discreteSourceMapping W).map (vertexInjection k i).op)) := by
  let T := SSet.simplicialSpaceDiscrete.{u} ⋙ ofSimplicialObject
  let H := innerHomFunctor.flip.obj W
  letI : PreservesFiniteCoproducts SSet.simplicialSpaceDiscrete.{u} :=
    discretePreservesFiniteCoproducts
  letI : PreservesFiniteCoproducts T := by dsimp [T]; infer_instance
  letI : PreservesFiniteProducts H := flipInnerPreservesFiniteProducts W
  let hT := isColimitCofanMkObjOfIsColimit T
    (fun _ : Fin (k + 1) => (Δ[0] : SSet.{u})) (vertexInjection k)
    (vertexCofanIsColimit k)
  let hOpp := Cofan.IsColimit.op hT
  let hMap := isLimitOfPreserves H hOpp
  exact (isLimitMapConeFanMkEquiv H
    (fun _ : Fin (k + 1) => op (T.obj (Δ[0] : SSet.{u})))
    (fun i => (T.map (vertexInjection k i)).op)).toFun hMap

private def vertexMappingFirstIso (W : SimplicialSpace.{u}) (k : ℕ) :
    (discreteSourceMapping W).obj (op (vertexObject k)) ≅
      ∏ᶜ (fun _ : Fin (k + 1) => (discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) where
  hom := CategoryTheory.Limits.Pi.lift (fun i => (discreteSourceMapping W).map (vertexInjection k i).op)
  inv := (vertexMappingFanIsLimit W k).lift
    (Fan.mk _ (fun i => CategoryTheory.Limits.Pi.π _ i))
  hom_inv_id := by
    apply (vertexMappingFanIsLimit W k).hom_ext
    rintro ⟨i⟩
    rw [Category.assoc, IsLimit.fac]
    change (CategoryTheory.Limits.Pi.lift
      (fun i => (discreteSourceMapping W).map (vertexInjection k i).op)) ≫
      CategoryTheory.Limits.Pi.π _ i = _
    exact CategoryTheory.Limits.Pi.lift_comp_π _ _
  inv_hom_id := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro i
    rw [Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π]
    exact (vertexMappingFanIsLimit W k).fac
      (Fan.mk _ (fun i => CategoryTheory.Limits.Pi.π _ i)) ⟨i⟩

/-- Inner mapping out of the vertex coproduct is the product of the original zero levels. -/
def vertexMappingIso (W : SimplicialSpace.{u}) (k : ℕ) :
    (discreteSourceMapping W).obj (op (vertexObject k)) ≅
      ∏ᶜ (fun _ : Fin (k + 1) => W.diagram _⦋0⦌) :=
  vertexMappingFirstIso W k ≪≫ CategoryTheory.Limits.Pi.mapIso (fun _ => discreteYonedaIso W 0)

/-- Each product projection is the original vertex restriction followed by enriched Yoneda. -/
theorem vertexMappingIso_leg (W : SimplicialSpace.{u}) (k : ℕ)
    (i : Fin (k + 1)) :
    (vertexMappingIso W k).hom ≫ CategoryTheory.Limits.Pi.π _ i =
      (discreteSourceMapping W).map (vertexInjection k i).op ≫
        (discreteYonedaIso W 0).hom := by
  simp only [vertexMappingIso, Iso.trans_hom, Category.assoc,
    CategoryTheory.Limits.Pi.mapIso_hom_π, vertexMappingFirstIso]
  rw [← Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π]

/-- Restriction along a mono into a Reedy-fibrant space is a Kan fibration. -/
theorem discreteRestriction_fibration {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (W : SimplicialSpace.{u}) (hW : IsFibrant W) :
    Fibration ((discreteSourceMapping W).map i.op) := by
  letI : Mono (SSet.simplicialSpaceDiscrete.map i) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [NatTrans.mono_iff_mono_app]
    intro j
    change Mono (i.app m)
    infer_instance
  let f := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)
  letI : Mono f := by dsimp [f]; infer_instance
  letI : Cofibration f := (ReedyModel.cofibration_iff f).mpr inferInstance
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (ReedyModel.inner_precomp_fibration f W
      ((HomotopicalAlgebra.cofibration_iff f).mp inferInstance) hW)

end VertexRestriction

end SimplicialSpace
