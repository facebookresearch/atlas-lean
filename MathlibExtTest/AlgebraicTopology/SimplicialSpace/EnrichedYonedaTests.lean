/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.EnrichedYoneda

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.Rezk.EnrichedYonedaTests

section PointwiseHom

variable (X Y : SimplicialObject SSet.{u})
variable (j : SimplexCategoryᵒᵖ)

example : (SimplicialObject SSet.{u})ᵒᵖ ⥤
    SimplicialObject SSet.{u} ⥤ SSet.{u} :=
  SSet.simplicialSpacePointwiseHom

example : ((SSet.simplicialSpacePointwiseHom.obj (op X)).obj Y) ⟶
    (ihom (X.obj j)).obj (Y.obj j) :=
  SSet.simplicialSpacePointwiseHomπ X Y j

example {i : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    SSet.simplicialSpacePointwiseHomπ X Y i ≫
        (ihom (X.obj i)).map (Y.map f) =
      SSet.simplicialSpacePointwiseHomπ X Y j ≫
        (pre (X.map f)).app (Y.obj j) :=
  SSet.simplicialSpacePointwiseHomπ_outer X Y f

example {Z : SSet.{u}}
    {f g : Z ⟶ (SSet.simplicialSpacePointwiseHom.obj (op X)).obj Y}
    (h : ∀ a, f ≫ SSet.simplicialSpacePointwiseHomπ X Y a =
      g ≫ SSet.simplicialSpacePointwiseHomπ X Y a) : f = g :=
  SSet.simplicialSpacePointwiseHom_hom_ext X Y h

example {X' : SimplicialObject SSet.{u}} (g : X' ⟶ X) :
    ((SSet.simplicialSpacePointwiseHom.map (op g)).app Y) ≫
        SSet.simplicialSpacePointwiseHomπ X' Y j =
      SSet.simplicialSpacePointwiseHomπ X Y j ≫
        (pre (g.app j)).app (Y.obj j) :=
  SSet.simplicialSpacePointwiseHomπ_map_source g Y j

example {Y' : SimplicialObject SSet.{u}} (q : Y ⟶ Y') :
    ((SSet.simplicialSpacePointwiseHom.obj (op X)).map q) ≫
        SSet.simplicialSpacePointwiseHomπ X Y' j =
      SSet.simplicialSpacePointwiseHomπ X Y j ≫
        (ihom (X.obj j)).map (q.app j) :=
  SSet.simplicialSpacePointwiseHomπ_map_target X q j

end PointwiseHom

section Yoneda

variable (W : SimplicialObject SSet.{u})

example (n : ℕ) :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{u} n))).obj W) ≅ W.obj (op ⦋n⦌) :=
  pointwiseYonedaIso n W

example :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{u} 0))).obj W) ≅ W.obj (op ⦋0⦌) :=
  pointwiseYonedaIso 0 W

example :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{u} 1))).obj W) ≅ W.obj (op ⦋1⦌) :=
  pointwiseYonedaIso 1 W

example :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{u} 2))).obj W) ≅ W.obj (op ⦋2⦌) :=
  pointwiseYonedaIso 2 W

example (n : ℕ) :
    (pointwiseYonedaIso n W).hom ≫ (pointwiseYonedaIso n W).inv =
      𝟙 _ :=
  (pointwiseYonedaIso n W).hom_inv_id

example (n : ℕ) :
    (pointwiseYonedaIso n W).inv ≫ (pointwiseYonedaIso n W).hom =
      𝟙 _ :=
  (pointwiseYonedaIso n W).inv_hom_id

example (n : ℕ) :
    (pointwiseYonedaIso n W).hom =
      SSet.simplicialSpacePointwiseHomπ
          (representable.{u} n) W (op ⦋n⦌) ≫
        (λ_ _).inv ≫
        representableIdentityPoint.{u} n ▷
          (ihom ((representable.{u} n).obj (op ⦋n⦌))).obj
            (W.obj (op ⦋n⦌)) ≫
        (ihom.ev ((representable.{u} n).obj (op ⦋n⦌))).app
          (W.obj (op ⦋n⦌)) :=
  pointwiseYonedaIso_hom_projection n W

example (n : ℕ) {W' : SimplicialObject SSet.{u}} (q : W ⟶ W') :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{u} n))).map q) ≫
        (pointwiseYonedaIso n W').hom =
      (pointwiseYonedaIso n W).hom ≫ q.app (op ⦋n⦌) :=
  pointwiseYonedaIso_naturality_target n q

example {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map f)))).app W) ≫
        (pointwiseYonedaIso m W).hom =
      (pointwiseYonedaIso n W).hom ≫ W.map f.op :=
  pointwiseYonedaIso_naturality_index f W

example :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map (𝟙 ⦋2⦌))))).app W) ≫
        (pointwiseYonedaIso 2 W).hom =
      (pointwiseYonedaIso 2 W).hom ≫ W.map (𝟙 ⦋2⦌).op :=
  pointwiseYonedaIso_naturality_index (𝟙 ⦋2⦌) W

example :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map
            (SimplexCategory.δ (0 : Fin 2)))))).app W) ≫
        (pointwiseYonedaIso 0 W).hom =
      (pointwiseYonedaIso 1 W).hom ≫
        W.map (SimplexCategory.δ (0 : Fin 2)).op :=
  pointwiseYonedaIso_naturality_index
    (SimplexCategory.δ (0 : Fin 2)) W

example :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map
            (SimplexCategory.σ (0 : Fin 1)))))).app W) ≫
        (pointwiseYonedaIso 1 W).hom =
      (pointwiseYonedaIso 0 W).hom ≫
        W.map (SimplexCategory.σ (0 : Fin 1)).op :=
  pointwiseYonedaIso_naturality_index
    (SimplexCategory.σ (0 : Fin 1)) W

example (i : Fin 2) :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map
            (SimplexCategory.mkOfSucc i))))).app W) ≫
        (pointwiseYonedaIso 1 W).hom =
      (pointwiseYonedaIso 2 W).hom ≫
        W.map (SimplexCategory.mkOfSucc i).op :=
  pointwiseYonedaIso_consecutiveEdge 2 i W

example :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map
            (SimplexCategory.mkOfSucc (0 : Fin 2)))))).app W) ≫
        (pointwiseYonedaIso 1 W).hom =
      (pointwiseYonedaIso 2 W).hom ≫
        W.map (SimplexCategory.mkOfSucc (0 : Fin 2)).op :=
  pointwiseYonedaIso_consecutiveEdge 2 0 W

example :
    ((SSet.simplicialSpacePointwiseHom.map
        (op (SSet.simplicialSpaceDiscrete.map
          (SSet.stdSimplex.map
            (SimplexCategory.mkOfSucc (1 : Fin 2)))))).app W) ≫
        (pointwiseYonedaIso 1 W).hom =
      (pointwiseYonedaIso 2 W).hom ≫
        W.map (SimplexCategory.mkOfSucc (1 : Fin 2)).op :=
  pointwiseYonedaIso_consecutiveEdge 2 1 W

end Yoneda

section Universes

example (W : SimplicialObject SSet.{1}) :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{1} 2))).obj W) ≅ W.obj (op ⦋2⦌) :=
  pointwiseYonedaIso 2 W

example (W : SimplicialObject SSet.{0}) :
    ((SSet.simplicialSpacePointwiseHom.obj
      (op (representable.{0} 2))).obj W) ≅ W.obj (op ⦋2⦌) :=
  pointwiseYonedaIso 2 W

end Universes

section OuterVsInner

example (X Y : SimplicialObject SSet.{u}) :
    CategoryTheory.SimplicialCategory.sHom X Y =
      CategoryTheory.Functor.functorHom X Y :=
  rfl

example (K : SSet.{u}) (X : SimplicialObject SSet.{u})
    (n a : SimplexCategoryᵒᵖ) :
    (((SSet.simplicialSpaceTensor.obj K).obj X).obj n).obj a =
      (K.obj n × (X.obj n).obj a) :=
  SSet.simplicialSpaceTensor_obj_obj K X n a

example : True := by
  fail_if_success
    let _ : MonoidalClosed (SimplicialObject SSet.{u}) := inferInstance
  fail_if_success
    let _ := SSet.Rezk.pointwiseYonedaCoevaluation
  fail_if_success
    let _ := SSet.Rezk.mappingOutOfSpineIso
  fail_if_success
    let _ := SSet.Rezk.pointwiseYonedaDerivedIso
  fail_if_success
    let _ := SSet.Rezk.pointwiseYonedaWeakEquivalence
  fail_if_success
    let _ := SSet.Rezk.pointwiseYonedaLocalObject
  fail_if_success
    let _ := SSet.Rezk.pointwiseYonedaLocalization
  trivial

end OuterVsInner

#check SSet.simplicialSpacePointwiseHom
#check SSet.simplicialSpacePointwiseHomπ
#check SSet.simplicialSpacePointwiseHomπ_outer
#check SSet.simplicialSpacePointwiseHom_hom_ext
#check SSet.simplicialSpacePointwiseHomπ_map_source
#check SSet.simplicialSpacePointwiseHomπ_map_target
#check representableIdentityPoint
#check pointwiseYonedaIso
#check pointwiseYonedaIso_hom_projection
#check pointwiseYonedaIso_naturality_target
#check pointwiseYonedaIso_naturality_index
#check pointwiseYonedaIso_consecutiveEdge

#print axioms SSet.simplicialSpacePointwiseHom
#print axioms SSet.simplicialSpacePointwiseHomπ
#print axioms SSet.simplicialSpacePointwiseHomπ_outer
#print axioms SSet.simplicialSpacePointwiseHom_hom_ext
#print axioms SSet.simplicialSpacePointwiseHomπ_map_source
#print axioms SSet.simplicialSpacePointwiseHomπ_map_target
#print axioms representableIdentityPoint
#print axioms pointwiseYonedaIso
#print axioms pointwiseYonedaIso_hom_projection
#print axioms pointwiseYonedaIso_naturality_target
#print axioms pointwiseYonedaIso_naturality_index
#print axioms pointwiseYonedaIso_consecutiveEdge

end SSet.Rezk.EnrichedYonedaTests

end
