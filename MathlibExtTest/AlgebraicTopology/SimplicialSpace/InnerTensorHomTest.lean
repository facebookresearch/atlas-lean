/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerTensorHom

/-! # Public inner tensor–mapping comparison clients -/

@[expose] public section


set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial SimplicialSpace.Inner
namespace SimplicialSpace

-- Both inverse identities are whole maps, for arbitrary original objects.
example (K : SSet.{u}) (X Z : SimplicialSpace.{u}) :
    (innerTensorHomIso K X).hom.app Z ≫ (innerTensorHomIso K X).inv.app Z = 𝟙 _ :=
  (innerTensorHomIso K X).hom_inv_id_app Z

example (K : SSet.{u}) (X Z : SimplicialSpace.{u}) :
    (innerTensorHomIso K X).inv.app Z ≫ (innerTensorHomIso K X).hom.app Z = 𝟙 _ :=
  (innerTensorHomIso K X).inv_hom_id_app Z

example {K L : SSet.{u}} (k : K ⟶ L) (X Z : SimplicialSpace.{u}) :
    (innerHomFunctor.map ((innerTensorBifunctor.obj X).map k).op).app Z ≫
        (innerTensorHomIso K X).hom.app Z =
      (innerTensorHomIso L X).hom.app Z ≫
        (pre k).app ((innerHomFunctor.obj (op X)).obj Z) :=
  innerTensorHomIso_naturality_scalar k X Z

example (K : SSet.{u}) {X Y : SimplicialSpace.{u}} (x : X ⟶ Y)
    (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.map ((innerTensor K).map x).op).app Z ≫
        (innerTensorHomIso K X).hom.app Z =
      (innerTensorHomIso K Y).hom.app Z ≫
        (ihom K).map ((innerHomFunctor.map x.op).app Z) :=
  innerTensorHomIso_naturality_source K x Z

example (K : SSet.{u}) (X : SimplicialSpace.{u})
    {Z Z' : SimplicialSpace.{u}} (z : Z ⟶ Z') :
    (innerHomFunctor.obj (op ((innerTensor K).obj X))).map z ≫
        (innerTensorHomIso K X).hom.app Z' =
      (innerTensorHomIso K X).hom.app Z ≫
        (ihom K).map ((innerHomFunctor.obj (op X)).map z) :=
  (innerTensorHomIso K X).hom.naturality z

-- The empty scalar is the actual chosen initial simplicial set.
example (X Z : SimplicialSpace.{u}) :
    (innerTensorHomIso (⊥_ SSet.{u}) X).hom.app Z ≫
        (innerTensorHomIso (⊥_ SSet.{u}) X).inv.app Z = 𝟙 _ :=
  (innerTensorHomIso (⊥_ SSet.{u}) X).hom_inv_id_app Z

-- The original inner degree-zero functions retain both inverse equations.
example (K : SSet.{u}) (X Z : SimplicialSpace.{u})
    (b : (innerHomFunctor.obj (op ((innerTensor K).obj X))).obj Z _⦋0⦌) :
    ((innerTensorHomIso K X).inv.app Z).app (op (SimplexCategory.mk 0))
      (((innerTensorHomIso K X).hom.app Z).app (op (SimplexCategory.mk 0)) b) = b := by
  have h := congrArg (fun f => f.app (op (SimplexCategory.mk 0)) b)
    ((innerTensorHomIso K X).hom_inv_id_app Z)
  exact h

example (K : SSet.{u}) (X Z : SimplicialSpace.{u})
    (b : ((ihom K).obj ((innerHomFunctor.obj (op X)).obj Z)) _⦋0⦌) :
    ((innerTensorHomIso K X).hom.app Z).app (op (SimplexCategory.mk 0))
      (((innerTensorHomIso K X).inv.app Z).app (op (SimplexCategory.mk 0)) b) = b := by
  have h := congrArg (fun f => f.app (op (SimplexCategory.mk 0)) b)
    ((innerTensorHomIso K X).inv_hom_id_app Z)
  exact h

end SimplicialSpace
