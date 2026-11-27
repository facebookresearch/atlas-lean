/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ChainMap

open CategoryTheory Limits AlgebraicTopology

universe u v

namespace MathlibExtTest.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleChainMap

theorem shuffleBidegree_naturality_client
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    {X X₂ Y Y₂ : SimplicialObject C}
    (f : X ⟶ X₂) (g : Y ⟶ Y₂) (p q : ℕ) :
    AlgebraicTopology.EilenbergZilber.shuffleBidegree X Y p q ≫
      (MonoidalCategory.tensorHom f g).app
        (Opposite.op (SimplexCategory.mk (p + q))) =
      MonoidalCategory.tensorHom
        (f.app (Opposite.op (SimplexCategory.mk p)))
        (g.app (Opposite.op (SimplexCategory.mk q))) ≫
        AlgebraicTopology.EilenbergZilber.shuffleBidegree X₂ Y₂ p q :=
  AlgebraicTopology.EilenbergZilber.shuffleBidegree_naturality f g p q

theorem ιTensorObj_comp_shuffleComponent_client
    (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [(MonoidalCategory.curriedTensor C).Additive]
    [∀ Z : C, ((MonoidalCategory.curriedTensor C).obj Z).Additive]
    (X Y : SimplicialObject C)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n h ≫
      AlgebraicTopology.EilenbergZilber.shuffleComponent X Y n =
    AlgebraicTopology.EilenbergZilber.shuffleBidegree X Y p q ≫
      eqToHom (by rw [AlgebraicTopology.alternatingFaceMapComplex_obj_X, h]) :=
  AlgebraicTopology.EilenbergZilber.ιTensorObj_comp_shuffleComponent X Y p q n h

theorem shuffleComponent_comm_client
    (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [(MonoidalCategory.curriedTensor C).Additive]
    [∀ Z : C, ((MonoidalCategory.curriedTensor C).obj Z).Additive]
    (X Y : SimplicialObject C)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    (n : ℕ) :
    AlgebraicTopology.EilenbergZilber.shuffleComponent X Y (n + 1) ≫
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj
          (MonoidalCategory.tensorObj X Y)).d (n + 1) n =
      (HomologicalComplex.tensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).d (n + 1) n ≫
        AlgebraicTopology.EilenbergZilber.shuffleComponent X Y n :=
  AlgebraicTopology.EilenbergZilber.shuffleComponent_comm X Y n

theorem alternatingMap_naturality_client
    (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [(MonoidalCategory.curriedTensor C).Additive]
    [∀ Z : C, ((MonoidalCategory.curriedTensor C).obj Z).Additive]
    {X X₂ Y Y₂ : SimplicialObject C}
    (f : X ⟶ X₂) (g : Y ⟶ Y₂)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X₂)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y₂)] :
    HomologicalComplex.tensorHom
        ((AlgebraicTopology.alternatingFaceMapComplex C).map f)
        ((AlgebraicTopology.alternatingFaceMapComplex C).map g) ≫
      AlgebraicTopology.EilenbergZilber.alternatingMap X₂ Y₂ =
    AlgebraicTopology.EilenbergZilber.alternatingMap X Y ≫
      (AlgebraicTopology.alternatingFaceMapComplex C).map
        (MonoidalCategory.tensorHom f g) :=
  AlgebraicTopology.EilenbergZilber.alternatingMap_naturality f g

end MathlibExtTest.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleChainMap
