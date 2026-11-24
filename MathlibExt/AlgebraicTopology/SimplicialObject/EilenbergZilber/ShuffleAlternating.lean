/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Simplicial

open scoped Simplicial

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ Z : C, ((curriedTensor C).obj Z).Additive]

noncomputable def shuffleComponent (X Y : SimplicialObject C)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)] (n : ℕ) :
    (HomologicalComplex.tensorObj
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).X n ⟶
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y)).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h =>
    have h' : p + q = n := h
    shuffleBidegree X Y p q ≫
      eqToHom (by
        rw [AlgebraicTopology.alternatingFaceMapComplex_obj_X, h'])

@[reassoc (attr := simp)]
theorem ιTensorObj_comp_shuffleComponent (X Y : SimplicialObject C)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n h ≫
      shuffleComponent X Y n =
    shuffleBidegree X Y p q ≫
      eqToHom (by
        rw [AlgebraicTopology.alternatingFaceMapComplex_obj_X, h]) := by
  apply HomologicalComplex.ι_mapBifunctorDesc

@[reassoc]
theorem shuffleComponent_naturality {X X₂ Y Y₂ : SimplicialObject C}
    (f : X ⟶ X₂) (g : Y ⟶ Y₂)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X₂)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y₂)] (n : ℕ) :
    (HomologicalComplex.tensorHom
        ((AlgebraicTopology.alternatingFaceMapComplex C).map f)
        ((AlgebraicTopology.alternatingFaceMapComplex C).map g)).f n ≫
      shuffleComponent X₂ Y₂ n =
    shuffleComponent X Y n ≫
      ((AlgebraicTopology.alternatingFaceMapComplex C).map (f ⊗ₘ g)).f n := by
  ext p q h
  change p + q = n at h
  subst n
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc,
    ιTensorObj_comp_shuffleComponent_assoc, ιTensorObj_comp_shuffleComponent,
    AlgebraicTopology.alternatingFaceMapComplex_map_f, eqToHom_refl,
    Category.comp_id, Category.id_comp]
  dsimp only [curriedTensor]
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def]
  exact (shuffleBidegree_naturality f g p q).symm

end AlgebraicTopology.EilenbergZilber
