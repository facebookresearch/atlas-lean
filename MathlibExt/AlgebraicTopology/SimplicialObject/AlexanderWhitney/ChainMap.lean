/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Differential

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Simplicial

namespace AlgebraicTopology.AlexanderWhitney

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

/-- The Alexander--Whitney map on alternating-face complexes. -/
noncomputable def alternatingMap :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y)) ⟶
      HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) where
  f := alternatingComponent X Y
  comm' := fun {i j} hij ↦ by
    subst hij
    exact alternatingComponent_comm X Y j

@[simp]
theorem alternatingMap_f (n : ℕ) :
    (alternatingMap X Y).f n = alternatingComponent X Y n := rfl

private lemma alternatingComponent_naturality
    {X X' Y Y' : SimplicialObject C} (f : X ⟶ X') (g : Y ⟶ Y')
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X')
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y')]
    (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).map (f ⊗ₘ g)).f n ≫
        alternatingComponent X' Y' n =
      alternatingComponent X Y n ≫
        (HomologicalComplex.tensorHom
          ((AlgebraicTopology.alternatingFaceMapComplex C).map f)
          ((AlgebraicTopology.alternatingFaceMapComplex C).map g)).f n := by
  simp only [alternatingComponent, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  dsimp
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  dsimp only [curriedTensor]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  rw [frontFace_naturality, backFace_naturality]
  rfl

@[reassoc]
theorem alternatingMap_naturality
    {X X' Y Y' : SimplicialObject C} (f : X ⟶ X') (g : Y ⟶ Y')
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X')
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y')] :
    (AlgebraicTopology.alternatingFaceMapComplex C).map (f ⊗ₘ g) ≫
        alternatingMap X' Y' =
      alternatingMap X Y ≫
        HomologicalComplex.tensorHom
          ((AlgebraicTopology.alternatingFaceMapComplex C).map f)
          ((AlgebraicTopology.alternatingFaceMapComplex C).map g) := by
  ext n
  exact alternatingComponent_naturality f g n

end AlgebraicTopology.AlexanderWhitney
