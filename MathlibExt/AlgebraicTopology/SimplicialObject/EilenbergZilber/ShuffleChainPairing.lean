/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairing
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ChainMap

/-!
# The Eilenberg–Zilber shuffle chain pairing

The shuffle map defines a chain pairing of alternating
complexes. The generic pairing descent gives the
corresponding homology pairing when the relevant
homology objects exist.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Simplicial

namespace AlgebraicTopology.EilenbergZilber

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

/-- The shuffle chain map, viewed as a degree-preserving chain pairing. -/
noncomputable def alternatingPairing :
    HomologicalComplex.ChainGradedPairing
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y)) :=
  alternatingMap X Y

@[simp]
theorem alternatingPairing_pair (p q : ℕ) :
    HomologicalComplex.ChainGradedPairing.pair
        (alternatingPairing X Y) p q =
      HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q (p + q) rfl ≫
        shuffleComponent X Y (p + q) := rfl

@[reassoc]
theorem alternatingPairing_naturality
    {X X' Y Y' : SimplicialObject C} (f : X ⟶ X') (g : Y ⟶ Y')
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X')
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y')] :
    HomologicalComplex.tensorHom
        ((AlgebraicTopology.alternatingFaceMapComplex C).map f)
        ((AlgebraicTopology.alternatingFaceMapComplex C).map g) ≫
      alternatingPairing X' Y' =
    alternatingPairing X Y ≫
      (AlgebraicTopology.alternatingFaceMapComplex C).map (f ⊗ₘ g) :=
  alternatingMap_naturality f g

end AlgebraicTopology.EilenbergZilber
