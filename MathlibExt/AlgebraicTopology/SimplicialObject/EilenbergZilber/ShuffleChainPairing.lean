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
# The shuffle pairing of alternating-face chain complexes

Let C be a preadditive monoidal category whose tensor product is additive in both variables,
and let X and Y be simplicial objects. When the tensor complex of their alternating-face
complexes exists, the Eilenberg–Zilber shuffle map is a chain pairing with target the
alternating-face complex of the degreewise tensor product X ⊗ Y.

Its bidegree (p, q) map is the signed sum over ordered shuffles of the tensor products of the
two rank-surjection maps. The tensor differential uses the sign (−1)^p on the second-factor
boundary. Thus the chain-map condition is the signed Leibniz law for this pairing.

See Weibel, *An Introduction to Homological Algebra*, Chapter 8.
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

/-- Let C be a preadditive monoidal category with tensor product additive in both variables, and
let X and Y be simplicial objects. Assume the tensor complex of K_X and K_Y exists, where K
denotes the alternating-face complex. The shuffle map defines a chain pairing K_X ⊗ K_Y ⟶
K_(X⊗Y). In bidegree (p, q), its map X_p ⊗ Y_q ⟶ X_(p+q) ⊗ Y_(p+q) is ∑ s : Shuffle p q,
sign(s) • (X.map s.leftHom.op ⊗ₘ Y.map s.rightHom.op), with sign(s) the integer value of the
permutation sign. -/
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
