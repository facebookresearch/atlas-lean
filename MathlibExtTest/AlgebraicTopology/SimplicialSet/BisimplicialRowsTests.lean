/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialRows

/-!
# Bisimplicial row and transpose tests

These tests pin the swapped row coordinates, the outer-then-inner transposed
diagonal action, identity components and map naturality of the diagonal
transpose isomorphism, and the closed-T1 shadow of outer degeneracies.  They
make no properness or weak-equivalence claim.
-/

open CategoryTheory Opposite Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BisimplicialRowsTests

variable (X : SimplicialObject SSet.{u})

example (a b : SimplexCategoryᵒᵖ) :
    (SSet.simplicialRow X a).obj b = (X.obj b).obj a :=
  SSet.simplicialRow_obj X a b

example (a : SimplexCategoryᵒᵖ) {b c : SimplexCategoryᵒᵖ} (k : b ⟶ c) :
    (SSet.simplicialRow X a).map k = (X.map k).app a :=
  SSet.simplicialRow_map X a k

example {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (SSet.simplicialDiagonalFunctor.obj
      (SSet.simplicialTransposeFunctor.obj X)).map f =
        (X.map f).app a ≫ (X.obj b).map f :=
  SSet.simplicialDiagonalTranspose_obj_map X f

example (a : SimplexCategoryᵒᵖ) :
    (SSet.simplicialDiagonalTransposeIso X).hom.app a = 𝟙 _ :=
  SSet.simplicialDiagonalTransposeIso_hom_app X a

example (a : SimplexCategoryᵒᵖ) :
    (SSet.simplicialDiagonalTransposeIso X).inv.app a = 𝟙 _ :=
  SSet.simplicialDiagonalTransposeIso_inv_app X a

section Naturality

variable {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)

example (a b : SimplexCategoryᵒᵖ) :
    ((SSet.simplicialTransposeFunctor.map η).app a).app b =
      (η.app b).app a :=
  SSet.simplicialTranspose_map_app η a b

example :
    SSet.simplicialDiagonalFunctor.map
          (SSet.simplicialTransposeFunctor.map η) ≫
        (SSet.simplicialDiagonalTransposeIso Y).hom =
      (SSet.simplicialDiagonalTransposeIso X).hom ≫
        SSet.simplicialDiagonalFunctor.map η :=
  SSet.simplicialDiagonalTransposeIso_naturality η

end Naturality

section Degeneracy

variable (X₀ : SimplicialObject SSet.{0}) {n : ℕ} (i : Fin (n + 1))

example : Mono (X₀.σ i) :=
  SimplicialObject.mono_sigma X₀ i

example : TopCat.closedT1Embeddings (SSet.toTop.map (X₀.σ i)) :=
  SSet.closedT1_rowDegeneracy X₀ i

end Degeneracy

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BisimplicialRowsTests
