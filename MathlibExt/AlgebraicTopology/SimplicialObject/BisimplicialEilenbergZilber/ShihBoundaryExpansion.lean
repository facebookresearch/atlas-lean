/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihComposite

/-!
# Boundary expansion for the bisimplicial Shih operator

The two contributions to the boundary of the degree-raising Shih component
are expanded into finite double sums.  This is the additive expansion only;
the combinatorial cancellations are handled in subsequent files.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- A diagonal face applied after a degree-`n` bisimplicial Shih summand. -/
noncomputable def shihUpperBoundaryTerm (n : ℕ)
    (i : AlgebraicTopology.EilenbergZilber.ShihIndex n)
    (k : Fin (n + 2)) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n :=
  ((-1 : ℤ) ^ k.val) •
    (shihSummand B i ≫ ((SimplicialObject.diagonalFunctor A).obj B).δ k)

/-- A diagonal face applied before a degree-`n` bisimplicial Shih summand. -/
noncomputable def shihLowerBoundaryTerm (n : ℕ)
    (k : Fin (n + 2))
    (i : AlgebraicTopology.EilenbergZilber.ShihIndex n) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) :=
  ((-1 : ℤ) ^ k.val) •
    (((SimplicialObject.diagonalFunctor A).obj B).δ k ≫ shihSummand B i)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of a Shih component followed by the diagonal differential. -/
theorem shihComponent_comp_d (n : ℕ) :
    shihComponent B n ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) n =
      ∑ z : Fin (n + 2) × AlgebraicTopology.EilenbergZilber.ShihIndex n,
        shihUpperBoundaryTerm B n z.2 z.1 := by
  unfold shihComponent AlgebraicTopology.AlternatingFaceMapComplex.objD
    shihUpperBoundaryTerm
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ]

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of the diagonal differential followed by a Shih component. -/
theorem d_comp_shihComponent (n : ℕ) :
    AlgebraicTopology.AlternatingFaceMapComplex.objD
          ((SimplicialObject.diagonalFunctor A).obj B) n ≫
        shihComponent B n =
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihIndex n × Fin (n + 2),
        shihLowerBoundaryTerm B n z.2 z.1 := by
  unfold shihComponent AlgebraicTopology.AlternatingFaceMapComplex.objD
    shihLowerBoundaryTerm
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp]
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ]

end AlgebraicTopology.BisimplicialEilenbergZilber
