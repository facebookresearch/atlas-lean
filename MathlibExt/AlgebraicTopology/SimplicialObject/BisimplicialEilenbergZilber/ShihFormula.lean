/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihFormula

/-!
# The bisimplicial Shih formula

The explicit Eilenberg--Mac Lane Shih indices already encode a pair of
simplex-category maps from degree `n + 1` to degree `n` and their sign.  A
bisimplicial object evaluates that pair through `Bisimplicial.map`, giving a
degree-raising endomorphism of its diagonal chains.  This file defines the
signed finite sum and proves its naturality.  Its boundary identity is
developed separately.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- The unsigned bidegree map associated to a Shih index. -/
noncomputable def shihMap {n : ℕ}
    (i : AlgebraicTopology.EilenbergZilber.ShihIndex n) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) :=
  AlgebraicTopology.Bisimplicial.map B i.leftHom i.rightHom

/-- One signed summand in the bisimplicial Shih formula. -/
noncomputable def shihSummand {n : ℕ}
    (i : AlgebraicTopology.EilenbergZilber.ShihIndex n) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) :=
  i.sign • shihMap B i

/-- The degree-`n` component of the explicit bisimplicial Shih operator. -/
noncomputable def shihComponent (n : ℕ) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) :=
  ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n, shihSummand B i

/-- Naturality of the unsigned Shih map. -/
theorem shihMap_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    {n : ℕ} (i : AlgebraicTopology.EilenbergZilber.ShihIndex n) :
    shihMap B i ≫
        (f.app (Opposite.op ⦋n + 1⦌)).app (Opposite.op ⦋n + 1⦌) =
      (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋n⦌) ≫
        shihMap B' i := by
  exact AlgebraicTopology.Bisimplicial.map_naturality f i.leftHom i.rightHom

/-- Naturality of one signed Shih summand. -/
theorem shihSummand_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    {n : ℕ} (i : AlgebraicTopology.EilenbergZilber.ShihIndex n) :
    shihSummand B i ≫
        (f.app (Opposite.op ⦋n + 1⦌)).app (Opposite.op ⦋n + 1⦌) =
      (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋n⦌) ≫
        shihSummand B' i := by
  unfold shihSummand
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  exact shihMap_naturality f i

/-- Naturality of the degreewise Shih component. -/
theorem shihComponent_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (n : ℕ) :
    shihComponent B n ≫
        (f.app (Opposite.op ⦋n + 1⦌)).app (Opposite.op ⦋n + 1⦌) =
      (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋n⦌) ≫
        shihComponent B' n := by
  unfold shihComponent
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact shihSummand_naturality f i

end AlgebraicTopology.BisimplicialEilenbergZilber
