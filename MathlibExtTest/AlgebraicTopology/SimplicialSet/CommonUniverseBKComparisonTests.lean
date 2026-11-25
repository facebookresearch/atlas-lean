/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotal

/-!
# Original carrier, Alexander--Whitney and shuffle clients

The actual carrier-chain presentation is the identity on its original
complex. The comparison retains the exact original forward and inverse
programs and both true homotopies on those original complexes.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe uJ vJ uA vA

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKComparisonTests

variable {J : Type uJ} [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max uJ vJ} A] (R : A) (D : J ⥤ SSet.{max uJ vJ})

/-- Both directions of the actual carrier-chain identification are the
original identity presentation. -/
theorem originalCarrierPresentation :
    (SSet.bkCarrierChainIso A R D).hom = 𝟙 _ ∧
      (SSet.bkCarrierChainIso A R D).inv = 𝟙 _ :=
  ⟨rfl, rfl⟩

/-- The actual carrier comparison retains the original inverse-diagonal/AW
forward, shuffle/diagonal inverse, and both complete original homotopies. -/
theorem originalCarrierAWShuffle :
    let B := SSet.bkLinearizedBisimplicial A R D
    let c := SSet.bkCarrierChainIso A R D
    let d := SSet.bkDiagonalAlternatingComplexIso A R D
    let e := (HomotopyEquiv.ofIso c).trans (SSet.bkDiagonalTotalHomotopyEquiv A R D)
    e.hom = c.hom ≫ (d.inv ≫ AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B) ∧
      e.inv = (AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap B ≫ d.hom) ≫ c.inv ∧
      Nonempty (Homotopy (e.hom ≫ e.inv) (𝟙 ((SSet.bkHocolim D).chainComplex R))) ∧
      Nonempty (Homotopy (e.inv ≫ e.hom) (𝟙 (SSet.bkAlternatingTotalComplex A R D))) := by
  let c := SSet.bkCarrierChainIso A R D
  let e := (HomotopyEquiv.ofIso c).trans (SSet.bkDiagonalTotalHomotopyEquiv A R D)
  exact ⟨rfl, rfl, ⟨e.homotopyHomInvId⟩, ⟨e.homotopyInvHomId⟩⟩

/-- The original homology isomorphism is induced by that same original
diagonal/total homotopy equivalence. -/
theorem originalHomologyComparison (S : AddCommGrpCat.{max uJ vJ}) (n : ℕ) :
    SSet.bkDiagonalTotalHomologyIso S D n =
      (SSet.bkDiagonalTotalHomotopyEquiv AddCommGrpCat.{max uJ vJ} S D).toHomologyIso n :=
  rfl

end MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKComparisonTests

end
