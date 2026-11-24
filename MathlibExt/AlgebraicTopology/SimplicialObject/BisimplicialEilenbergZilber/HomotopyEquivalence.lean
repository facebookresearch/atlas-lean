/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ProjectedRetraction
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihHomotopy

/-!
# Bisimplicial Eilenberg--Zilber homotopy equivalence

The double-normalization projector is homotopic to the total identity, while
the projector-sandwiched shuffle/Alexander--Whitney composite is strictly the
projector.  These facts give the total-side homotopy.  Together with the
explicit diagonal Shih homotopy they package the Alexander--Whitney and
shuffle chain maps as a homotopy equivalence.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialNormalization

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasCountableCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- The shuffle--Alexander--Whitney composite is homotopic to the total identity. -/
noncomputable def totalCompositeHomotopy :
    Homotopy
      (AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap B ≫
        AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B)
      (𝟙 (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B)) := by
  let P := totalPInfty B
  let F := AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap B ≫
    AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B
  let H := totalPInftyHomotopy B
  let Hleft : Homotopy F (P ≫ F) := by
    simpa only [Category.id_comp] using H.symm.compRight F
  let Hright : Homotopy (P ≫ F) ((P ≫ F) ≫ P) := by
    simpa only [Category.comp_id] using H.symm.compLeft (P ≫ F)
  let Hstrict : Homotopy ((P ≫ F) ≫ P) P :=
    Homotopy.ofEq (by
      dsimp only [P, F]
      simpa only [Category.assoc] using projectedStrictRetraction B)
  exact Hleft.trans (Hright.trans (Hstrict.trans H))

/-- The natural Alexander--Whitney/shuffle homotopy equivalence. -/
noncomputable def homotopyEquiv :
    HomotopyEquiv
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B)
      (AlgebraicTopology.bisimplicialAlternatingTotalComplex A B) where
  hom := AlgebraicTopology.BisimplicialAlexanderWhitney.alternatingMap B
  inv := AlgebraicTopology.BisimplicialEilenbergZilber.alternatingMap B
  homotopyHomInvId := AlgebraicTopology.BisimplicialEilenbergZilber.homotopy B
  homotopyInvHomId := totalCompositeHomotopy B

end AlgebraicTopology.BisimplicialNormalization
