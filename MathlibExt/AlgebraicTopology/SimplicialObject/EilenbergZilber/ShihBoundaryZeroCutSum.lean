/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryZeroCut
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOneSurvivor
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Coherence

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial SimplexCategory
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The exceptional zero-cut term is the complete front-degree-zero
Alexander--Whitney--shuffle component. -/
theorem zeroCutAlexanderWhitneyShuffleTerm_eq_awShuffleZeroComponent
    (X Y : SimplicialObject C) (n : ℕ) :
    zeroCutAlexanderWhitneyShuffleTerm X Y n =
      awShuffleZeroComponent X Y (n + 1) := by
  let _ := Shuffle.leftZeroUnique (n + 1)
  unfold awShuffleZeroComponent
  rw [Fintype.sum_unique]
  rw [Shuffle.eq_leftUnitShuffle
    (q := n + 1) (default : Shuffle 0 (n + 1))]
  have hfrontZero :
      (AlexanderWhitney.frontInclusion 0 (n + 1) (n + 1)
        (by omega)).toOrderHom 0 = 0 := by
    rfl
  unfold zeroCutAlexanderWhitneyShuffleTerm awShuffleDiagonalSummand
    awShuffleLeftHom awShuffleRightHom
  simp [Shuffle.leftUnitShuffle_leftHom, hfrontZero,
    Shuffle.leftUnitShuffle_rightHom,
    AlexanderWhitney.backInclusion, SimplexCategory.δ₀Iter_zero]

/-- The terminal zero-cut Shih boundary term is the whole omitted
front-degree-zero Alexander--Whitney--shuffle component. -/
theorem shihZeroCutSurvivor_eq_awShuffleZeroComponent
    (X Y : SimplicialObject C) (n : ℕ) :
    shihUpperBoundaryTerm X Y (n + 1) (ShihIndex.zeroCutSurvivor n)
        (ShihIndex.zeroCutSurvivorFace n) =
      awShuffleZeroComponent X Y (n + 1) := by
  rw [shihZeroCutSurvivor_eq,
    zeroCutAlexanderWhitneyShuffleTerm_eq_awShuffleZeroComponent]

end AlgebraicTopology.EilenbergZilber
