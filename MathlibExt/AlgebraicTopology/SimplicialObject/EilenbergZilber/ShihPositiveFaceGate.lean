/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryReduction
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOneSurvivor

/-!
# The remaining positive-face gate for the Shih boundary

All front faces have already been evaluated or cancelled.  The single
remaining combinatorial statement says that the positive faces recover the
omitted front-degree-zero `AW ≫ shuffle` term minus the identity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The exact all-positive-face identity remaining in the explicit Shih
boundary calculation. -/
def ShihPositiveFaceIdentity (X Y : SimplicialObject C) (n : ℕ) : Prop :=
  (∑ i : ShihIndex (n + 1),
      ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
    ∑ i : ShihIndex n,
      ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i =
    awShuffleZeroComponent X Y (n + 1) -
      𝟙 (X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌))

/-- Once the positive-face identity is supplied, the explicit boundary is the
degreewise `AW ≫ shuffle` sum minus the identity. -/
theorem shihBoundary_sum_eq_awShuffle_sub_id_of_positiveFaces
    (X Y : SimplicialObject C) (n : ℕ) (h : ShihPositiveFaceIdentity X Y n) :
    (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 3), shihUpperBoundaryTerm X Y (n + 1) i k) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 2), shihLowerBoundaryTerm X Y n k i =
      awShuffleDiagonalComponent X Y (n + 1) -
        𝟙 (X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌)) := by
  rw [shihBoundary_sum_reduction,
    sum_gapOneBaseSummand_eq_awShuffle_sub_zero]
  rw [show
    awShuffleDiagonalComponent X Y (n + 1) - awShuffleZeroComponent X Y (n + 1) +
          (∑ i : ShihIndex (n + 1),
            ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
        ∑ i : ShihIndex n,
          ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i =
      awShuffleDiagonalComponent X Y (n + 1) - awShuffleZeroComponent X Y (n + 1) +
        ((∑ i : ShihIndex (n + 1),
            ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
          ∑ i : ShihIndex n,
            ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i) by abel,
    h]
  abel

end AlgebraicTopology.EilenbergZilber
