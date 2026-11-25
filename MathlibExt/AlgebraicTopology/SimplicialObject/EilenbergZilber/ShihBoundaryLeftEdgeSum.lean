/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryLeftEdgeCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryZeroCutSum

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

@[simp]
theorem leftEdgeIndex_zero_eq_identitySurvivor (n : ℕ) :
    leftEdgeIndex (n + 1) (0 : Fin (n + 1)) 0 = identitySurvivor n := by
  unfold leftEdgeIndex identitySurvivor
  congr 1
  apply Shuffle.eq_rightUnitShuffle

@[simp]
theorem leftEdgeFace_zero_eq_identitySurvivorFace (n : ℕ) :
    leftEdgeFace (n + 1) (0 : Fin (n + 1)) 0 = identitySurvivorFace n := by
  apply Fin.ext
  simp [identitySurvivorFace]

@[simp]
theorem leftEdgeIndex_last_eq_zeroCutSurvivor (n : ℕ) :
    leftEdgeIndex (n + 1) (Fin.last n) (Fin.last 1) = zeroCutSurvivor n := by
  unfold leftEdgeIndex zeroCutSurvivor
  congr

@[simp]
theorem leftEdgeFace_last_eq_zeroCutSurvivorFace (n : ℕ) :
    leftEdgeFace (n + 1) (Fin.last n) (Fin.last 1) =
      zeroCutSurvivorFace n := by
  rw [leftEdgeFace_last]
  rfl

end ShihIndex

section Telescope

variable {A : Type*} [AddCommGroup A]

/-- A finite chain whose adjacent right/left entries cancel reduces to its
two outer endpoints. -/
theorem sum_fin_pairs_eq_endpoints_of_adjacent_cancel
    (n : ℕ) (left right : Fin (n + 1) → A)
    (hcancel : ∀ q : Fin n, right q.castSucc + left q.succ = 0) :
    ∑ q, (left q + right q) = left 0 + right (Fin.last n) := by
  rw [Finset.sum_add_distrib, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hmiddle :
      (∑ q : Fin n, left q.succ) + ∑ q : Fin n, right q.castSucc = 0 := by
    rw [add_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun q _ => hcancel q
  calc
    left 0 + (∑ q : Fin n, left q.succ) +
          ((∑ q : Fin n, right q.castSucc) + right (Fin.last n)) =
        left 0 +
          ((∑ q : Fin n, left q.succ) +
            ∑ q : Fin n, right q.castSucc) + right (Fin.last n) := by abel
    _ = left 0 + right (Fin.last n) := by rw [hmiddle]; simp

end Telescope

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The complete `p = 0` left-edge family telescopes from the negative
identity survivor to the zero-cut Alexander--Whitney--shuffle survivor. -/
theorem shihLeftEdge_sum_eq_awShuffleZeroComponent_sub_id
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ q : Fin (n + 1), (
        shihUpperBoundaryTerm X Y (n + 1)
            (ShihIndex.leftEdgeIndex (n + 1) q 0)
            (ShihIndex.leftEdgeFace (n + 1) q 0) +
          shihUpperBoundaryTerm X Y (n + 1)
            (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
            (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1)))) =
      awShuffleZeroComponent X Y (n + 1) - 𝟙 _ := by
  rw [sum_fin_pairs_eq_endpoints_of_adjacent_cancel]
  · rw [ShihIndex.leftEdgeIndex_zero_eq_identitySurvivor,
      ShihIndex.leftEdgeFace_zero_eq_identitySurvivorFace,
      ShihIndex.leftEdgeIndex_last_eq_zeroCutSurvivor,
      ShihIndex.leftEdgeFace_last_eq_zeroCutSurvivorFace,
      shihIdentitySurvivor_eq_neg_id,
      shihZeroCutSurvivor_eq_awShuffleZeroComponent]
    abel
  · intro q
    exact shihLeftEdge_last_add_zeroSucc_eq_zero X Y n q

end AlgebraicTopology.EilenbergZilber
