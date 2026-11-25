/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraph

open MathlibExt.Combinatorics.ThreeChromaticZeroTwoGraphWanted

namespace ThreeChromaticZeroTwoGraphTest

private def squareWithIsolates (n : ℕ) : SimpleGraph (Fin n) :=
  .fromRel fun u v ↦ u.val < 4 ∧ v.val < 4 ∧ u.val % 2 ≠ v.val % 2

private instance (n : ℕ) : DecidableRel (squareWithIsolates n).Adj := by
  unfold squareWithIsolates
  infer_instance

private lemma isZeroTwo_iff_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    IsZeroTwo G ↔ ∀ u v : Fin n, u ≠ v →
      let k := (Finset.univ.filter fun x ↦ G.Adj u x ∧ G.Adj v x).card
      k = 0 ∨ k = 2 := by
  have h (u v : Fin n) : G.commonNeighbors u v =
      ↑(Finset.univ.filter fun x ↦ G.Adj u x ∧ G.Adj v x) := by
    ext x
    simp [SimpleGraph.mem_commonNeighbors]
  simp only [IsZeroTwo, h, Set.ncard_coe_finset]

-- A square and a disconnected square with an isolated vertex both satisfy (0,2).
example : IsZeroTwo (squareWithIsolates 4) := by
  rw [isZeroTwo_iff_filter]
  decide

example : IsZeroTwo (squareWithIsolates 5) := by
  rw [isZeroTwo_iff_filter]
  decide

-- The three-chromatic triangle fails the common-neighbor condition.
example : (⊤ : SimpleGraph (Fin 3)).chromaticNumber = 3 := by
  rw [SimpleGraph.chromaticNumber_top, Fintype.card_fin]
  rfl

example : ¬ IsZeroTwo (⊤ : SimpleGraph (Fin 3)) := by
  rw [isZeroTwo_iff_filter]
  decide

example : ¬ conjecture := conjecture_refuted

end ThreeChromaticZeroTwoGraphTest
