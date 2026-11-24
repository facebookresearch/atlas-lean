/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.EuclidGameCalkinWilf

open MetaMathlibExt

-- The root is terminal, and its two arch tops occur in the second row.
example : euclidMoves (1, 1) = ∅ ∧ (3, 2) ∈ calkinWilfRow 2 ∧ (2, 3) ∈ calkinWilfRow 2 := by
  decide

-- The two distinct paths also give P-positions for an unequal pair with a common factor.
example : euclidPPosition 14 10 = true ∧ euclidPPosition 10 16 = true :=
  euclidPPosition_tops_of_arch 4 6 (by decide) (by decide) (by decide)

-- From the left arch top the move is forced, although the reply need not be.
example : euclidMoves (14, 10) = {(4, 10)} ∧ euclidMoves (4, 10) = {(4, 6), (4, 2)} := by
  decide

-- At the root both mixed grandchildren are P-positions, so the aunt cannot be one.
example : euclidPPosition 2 1 ≠ true := by
  have h := (euclidPPosition_aunt_xor_cousin 1 1 (by decide) (by decide)).1 (by decide)
  exact fun ha => h.mp ha (by decide)

-- At (4, 2) the female cousin is an N-position, so the uncle is a P-position.
example : euclidPPosition 4 6 = true :=
  ((euclidPPosition_aunt_xor_cousin 4 2 (by decide) (by decide)).2.2.1 (by decide)).mpr (by decide)

-- The daughter (3, 2) and its niece (4, 3) continue the same branch.
example : euclidPPosition 4 3 = true :=
  (euclidPPosition_branch_step 1 2 (by decide) (by decide)).1 (by decide)

-- The nephew implication also applies to pairs with a common factor.
example : euclidPPosition 6 8 = true :=
  (euclidPPosition_branch_step 4 2 (by decide) (by decide)).2 (by decide)

-- At level zero the coefficient 3k - 2 in the left branch formula is negative.
example : euclidPPosition 8 5 = true ∧ euclidPPosition 5 7 = true ∧
    (7 : ℤ) = 3 * 3 + (3 * 0 - 2) * 1 := by
  obtain ⟨⟨_, hL, hR, _, _, _, hden⟩, _⟩ := fibonacci_arch_tops 1 0 (by decide)
  exact ⟨hL, hR, hden⟩

-- Two levels down the next arch, the two branch positions have different numerators.
example : euclidPPosition 14 11 = true ∧ euclidPPosition 9 11 = true ∧
    euclidPPosition 29 20 = true ∧ euclidPPosition 20 31 = true := by
  obtain ⟨⟨hX, _⟩, hY, hL, hR, _⟩ := fibonacci_arch_tops 2 2 (by decide)
  exact ⟨hX, hY, hL, hR⟩

-- Two daughter steps followed by a son reach P-positions from both (3, 2) and the root.
example : euclidPPosition 7 9 = true :=
  (euclidPPosition_self_similar 2 (3, 2) (by decide) (by decide) [true, true, false]).trans
    (by decide)

-- Three alternating steps from the same vertex end at an N-position.
example : euclidPPosition 8 13 = false :=
  (euclidPPosition_self_similar 2 (3, 2) (by decide) (by decide) [false, true, false]).trans
    (by decide)
