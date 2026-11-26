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

-- The closed forms reach deep levels at once: at level `10 ^ 6` below the arch tops 3/2 and 2/3
-- the branches are at `(10 ^ 6 + 3)/(10 ^ 6 + 2)` and `(10 ^ 6 + 2)/(10 ^ 6 + 3)`.
example :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    t (s^[10 ^ 6] (3 - 2, 2)) = (10 ^ 6 + 3, 10 ^ 6 + 2) ∧
      s (t^[10 ^ 6] (2, 3 - 2)) = (10 ^ 6 + 2, 10 ^ 6 + 3) := by
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ :=
    arch_branch_levels 3 2 2 3 (10 ^ 6) (by decide) (by decide) (by decide) (by decide)
  intro s t
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> apply Nat.cast_injective (R := ℤ) <;> push_cast
  exacts [h₁.trans (by norm_num), h₂.trans (by norm_num), h₃.trans (by norm_num),
    h₄.trans (by norm_num)]

-- Along the left branch the numerator exceeds the denominator by `a - b` at every level.
example (a b k : ℕ) (hb : 0 < b) (hab : b < a) :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    ((t (s^[k] (a - b, b))).1 : ℤ) - (t (s^[k] (a - b, b))).2 = a - b := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := arch_branch_levels a b 1 2 k hb hab one_pos one_lt_two
  intro s t
  rw [h₁, h₂]
  ring

-- Along the right branch the denominator exceeds the numerator by `d - c` at every level.
example (c d k : ℕ) (hc : 0 < c) (hcd : c < d) :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    ((s (t^[k] (c, d - c))).2 : ℤ) - (s (t^[k] (c, d - c))).1 = d - c := by
  obtain ⟨-, h₁, h₂⟩ := arch_branch_levels 2 1 c d k one_pos one_lt_two hc hcd
  intro s t
  rw [h₁, h₂]
  ring

-- At the root and level zero the left denominator uses the coefficient `-1`.
example : euclidPPosition 1 1 = true ∧ euclidPPosition 3 2 = true ∧
    euclidPPosition 2 3 = true ∧ (2 : ℤ) = 3 + (0 - 1) * 1 := by
  obtain ⟨hV, _, _, ⟨_, hden, hL⟩, _, hR⟩ := fibonacci_arch_positions 1 0 (by decide)
  exact ⟨hV, hL, hR, hden⟩

-- At level two of the next arch, check both tops and the asymmetric branch coordinates.
example :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let L := t (s^[2] (3, 5))
    let R := s (t^[2] (5, 2))
    t (s (3, 2)) = (8, 5) ∧ s (t (3, 2)) = (5, 7) ∧
      (L.1 : ℤ) = 14 ∧ (L.2 : ℤ) = 11 ∧ euclidPPosition L.1 L.2 = true ∧
      R = (9, 11) ∧ euclidPPosition R.1 R.2 = true := by
  obtain ⟨_, hTopL, hTopR, ⟨hNum, hDen, hL⟩, hPairR, hR⟩ :=
    fibonacci_arch_positions 2 2 (by decide)
  exact ⟨hTopL, hTopR, hNum, hDen, hL, hPairR, hR⟩
