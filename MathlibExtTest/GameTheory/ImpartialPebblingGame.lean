/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ImpartialPebblingGame

open MetaMathlibExt

-- At the largest allowed ℓ for k = 1, the reply leaves every pile at most one.
example : ∀ b ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) 1 ![2, 0, 2],
    ∃ c ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) 1 b, ∀ i, c i ≤ 1 :=
  pebbling_completeThree_response_lowersMax 1 1 (by decide) (by decide) _ (by decide)
    ⟨0, by decide⟩ (by decide)

-- Moving into an empty pile forces the reply to draw from the untouched pile.
example : ![0, 1, 2] ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) 1 ![2, 0, 2] ∧
    ![1, 1, 0] ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) 1 ![0, 1, 2] ∧
    pebblingMoves (⊤ : SimpleGraph (Fin 3)) 1 ![1, 1, 0] = ∅ := by
  decide

-- If the first destination already held one pebble, reversing the move can lower the bound.
example : ![0, 2, 1] ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) 1 ![2, 1, 1] ∧
    ![1, 0, 1] ∈ pebblingMoves (⊤ : SimpleGraph (Fin 3)) 1 ![0, 2, 1] := by
  decide

-- The four-cycle predicates use cyclic indices and ignore multiples of their modulus.
example : C4PatternAAAB ![4, 1, 3, 1] ∧ C4ModFourABABHat ![1, 6, 5, 2] := by
  unfold C4PatternAAAB C4ModFourABABHat
  decide

-- A rotational reply preserves the alternating pattern when both sources are emptied.
example : C4PatternABAB ![2, 0, 2, 0] := by
  have h := c4Pattern_invariant_rotationalSymmetric_reflectional ![1, 2, 1, 2] 3 1
    (Or.inl rfl) (by decide) ![2, 0, 2, 0] (Or.inl ⟨by decide, by decide⟩)
  apply h.2.1
  unfold C4PatternABAB
  decide

/- A reflectional reply after the move from 0 to 3 preserves the adjacent repeated residue
even as it changes from two to zero. -/
example : C4PatternAABC ![0, 0, 1, 2] := by
  have h := c4Pattern_invariant_rotationalSymmetric_reflectional ![2, 2, 0, 1] 0 (-1)
    (Or.inr rfl) (by decide) ![0, 0, 1, 2] (Or.inr ⟨by decide, by decide⟩)
  apply h.2.2.1
  unfold C4PatternAABC
  decide

-- Moving from 3 to 0 empties the source and changes adjacent pairs into an ABAC pattern.
example : C4PatternABAC ![1, 0, 2, 0] := by
  have h := (c4Pattern_closed_under_moves ![0, 0, 2, 2] ![1, 0, 2, 0] (by decide)).1
  have ha : C4PatternAABBHat ![0, 0, 2, 2] := by unfold C4PatternAABBHat; decide
  exact (h (Or.inl ha)).resolve_left (by unfold C4PatternAABBHat; decide)

-- In the other union, a move from alternating residues can leave an equal pair across 3 and 0.
example : C4PatternAABC ![0, 1, 2, 0] := by
  have h := (c4Pattern_closed_under_moves ![2, 0, 2, 0] ![0, 1, 2, 0] (by decide)).2
  have ha : C4PatternABAB ![2, 0, 2, 0] := by unfold C4PatternABAB; decide
  have hb := (h (Or.inr (Or.inl ha))).resolve_left (by unfold C4PatternAAAB; decide)
  exact hb.resolve_left (by unfold C4PatternABAB; decide)
