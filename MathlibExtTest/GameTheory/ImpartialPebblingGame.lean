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
