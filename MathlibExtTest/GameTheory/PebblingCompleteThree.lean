/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PebblingCompleteThree

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

-- At the smallest k, an empty pile and a pile exactly at the upper bound can coexist.
example : ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 1) ![4, 0, 1] :=
  pebbling_completeThree_isN_of_le_fourK 1 (by decide) _ (by decide) (by decide)

-- Two piles can tie for largest while the unique smallest pile is just below 2k.
example : ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 2) ![4, 3, 4] :=
  pebbling_completeThree_isN_of_le_fourK 2 (by decide) _ (by decide) (by decide)

-- At the smallest positive k, the reply leaves exactly one pebble on each vertex.
example : IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 1) ![5, 0, 0] :=
  pebbling_completeThree_isP_twoKAddThree 1 (by decide) (Equiv.refl _)

-- The single pile may lie at a vertex other than zero.
example : IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 2) ![0, 0, 7] := by
  have h : (![7, 0, 0] : Fin 3 → ℕ) ∘ Equiv.swap 0 2 = ![0, 0, 7] := by decide
  rw [← h]
  exact pebbling_completeThree_isP_twoKAddThree 2 (by decide) (Equiv.swap 0 2)
