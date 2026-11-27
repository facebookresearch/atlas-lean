/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PebblingEvenTotalCompleteThree

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

-- A position in the range of the theorem can already be terminal.
example : IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 2) ![2, 2, 2] :=
  pebbling_completeThree_isP_of_le 2 3 (by decide) (by decide) _ (by decide) (by decide)

-- At ℓ = 2k - 1, the position can still be nonterminal, but the reply is terminal.
example : IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 2) ![2, 3, 1] :=
  pebbling_completeThree_isP_of_le 2 3 (by decide) (by decide) _ (by decide) (by decide)

-- At ℓ = 0, two piles can both reach the cap, and a single reply cannot end the game.
example : IsP (pebblingGame (⊤ : SimpleGraph (Fin 3)) 2) ![6, 6, 0] :=
  pebbling_completeThree_isP_of_le 2 0 (by decide) (by decide) _ (by decide) (by decide)
