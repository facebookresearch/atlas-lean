/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PebblingCompleteTwo

open MetaMathlibExt SpragueGrundy

-- The empty board is a terminal position with equal residues.
example : IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) ![0, 0] := by
  by_contra hn
  exact ((pebbling_completeTwo_isN_iff ![0, 0]).1 (by decide)).1 hn (by decide)

-- Two pebbles on one vertex can move to a single pebble on the other.
example : ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) ![2, 0] :=
  ((pebbling_completeTwo_isN_iff ![2, 0]).1 (by decide)).2 (by decide)

-- Three pebbles on one vertex can move to two equal singleton piles.
example : ¬ IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) ![0, 3] :=
  ((pebbling_completeTwo_isN_iff ![0, 3]).2 (by decide)).2 (by decide)

-- With three pebbles split between the two vertices, the player to move loses.
example : IsP (pebblingGame (⊤ : SimpleGraph (Fin 2)) 1) ![2, 1] := by
  by_contra hn
  exact (by decide : ¬ 2 ≡ 1 [MOD 3])
    (((pebbling_completeTwo_isN_iff ![2, 1]).2 (by decide)).1 hn)
