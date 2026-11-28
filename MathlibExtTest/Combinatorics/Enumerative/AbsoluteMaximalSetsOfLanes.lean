/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AbsoluteMaximalSetsOfLanes

open MetaMathlibExt

-- The empty intersection has one absolute maximal set.
example : (Finset.univ.filter fun S : Finset (Fin 0 × Fin 0) =>
    IsAbsoluteMaximalSetOfLanes S).card = 1 :=
  (card_absolute_maximalSetsOfLanes 0).trans lonelySinglesCount_zero_one.1

-- Two U-turns separated by a two-point block cannot be exchanged.
example : IsAbsoluteMaximalSetOfLanes ({(0, 2), (2, 0), (1, 1), (3, 3)} :
    Finset (Fin 4 × Fin 4)) := by decide

-- With adjacent U-turns the exchange is possible.
example :
    let S : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 1), (2, 3), (3, 2)}
    IsMaximalSetOfLanes Finset.univ S ∧ ¬ IsAbsoluteMaximalSetOfLanes S := by decide

-- One entry does not admit two distinct U-turns to exchange.
example : (Finset.univ.filter fun S : Finset (Fin 1 × Fin 1) =>
    IsMaximalSetOfLanes Finset.univ S ∧ ¬ IsAbsoluteMaximalSetOfLanes S).card = 0 :=
  (card_nonabsolute_maximalSetsOfLanes 1).trans (marriageableSinglesCount_of_le_one le_rfl)

-- At size two, just the set of both U-turns admits an exchange.
example : marriageableSinglesCount 2 = 1 := by
  rw [← card_nonabsolute_maximalSetsOfLanes]
  decide
