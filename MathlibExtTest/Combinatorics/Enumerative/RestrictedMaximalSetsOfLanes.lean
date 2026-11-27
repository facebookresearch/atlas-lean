/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RestrictedMaximalSetsOfLanes

open MetaMathlibExt

-- At size one the only lane is a forbidden U-turn, so the empty set is the only maximal set.
example : (Finset.univ.filter fun S : Finset (Fin 1 × Fin 1) =>
    IsMaximalSetOfLanes (Finset.univ.filter fun ℓ : Fin 1 × Fin 1 => ℓ.1 ≠ ℓ.2) S).card = 1 :=
  (card_restricted_maximalSetsOfLanes 1).trans lonelySinglesCount_zero_one.2

-- An unused index does not spoil maximality once U-turns are forbidden: `{E_0X_2, E_2X_0}` is
-- maximal in the restricted intersection of size three, but not among all lanes (add `E_1X_1`).
example :
    let S : Finset (Fin 3 × Fin 3) := {(0, 2), (2, 0)}
    IsMaximalSetOfLanes (Finset.univ.filter fun ℓ : Fin 3 × Fin 3 => ℓ.1 ≠ ℓ.2) S ∧
      ¬ IsMaximalSetOfLanes Finset.univ S := by
  decide

-- The four maximal sets of lanes without U-turns at size three give `L_3 = 4`.
example : lonelySinglesCount 3 = 4 := by
  rw [← card_restricted_maximalSetsOfLanes]
  decide
