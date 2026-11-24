/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ParkingFunctionStatistics

/-! # Tests for ascent and descent sets of parking functions -/

namespace MetaMathlibExt.parkingFunction_descentSet_card_eq_ascentSet

private def countWith (n : ℕ) (r : Fin n → Fin n → Prop) [DecidableRel r] (I : Finset ℕ) : ℕ :=
  ((Finset.univ.filter (IsParkingFunction n)).filter fun f =>
    (Finset.univ.filter (fun i => ∃ j, j.val = i.val + 1 ∧ r (f i) (f j))).image
      (fun i => i.val + 1) = I).card

-- The empty word contributes one parking function on each side.
example : countWith 0 (· > ·) ∅ = 1 ∧ countWith 0 (· < ·) ∅ = 1 := by decide

-- Prescribe two separated descents, then use equidistribution for the same ascent positions.
example : countWith 4 (· < ·) {1, 3} = 19 := by
  calc
    _ = countWith 4 (· > ·) {1, 3} :=
      (parkingFunction_descentSet_card_eq_ascentSet 4 {1, 3} (by decide)).symm
    _ = 19 := by decide

end MetaMathlibExt.parkingFunction_descentSet_card_eq_ascentSet
