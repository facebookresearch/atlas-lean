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

namespace MetaMathlibExt.sum_ndpf_multisetDescent_eq

private def fiberCount {n : ℕ} (β : Fin n → Fin n) (I : Finset ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Fin n =>
    Finset.univ.val.map w = Finset.univ.val.map β ∧
      (Finset.univ.filter (fun i => ∃ j, j.val = i.val + 1 ∧ w j < w i)).image
        (fun i => i.val + 1) = I).card

-- The empty content has exactly one rearrangement with no descents.
example : fiberCount (id : Fin 0 → Fin 0) ∅ = 1 := by decide

-- With descent set {1}, content (0,1,1) contributes once and (0,1,2) contributes twice.
example : fiberCount (fun i : Fin 3 => min i 1) {1} = 1 ∧
    fiberCount (id : Fin 3 → Fin 3) {1} = 2 := by decide

open Classical parkingFunction_descentSet_card_eq_ascentSet in
example :
    ∑ β ∈ Finset.univ.filter (fun β : Fin 3 → Fin 3 => IsParkingFunction 3 β ∧ Monotone β),
      fiberCount β {1} = 5 := by
  calc
    _ = countWith 3 (· > ·) {1} := sum_ndpf_multisetDescent_eq 3 {1} (by decide)
    _ = 5 := by decide

end MetaMathlibExt.sum_ndpf_multisetDescent_eq
