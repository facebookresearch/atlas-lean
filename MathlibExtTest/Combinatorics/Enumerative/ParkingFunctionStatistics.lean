/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
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

namespace MetaMathlibExt.parkingFunction_descentSet_card_eq_ascentSet_reflect

open parkingFunction_descentSet_card_eq_ascentSet

example : countWith 0 (· > ·) ∅ = countWith 0 (· < ·) ∅ := by
  exact parkingFunction_descentSet_card_eq_ascentSet_reflect 0 ∅ (by simp)

-- Reversal sends the first two descent positions to the last two ascent positions.
example : countWith 4 (· < ·) {2, 3} = 9 := by
  have h : ({1, 2} : Finset ℕ).image (fun i => 4 - i) = {2, 3} := by decide
  calc
    _ = countWith 4 (· > ·) {1, 2} := by
      rw [← h]
      exact (parkingFunction_descentSet_card_eq_ascentSet_reflect 4 {1, 2} (by decide)).symm
    _ = 9 := by decide

end MetaMathlibExt.parkingFunction_descentSet_card_eq_ascentSet_reflect

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

namespace MetaMathlibExt.card_peakless_parkingFunction_max_ties

-- The words of `s` with no peaks and `n - 1` ties.
private def peaklessMaxTies (n : ℕ) (s : Finset (Fin n → Fin n)) : Finset (Fin n → Fin n) :=
  s.filter fun f =>
    (∀ i j k : Fin n, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (f i < f j ∧ f k < f j)) ∧
      (Finset.univ.filter (fun i => ∃ j, j.val = i.val + 1 ∧ f i = f j)).card = n - 1

private abbrev parking (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter fun f => IsParkingFunction n f

-- The three constant words qualify; the parking condition keeps only the all-ones word `1 1 1`.
example : (peaklessMaxTies 3 Finset.univ).card = 3 ∧
    peaklessMaxTies 3 (parking 3) = {fun _ => 0} := by
  decide

-- The count is also `1` for the empty word, which the theorem excludes.
example : (peaklessMaxTies 0 (parking 0)).card = 1 := by decide

example : (peaklessMaxTies 5 (parking 5)).card = 1 :=
  card_peakless_parkingFunction_max_ties 5 (by omega)

end MetaMathlibExt.card_peakless_parkingFunction_max_ties

namespace MetaMathlibExt.valleyless_tieless_prepend_one_bijOn

private def words (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter fun f => IsParkingFunction n f ∧
    (∀ i j : Fin n, j.val = i.val + 1 → f i ≠ f j) ∧
    ∀ i j k : Fin n, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (f j < f i ∧ f j < f k)

private abbrev images (n : ℕ) : Set (Fin (n + 1) → Fin (n + 1)) :=
  (fun f : Fin n → Fin n => Fin.cons (0 : Fin (n + 1)) fun i => (f i).succ) '' (words n : Set _)

-- At the smallest allowed length the sole image is (1, 2) in one-based preferences.
example : images 1 = {![0, 1]} := by
  unfold images words
  rw [(valleyless_tieless_prepend_one_bijOn 1 (by decide)).image_eq]
  ext g
  revert g
  decide

-- Both orders of the two tail entries occur. The word (1, 2, 1) fails the endpoint condition.
example : images 2 = {![0, 1, 2], ![0, 2, 1]} := by
  unfold images words
  rw [(valleyless_tieless_prepend_one_bijOn 2 (by decide)).image_eq]
  ext g
  revert g
  decide

end MetaMathlibExt.valleyless_tieless_prepend_one_bijOn
