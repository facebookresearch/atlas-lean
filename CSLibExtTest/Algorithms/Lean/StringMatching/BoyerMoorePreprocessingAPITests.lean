/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore.Preprocessing

set_option autoImplicit false

open Cslib.Algorithms.Lean.StringMatching.BoyerMoore

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check badScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check prefixFill

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check borderScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check suffixScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Fallback

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check LeastFallback

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check ShiftCandidate

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check LeastShift

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Strong

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check badScan_time

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check prefixFill_time

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check prefixFill_index

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check suffixScan_time

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check borderScan_stats

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check preprocess_time_le_z

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check badScan_spec

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check preprocess_bad_ret

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check reverseZ_prefix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check reverseZ_isSuffix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check prefixFill_get

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check fallback_step

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check fallback_min_fill

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check borderScan_min

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check borderScan_initial_least

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check shiftCandidate_step

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check suffixScan_min

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check preprocess_leastShift

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check shiftCandidate_bounds

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check shiftCandidate_strong

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check strong_shiftCandidate

example {σ m : Nat} (p : Vector (Fin σ) m) (i : Fin m) :
    0 < (preprocess p).ret.2[i.val] ∧ (preprocess p).ret.2[i.val] ≤ m := by
  have h := preprocess_goodSuffix p i
  exact ⟨h.1, h.2.1⟩

example {σ m : Nat} (p : Vector (Fin σ) m) (c : Fin σ) :
    (preprocess p).ret.1[c.val] ≤ m := by
  rcases preprocess_badCharacter p c with ⟨he, _⟩ | ⟨j, hj, _, he, _⟩ <;> omega

example {σ m : Nat} (p : Vector (Fin σ) m) (hm : 0 < m) :
    ∀ t : Fin m, (preprocess p).ret.2[0] ≤ t.val →
      p[t.val - (preprocess p).ret.2[0]] = p[t.val] :=
  (preprocess_fullMatch p hm).2.2.1

example {σ m : Nat} (p : Vector (Fin σ) m) :
    (preprocess p).time ≤ if m = 0 then σ else σ + 10 * m - 6 :=
  preprocess_time_le p

example : (preprocess (#v[0, 0] : Vector (Fin 1) 2)).ret.2[1] = 2 := by
  have h := preprocess_goodSuffix (#v[0, 0] : Vector (Fin 1) 2) ⟨1, by decide⟩
  dsimp only at h
  by_contra hn
  have he : (preprocess (#v[0, 0] : Vector (Fin 1) 2)).ret.2[1] = 1 := by omega
  have hne := h.2.2.2.1 (by omega)
  apply hne
  simp only [he]
  rfl
