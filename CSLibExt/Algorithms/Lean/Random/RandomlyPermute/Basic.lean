/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# Fisher–Yates permutation with supplied legal draws

The increasing-position procedure in CLRS, fourth edition, Section5.3
(printed page136), swaps each saved position with a uniformly selected suffix
position. Here a direct dependent history supplies those legal choices.

Each retrieved choice emits `(1, 0)` and each canonical `Vector.swap` emits
`(0, 1)`. The final singleton draw and self-swap are executed. Index arithmetic,
allocation, copying and random-bit generation are not charged; this is not a
physical constant-space or PRNG cost claim.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

namespace Cslib.Algorithms.Lean.TimeM

universe u

@[no_expose] private def scan {α : Type u} {n : Nat}
    (draws : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n) :
    Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n) :=
  if hi : i < n then do
    TimeM.tick (1, 0)
    let draw := draws ⟨i, hi⟩
    let j := i + draw.val
    TimeM.tick (0, 1)
    let saved := xs.swap i j hi (by
      dsimp [j]
      have hd : draw.val < n - i := draw.isLt
      omega)
    scan draws (i + 1) saved
  else
    pure xs
termination_by n - i

/-- Execute the increasing-position Fisher–Yates swaps using legal supplied
suffix draws. The two counters record actual draw and swap calls. -/
public def randomlyPermute {α : Type u} {n : Nat} (xs : Vector α n)
    (draws : (i : Fin n) → Fin (n - i.val)) :
    Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n) :=
  scan draws 0 xs

private theorem scan_time {α : Type u} {n : Nat}
    (draws : (i : Fin n) → Fin (n - i.val)) (i : Nat) (xs : Vector α n) :
    (scan draws i xs).time = (n - i, n - i) := by
  rw [scan]
  split_ifs with hi
  · simp only [TimeM.time_bind, TimeM.time_tick]
    rw [scan_time]
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> omega
  · simp only [TimeM.time_pure]
    have h : n - i = 0 := by omega
    rw [h]
    rfl
termination_by n - i
decreasing_by omega

/-- Fisher–Yates executes exactly one draw and one swap at every position,
including the final singleton draw and self-swap. -/
public theorem randomlyPermute_time {α : Type u} {n : Nat} (xs : Vector α n)
    (draws : (i : Fin n) → Fin (n - i.val)) :
    (randomlyPermute xs draws).time = (n, n) := by
  simpa only [randomlyPermute, Nat.sub_zero] using scan_time draws 0 xs

end Cslib.Algorithms.Lean.TimeM
