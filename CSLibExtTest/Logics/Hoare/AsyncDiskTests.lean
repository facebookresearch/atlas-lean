/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Hoare.AsyncDisk

/-! # Regressions for the asynchronous disk model -/

set_option autoImplicit false

namespace Cslib.Hoare.AsyncDisk.Tests

private def disk : Disk 3 ℕ := fun i =>
  if i = 0 then some ⟨10, {7}⟩ else if i = 1 then some ⟨20, {18}⟩ else none

private def written : Disk 3 ℕ :=
  Function.update disk 0 (some ⟨12, insert 10 {7}⟩)

-- Normal reads see the latest value. A write retains both the old latest and earlier values.
example : read disk 0 = some 10 ∧ write disk 0 12 = some written ∧
    read written 0 = some 12 ∧ read written 1 = some 20 :=
  ⟨rfl, rfl, rfl, rfl⟩

-- Missing in-range and out-of-range addresses both fail; writing does not allocate.
example : read disk 2 = none ∧ read disk 3 = none ∧
    write disk 2 99 = none ∧ write disk 3 99 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

private def mixed : Disk 3 ℕ := fun i =>
  if i = 0 then some ⟨7, ∅⟩ else if i = 1 then some ⟨20, ∅⟩ else none

-- One block can retain an earlier value while another keeps its latest, with no history left.
private theorem mixed_crash : Crash written mixed := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · change ∃ v : ℕ, (v = 12 ∨ v ∈ insert 10 ({7} : Finset ℕ)) ∧
      some (Block.mk 7 ∅) = some (Block.mk v ∅)
    exact ⟨7, Or.inr (Finset.mem_insert_of_mem (Finset.mem_singleton_self 7)), rfl⟩
  · exact ⟨20, Or.inl rfl, rfl⟩
  · rfl

example : ¬ Crash (sync written) mixed := by
  intro h
  have he := (crash_sync_iff written mixed).mp h
  have hr := congrArg (fun d => read d 0) he
  change some 7 = some 12 at hr
  exact (by decide : (some 7 : Option ℕ) ≠ some 12) hr

private def repaired : Disk 3 ℕ := Function.update mixed 0 (some ⟨30, insert 7 ∅⟩)

-- Recovery sees the value selected by the crash, not the value visible before the crash.
example : CrashThenRecover (fun d result => read d 0 = some 7 ∧ write d 0 30 = some result)
    written repaired :=
  ⟨mixed, mixed_crash, rfl, rfl⟩

end Cslib.Hoare.AsyncDisk.Tests
