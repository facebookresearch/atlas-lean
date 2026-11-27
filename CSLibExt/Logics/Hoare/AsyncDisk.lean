/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fin.Basic

/-!
# The asynchronous disk model of Crash Hoare Logic

A block stores its latest value and a finite set of previous values that might persist across
a crash. A successful sync makes the latest values durable at all blocks. Crash outcomes choose
one whole value at each present block, independently of the choices at other blocks, and clear
all histories. Recovery may then run on that disk; its behavior is supplied separately.

Source: Chen et al., *Using Crash Hoare Logic for Certifying the FSCQ File System*, SOSP 2015,
§§3.2 and 3.4 and Figure 3. We model a completed global sync, not the per-address sync used
for local reasoning in §5.2. We do not model additional crashes during recovery.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Hoare.AsyncDisk

/-- The latest value of a block and the finite set of earlier possible persistent values. -/
structure Block (Value : Type*) where
  latest : Value
  previous : Finset Value

/-- A bounded disk can leave some in-range addresses unallocated. -/
abbrev Disk (size : ℕ) (Value : Type*) := Fin size → Option (Block Value)

variable {size : ℕ} {Value : Type*}

/-- A normal read returns the latest value, or fails at a missing or out-of-range address. -/
def read (disk : Disk size Value) (address : ℕ) : Option Value :=
  if h : address < size then (disk ⟨address, h⟩).map Block.latest else none

/-- A successful write replaces the entire block value and retains the old latest value in the
history. All other cells are unchanged. A write at a missing or out-of-range address fails. -/
def write [DecidableEq Value] (disk : Disk size Value) (address : ℕ) (value : Value) :
    Option (Disk size Value) :=
  if h : address < size then
    match disk ⟨address, h⟩ with
    | none => none
    | some b => some (Function.update disk ⟨address, h⟩
        (some ⟨value, insert b.latest b.previous⟩))
  else none

/-- A completed global sync retains each block's latest value and discards all earlier values. -/
def sync (disk : Disk size Value) : Disk size Value :=
  fun i => (disk i).map fun b => ⟨b.latest, ∅⟩

/-- At a present address, a crash leaves either the latest whole value or one of the earlier
whole values, and discards the history. A missing cell stays missing. -/
def CrashCell : Option (Block Value) → Option (Block Value) → Prop
  | none, post => post = none
  | some b, post => ∃ v, (v = b.latest ∨ v ∈ b.previous) ∧ post = some ⟨v, ∅⟩

/-- A disk crash is a pointwise choice of legal cell outcomes. The disk size and allocation
are preserved; there is no shared choice or ordering constraint across addresses. -/
def Crash (before after : Disk size Value) : Prop :=
  ∀ i, CrashCell (before i) (after i)

/-- Run a supplied recovery relation on the disk produced by one crash. -/
def CrashThenRecover (recovery : Disk size Value → Disk size Value → Prop)
    (before after : Disk size Value) : Prop :=
  ∃ crashed, Crash before crashed ∧ recovery crashed after

/-- It is always possible for all latest values to persist, with no remaining history. -/
theorem crash_to_sync (disk : Disk size Value) : Crash disk (sync disk) := by
  intro i
  cases h : disk i with
  | none => simp [CrashCell, sync, h]
  | some b =>
      exact ⟨b.latest, Or.inl rfl, by simp [sync, h]⟩

/-- Once sync has completed, a crash has exactly one outcome: the synced disk itself. -/
theorem crash_sync_iff (disk result : Disk size Value) :
    Crash (sync disk) result ↔ result = sync disk := by
  have hs (i : Fin size) : CrashCell (sync disk i) (result i) ↔ result i = sync disk i := by
    cases h : disk i <;> simp [sync, CrashCell, h]
  exact ⟨fun h => funext fun i => (hs i).mp (h i),
    fun h i => (hs i).mpr (congrFun h i)⟩

end Cslib.Hoare.AsyncDisk
