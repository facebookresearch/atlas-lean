/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic

@[expose] public section

open Finset

/-- A synchronous PRAM program step with `p` processors on
shared memory `ℕ → α`: processor `i` reads `readAddr i`,
computes `compute i` of the value read, and optionally writes
the result to `writeAddr i`. -/
structure PramProg (α : Type*) (p : ℕ) where
  readAddr : Fin p → ℕ
  compute : Fin p → α → α
  writeAddr : Fin p → Option ℕ

/-- The processors writing to address `a` in step `s`. -/
def writers {α : Type*} {p : ℕ} (s : PramProg α p) (a : ℕ) :
    Finset (Fin p) :=
  Finset.univ.filter (fun i => s.writeAddr i = some a)

/-- The value processor `i` would write. -/
def writeVal {α : Type*} {p : ℕ} (mem : ℕ → α) (s : PramProg α p)
    (i : Fin p) : α :=
  s.compute i (mem (s.readAddr i))

/-- The total CRCW step function: a written cell takes the
least-index writer's value; an unwritten cell is unchanged.
On steps legal for Common (all writers agree) or for CREW
(at most one writer), this is the semantics of the discipline. -/
def stepCRCW {α : Type*} {p : ℕ} (mem : ℕ → α) (s : PramProg α p)
    (a : ℕ) : α :=
  if h : (writers s a).Nonempty then
    writeVal mem s ((writers s a).min' h)
  else mem a

/-- EREW legality: no two processors read the same cell, and
no two write the same cell. -/
def EREW {α : Type*} {p : ℕ} (s : PramProg α p) : Prop :=
  Function.Injective s.readAddr ∧
    ∀ i j, s.writeAddr i = s.writeAddr j →
      s.writeAddr i = none ∨ i = j

/-- CREW legality: concurrent reads allowed, writes exclusive. -/
def CREW {α : Type*} {p : ℕ} (s : PramProg α p) : Prop :=
  ∀ i j, s.writeAddr i = s.writeAddr j →
    s.writeAddr i = none ∨ i = j

/-- CRCW-Common legality: all writers to a cell computed the
same value. -/
def CommonLegal {α : Type*} {p : ℕ} (mem : ℕ → α)
    (s : PramProg α p) : Prop :=
  ∀ a, ∀ i ∈ writers s a, ∀ j ∈ writers s a,
    writeVal mem s i = writeVal mem s j

/-- An EREW-legal step is CREW-legal. -/
theorem EREW.crew {α : Type*} {p : ℕ} {s : PramProg α p}
    (h : EREW s) : CREW s := by
  exact h.2

/-- On a CREW-legal step, the cell written by processor `i`
takes `i`'s value. -/
theorem stepCRCW_of_crew {α : Type*} {p : ℕ} (mem : ℕ → α)
    {s : PramProg α p} (h : CREW s) {i : Fin p} {a : ℕ}
    (hi : s.writeAddr i = some a) :
    stepCRCW mem s a = writeVal mem s i := by
  have hmem : i ∈ writers s a := by
    simp only [writers, Finset.mem_filter, Finset.mem_univ, true_and, hi]
  have hne : (writers s a).Nonempty := ⟨i, hmem⟩
  have hmin_mem : (writers s a).min' hne ∈ writers s a :=
    Finset.min'_mem _ hne
  have hmin_addr : s.writeAddr ((writers s a).min' hne) = some a := by
    simp only [writers, Finset.mem_filter, Finset.mem_univ, true_and] at hmin_mem
    exact hmin_mem
  have heq : (writers s a).min' hne = i := by
    have hdisj := h _ _ (Eq.trans hmin_addr hi.symm)
    cases hdisj with
    | inl hnone =>
      rw [hmin_addr] at hnone
      simp at hnone
    | inr heq => exact heq
  unfold stepCRCW
  rw [dite_eq_left hne, heq]

/-- On a Common-legal step, the cell written by processor `i`
takes `i`'s value. -/
theorem stepCRCW_of_common {α : Type*} {p : ℕ} (mem : ℕ → α)
    {s : PramProg α p} (h : CommonLegal mem s) {i : Fin p}
    {a : ℕ} (hi : s.writeAddr i = some a) :
    stepCRCW mem s a = writeVal mem s i := by
  have hmem : i ∈ writers s a := by
    simp only [writers, Finset.mem_filter, Finset.mem_univ, true_and, hi]
  have hne : (writers s a).Nonempty := ⟨i, hmem⟩
  have hmin_mem : (writers s a).min' hne ∈ writers s a :=
    Finset.min'_mem _ hne
  unfold stepCRCW
  rw [dite_eq_left hne]
  exact h a _ hmin_mem _ hmem

/-- An unwritten cell is unchanged. -/
theorem stepCRCW_of_no_writer {α : Type*} {p : ℕ} (mem : ℕ → α)
    {s : PramProg α p} {a : ℕ}
    (h : ∀ i, s.writeAddr i ≠ some a) :
    stepCRCW mem s a = mem a := by
  have hempty : writers s a = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    simp only [writers, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact h i hi
  have hnot : ¬ (writers s a).Nonempty := by
    rw [hempty]
    simp
  unfold stepCRCW
  rw [dite_eq_right hnot]

/-- Wyllie pointer jumping, one round, as a PRAM step
specialized to the current memory `ptr`: processor `i` reads
the cell `ptr i` its pointer names and writes the value found
there back to cell `i`, for `i < n`. -/
def pointerJumpStep (ptr : ℕ → ℕ) (n : ℕ) : PramProg ℕ n where
  readAddr i := ptr i
  compute _ v := v
  writeAddr i := some i

/-- One pointer-jumping round under the CRCW step: cell `i`
takes the value of the cell its pointer names, i.e. the new
memory is `ptr ∘ ptr` on cells below `n` and unchanged above.
The step is CREW (each cell has exactly one writer), so this
is also the CREW reading of the round. -/
theorem pointerJump_apply (ptr : ℕ → ℕ) (n : ℕ) :
    ∀ a, stepCRCW ptr (pointerJumpStep ptr n) a =
      if a < n then ptr (ptr a) else ptr a := by
  intro a
  by_cases ha : a < n
  · have hcrew : CREW (pointerJumpStep ptr n) := by
      intro i j hij
      right
      simp only [pointerJumpStep, Option.some_inj, Fin.ext_iff] at hij ⊢
      exact hij
    have hi : (pointerJumpStep ptr n).writeAddr ⟨a, ha⟩ = some a := rfl
    have hstep := stepCRCW_of_crew ptr hcrew hi
    rw [hstep]
    have hval : writeVal ptr (pointerJumpStep ptr n) ⟨a, ha⟩ = ptr (ptr a) := by
      simp only [writeVal, pointerJumpStep]
    rw [hval]
    simp [ha]
  · have hno : ∀ i : Fin n, (pointerJumpStep ptr n).writeAddr i ≠ some a := by
      intro i hi
      simp only [pointerJumpStep, Option.some_inj] at hi
      have hlt : (i : ℕ) < n := Fin.is_lt i
      omega
    rw [stepCRCW_of_no_writer _ hno]
    simp [ha]
