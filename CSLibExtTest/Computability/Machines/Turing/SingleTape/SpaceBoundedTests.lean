/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.SpaceBounded
public import CSLibExtTest.Computability.Machines.Turing.SingleTape.ClassesTests
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Tests for space-bounded single-tape machines

Small machines: `scanRight`, which scans right over its input and halts on the first blank, is a
linear bounded automaton that halts on every input; `loopForever` (from `ClassesTests`) is a
linear bounded automaton that never halts, whose halting set is still computable; `eraseRight`,
which erases its input, is a linear bounded automaton by the criterion `isLBA_of_stays_on_blank`
alone; `writeRight`, which walks right writing `true` forever, runs in no space bound at all. The
decidability theorems are applied to the automata.
-/

set_option autoImplicit false

open Relation Computability Cslib.Turing Cslib.Decidability

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape

/-! ### A linear bounded automaton that halts -/

/-- Scan right over the input and halt on the first blank. -/
def scanRight : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _
    | some b => (⟨some b, some .right⟩, some ())
    | none => (⟨none, none⟩, none)

/-- The invariant of `scanRight` on an input of length `n`: on a symbol, the cells around the head
fit in `n` cells and the right half has no blank; on a blank, the right half is empty and the left
half has at most `n` cells. -/
private def ScanInv (n : ℕ) (t : BiTape Bool) : Prop :=
  match t.head with
  | some _ => t.left.length + t.right.length + 1 ≤ n ∧ none ∉ t.right.toList
  | none => t.left.length ≤ n ∧ t.right.toList = []

/-- The run of `scanRight` keeps `ScanInv`. -/
private theorem scanInv_of_reflTransGen {l : List Bool} {c : scanRight.Cfg}
    (h : ReflTransGen scanRight.TransitionRelation (scanRight.initCfg l) c) :
    ScanInv l.length c.BiTape := by
  induction h with
  | refl =>
    cases l with
    | nil => exact ⟨le_rfl, rfl⟩
    | cons a t => simp [ScanInv, SingleTapeTM.initCfg, BiTape.mk₁, StackTape.mapSome,
        StackTape.length, StackTape.nil]
  | tail _ hstep ih =>
    rename_i b d _
    obtain ⟨_ | q, ⟨_ | a, L, ⟨_ | ⟨x, r⟩, hR⟩⟩⟩ := b <;>
      simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step, scanRight,
        reduceCtorEq] at hstep <;> obtain rfl := Option.some_injective _ hstep
    · exact ih
    · exact ih
    · simp only [ScanInv, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight,
        StackTape.head, StackTape.length_cons_some, StackTape.toList_tail] at ih ⊢
      exact ⟨by omega, rfl⟩
    · obtain ⟨hlen, hnone⟩ := ih
      obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.mp fun hx ↦ hnone (hx ▸ List.mem_cons_self)
      simp only [ScanInv, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight,
        StackTape.head, StackTape.cons_some_toList, StackTape.toList_tail, StackTape.length,
        List.length_cons, List.tail_cons, List.mem_cons, not_or] at hlen hnone ⊢
      exact ⟨by omega, hnone.2⟩

/-- `scanRight` is a linear bounded automaton: it uses one cell beyond the input, the blank where
it halts. -/
theorem scanRight_isLBA : scanRight.IsLBA := by
  intro l c hc
  have := scanInv_of_reflTransGen hc
  simp only [SingleTapeTM.Cfg.spaceUsed, BiTape.spaceUsed]
  unfold ScanInv at this
  split at this
  · omega
  · obtain ⟨h1, h2⟩ := this
    simp only [StackTape.length, h2, List.length_nil] at h1 ⊢
    omega

/-- `scanRight` needs the extra cell of `IsLBA`: on `[true]` it steps onto the blank after the
input, a configuration of space `2`, so it does not run in the space `max 1 n` of its input. -/
example : ¬scanRight.SpaceBoundedBy (max 1 ·) := fun h ↦
  absurd (h [true] _ (.single rfl)) (by decide)

/-- No machine runs in space `n`: the empty input already uses one cell. -/
example (tm : SingleTapeTM Bool) : ¬tm.SpaceBoundedBy id := fun h ↦
  absurd (h.max_one_le []) (by decide)

/-- `scanRight` halts on `[true, false]`. -/
theorem scanRight_haltsOn : scanRight.HaltsOn [true, false] :=
  ⟨_, .head rfl (.head rfl (.head rfl .refl)), rfl⟩

/-- The pigeonhole bound on `[true, false]`. -/
example : ∃ c : scanRight.Cfg, RelatesWithinSteps scanRight.TransitionRelation
    (scanRight.initCfg [true, false]) c (scanRight.cfgBound 3) ∧ c.state = none :=
  scanRight_isLBA.exists_halted_relatesWithinSteps scanRight_haltsOn

/-- The halting set of `scanRight` is computable. -/
example : ComputablePred scanRight.HaltsOn :=
  scanRight_isLBA.computablePred_haltsOn

/-- The halting set of `scanRight` is computable through a weaker, quadratic space bound. -/
example : ComputablePred scanRight.HaltsOn :=
  (scanRight_isLBA.mono fun n ↦ by nlinarith).computablePred_haltsOn (s := fun n ↦ n * n + 1)
    (Primrec.succ.comp (Primrec.nat_mul.comp Primrec.id Primrec.id)).to_comp

/-! ### A linear bounded automaton that never halts -/

/-- `loopForever` never changes its tape. -/
theorem loopForever_bitape {l : List Bool} {c : loopForever.Cfg}
    (h : ReflTransGen loopForever.TransitionRelation (loopForever.initCfg l) c) :
    c.BiTape = BiTape.mk₁ l := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rename_i b d _
    obtain ⟨_ | q, t⟩ := b
    · simp [SingleTapeTM.TransitionRelation] at hstep
    · simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step, loopForever] at hstep
      obtain rfl := Option.some_injective _ hstep
      exact ih

/-- `loopForever` is a linear bounded automaton. -/
theorem loopForever_isLBA : loopForever.IsLBA := fun l c hc ↦ by
  have := SingleTapeTM.Cfg.spaceUsed_initCfg loopForever l
  simp only [SingleTapeTM.Cfg.spaceUsed, SingleTapeTM.initCfg, loopForever_bitape hc] at this ⊢
  omega

/-! ### The criterion `isLBA_of_stays_on_blank` -/

/-- `scanRight` halts on a blank, writing a blank and not moving: the criterion applies. -/
example : scanRight.IsLBA :=
  SingleTapeTM.isLBA_of_stays_on_blank fun _ ↦ rfl

/-- `loopForever` neither writes nor moves on any cell: the criterion applies. -/
example : loopForever.IsLBA :=
  SingleTapeTM.isLBA_of_stays_on_blank fun _ ↦ rfl

/-- Erase the input from left to right and halt on the blank after it. -/
def eraseRight : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _
    | some _ => (⟨none, some .right⟩, some ())
    | none => (⟨none, none⟩, none)

/-- `eraseRight` is a linear bounded automaton by the criterion alone, with no invariant proved
by hand. -/
theorem eraseRight_isLBA : eraseRight.IsLBA :=
  SingleTapeTM.isLBA_of_stays_on_blank fun _ ↦ rfl

/-- `eraseRight` halts on `[true, false]` in three steps, leaving a blank tape. -/
example : eraseRight.Outputs [true, false] [] :=
  .head rfl (.head rfl (.head rfl .refl))

/-- The halting set of `eraseRight` is computable. -/
example : ComputablePred eraseRight.HaltsOn :=
  eraseRight_isLBA.computablePred_haltsOn

/-- The halting set of `loopForever`, an LBA that never halts, is computable. -/
example : ComputablePred loopForever.HaltsOn :=
  loopForever_isLBA.computablePred_haltsOn

/-- Halting of `loopForever` on binary codes of natural numbers is computable, and decided by a
single-tape machine. -/
example : (ComputablePred fun n : ℕ ↦ loopForever.HaltsOn ((encodeNat (Encodable.encode n)).map id))
    ∧ SingleTapeDecidable fun n : ℕ ↦
      loopForever.HaltsOn ((encodeNat (Encodable.encode n)).map not) :=
  ⟨loopForever_isLBA.computablePred_haltsOn_encodeNat id,
    loopForever_isLBA.singleTapeDecidable_haltsOn_encodeNat not⟩

/-- Halting of `scanRight` on binary codes of lists, written through `not`, is decided by a
single-tape machine. -/
example : SingleTapeDecidable fun w : List Bool ↦
    scanRight.HaltsOn ((encodeNat (Encodable.encode w)).map not) :=
  scanRight_isLBA.singleTapeDecidable_haltsOn_encodeNat not

/-! ### A machine that runs in no space bound -/

/-- Walk right forever, writing `true`. -/
def writeRight : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨some true, some .right⟩, some ())

/-- `writeRight` writes and moves on a blank, so `isLBA_of_stays_on_blank` does not apply. -/
example : ¬∀ q, (writeRight.tr q none).1 = ⟨none, none⟩ := fun h ↦
  absurd (h ()) (by simp [writeRight])

/-- `writeRight` is not a linear bounded automaton: one step on the empty input uses two cells. -/
theorem not_writeRight_isLBA : ¬writeRight.IsLBA := fun h ↦
  absurd (h [] _ (.single rfl)) (by decide)

/-- The configuration of `writeRight` after `k` steps on the empty input: `k` cells of `true` to
the left of the head, which is on a blank. -/
def writeRightCfg (k : ℕ) : writeRight.Cfg :=
  ⟨some (), ⟨none, ⟨List.replicate k (some true), by cases k <;> simp [List.getLast?_replicate]⟩,
    StackTape.nil⟩⟩

/-- `writeRight` steps from `writeRightCfg k` to `writeRightCfg (k + 1)`. -/
theorem writeRight_step (k : ℕ) :
    writeRight.TransitionRelation (writeRightCfg k) (writeRightCfg (k + 1)) := by
  simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step, writeRight, writeRightCfg,
    BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight, Option.some.injEq,
    SingleTapeTM.Cfg.mk.injEq, BiTape.mk.injEq, true_and]
  refine ⟨rfl, ?_, rfl⟩
  rw [StackTape.mk.injEq]
  rfl

/-- `writeRight` runs in no space bound. -/
theorem not_writeRight_spaceBoundedBy (s : ℕ → ℕ) : ¬writeRight.SpaceBoundedBy s := by
  intro h
  have hreach (k : ℕ) :
      ReflTransGen writeRight.TransitionRelation (writeRight.initCfg []) (writeRightCfg k) := by
    induction k with
    | zero => rfl
    | succ k ih => exact ih.tail (writeRight_step k)
  have := h [] _ (hreach (s 0))
  simp [SingleTapeTM.Cfg.spaceUsed, BiTape.spaceUsed, writeRightCfg, StackTape.length,
    StackTape.nil] at this

/-- `writeRight` never halts, so its halting set is computable even though no space bound
applies: space bounds are sufficient for decidability, not necessary. -/
example : ComputablePred writeRight.HaltsOn := by
  refine (Computable.computablePred (p := fun _ : List Bool ↦ False) (Computable.const false)).of_eq
    fun l ↦ ⟨False.elim, ?_⟩
  rintro ⟨c, hc, hhalt⟩
  have key : ∀ c : writeRight.Cfg, ReflTransGen writeRight.TransitionRelation
      (writeRight.initCfg l) c → c.state = some () := by
    intro c hc
    induction hc with
    | refl => rfl
    | tail _ hstep ih =>
      rename_i b d _
      obtain ⟨_ | q, t⟩ := b
      · cases ih
      · simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step, writeRight] at hstep
        obtain rfl := Option.some_injective _ hstep
        rfl
  rw [key c hc] at hhalt
  cases hhalt

end CSLibExtTest.Computability.Machines.Turing.SingleTape
