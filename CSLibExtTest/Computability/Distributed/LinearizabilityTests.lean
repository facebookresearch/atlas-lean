/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Linearizability

/-!
# Tests for linearizability

* **Well-formed intervals.** No operation record has its response at or before its invocation,
  so the degenerate record with `lo = hi = 0`, for which real-time order would be vacuous, cannot
  be built.
* **Distinct event positions.** `c1` responds at position `2`, where `d2` is invoked, so
  `[c1, d2]` is not a well-formed history and is not linearizable, even when every sequence is
  legal; shifting `d2` to `[3, 4]` (`d2'`) makes the history linearizable.
* **Real-time order on occurrences.** `a1` responds before `b1` is invoked. As lists, the order
  `[a1, a1, b1]` respects real time and `[a1, b1, a1]` does not: the second occurrence of `a1`
  follows `b1`, although the first occurrence precedes it. Neither list is a well-formed history,
  since both repeat the two events of `a1`.
* **A register.** `regSpec` is a register with initial value `0` on every object: a write
  `(0, a, _)` stores `a`, and a read `(1, _, r)` must return the stored value. The read `bad` of
  `3` from a fresh register is not linearizable, so legality is a real constraint.
* **Projection.** The history `hist` writes `5` to object `1`, then `7` to object `2`, then reads
  `5` from object `1`; it is linearizable. Its projection onto object `1` is exactly `[w1, r1]`,
  its projection onto object `3` is empty, and `linearizable_project` makes both linearizable.
* **Boundary.** A one-operation history projects onto its own object unchanged.
-/

@[expose] public section

namespace Cslib.Distributed.Linearizability.Tests

open Cslib.Distributed.Linearizability

/-! ### Well-formed intervals -/

/-- No operation record has its response at its invocation. -/
example : ¬ ∃ r : OpRec, r.lo = r.hi := fun ⟨r, h⟩ => by
  have := r.lo_lt_hi
  omega

/-- In particular the degenerate record with `lo = hi = 0` cannot be built. -/
example (r : OpRec) (h : r.lo = 0) : r.hi ≠ 0 := by
  have := r.lo_lt_hi
  omega

/-! ### Distinct event positions -/

/-- Specification for checks where only the history matters: every sequence is legal. -/
private def specAll : SeqSpec := fun _ _ => True

/-- An operation on object `1` during `[0, 2]`. -/
def c1 : OpRec := ⟨1, 0, 0, 0, 0, 2, by decide⟩

/-- An operation on object `2` invoked at position `2`, where `c1` responds. -/
def d2 : OpRec := ⟨2, 0, 0, 0, 2, 3, by decide⟩

/-- The same operation on object `2`, invoked at position `3` instead. -/
def d2' : OpRec := ⟨2, 0, 0, 0, 3, 4, by decide⟩

/-- `c1` and `d2` share the event position `2`, so `[c1, d2]` is not a well-formed history. -/
example : ¬ WellFormed [c1, d2] := by decide

/-- So `[c1, d2]` is not linearizable, although every sequence is legal under `specAll`. -/
example : ¬ Linearizable specAll [c1, d2] := fun h => absurd h.1 (by decide)

/-- With distinct positions the history is linearizable in its own order. -/
example : Linearizable specAll [c1, d2'] :=
  ⟨by decide, [c1, d2'], List.Perm.refl _, by unfold RespectsRT; decide, fun _ => trivial⟩

/-! ### Real-time order on occurrences -/

/-- An operation on object `1` during `[0, 1]`. -/
def a1 : OpRec := ⟨1, 0, 0, 0, 0, 1, by decide⟩

/-- An operation on object `1` during `[2, 3]`, after `a1` responds. -/
def b1 : OpRec := ⟨1, 0, 0, 0, 2, 3, by decide⟩

/-- Both occurrences of `a1` come before `b1`. -/
example : RespectsRT [a1, a1, b1] := by unfold RespectsRT; decide

/-- The second occurrence of `a1` follows `b1`, so real-time order fails, even though the first
occurrence precedes `b1`. -/
example : ¬ RespectsRT [a1, b1, a1] := by unfold RespectsRT; decide

/-- Repeating `a1` repeats both of its event positions, so `[a1, a1, b1]` is not a well-formed
history and is not linearizable. -/
example : ¬ Linearizable specAll [a1, a1, b1] := fun h => absurd h.1 (by decide)

/-- The same failure through the index form `respectsRT_iff`: position `2` holds `a1`, which
responds before `b1` at position `1` is invoked. -/
example : ¬ ∀ (i j : ℕ) (hi : i < [a1, b1, a1].length) (hj : j < [a1, b1, a1].length),
    [a1, b1, a1][i].hi < [a1, b1, a1][j].lo → i < j := fun h =>
  absurd (h 2 1 (by decide) (by decide) (by decide)) (by decide)

/-! ### A register specification -/

/-- The legal register sequences from the stored value `v`: a write `(0, a, _)` stores `a`, a read
`(1, _, r)` must return `v`, and every other operation is illegal. -/
def regOk : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | _, (0, a, _) :: s => regOk a s
  | v, (1, _, r) :: s => r == v && regOk v s
  | _, _ :: _ => false

/-- A register with initial value `0` on every object. An `abbrev`, so that legality of a concrete
sequence is decidable. -/
abbrev regSpec : SeqSpec := fun _ s => regOk 0 s = true

/-- The empty sequence is legal for every object. -/
theorem regSpec_nil (o : ℕ) : regSpec o [] := rfl

/-- A read of `3` from object `1`, which still holds `0`. -/
def bad : OpRec := ⟨1, 1, 0, 3, 0, 1, by decide⟩

/-- The read `bad` is illegal, so the one-operation history `[bad]` is not linearizable. -/
theorem not_linearizable_bad : ¬ Linearizable regSpec [bad] := by
  rintro ⟨-, lin, hperm, -, hleg⟩
  rw [List.perm_singleton.mp hperm] at hleg
  exact absurd (hleg 1) (by decide)

/-! ### A two-object history and its projections -/

/-- Write `5` to object `1` during `[0, 1]`. -/
def w1 : OpRec := ⟨1, 0, 5, 0, 0, 1, by decide⟩

/-- Write `7` to object `2` during `[2, 3]`. -/
def w2 : OpRec := ⟨2, 0, 7, 0, 2, 3, by decide⟩

/-- Read `5` from object `1` during `[4, 5]`. -/
def r1 : OpRec := ⟨1, 1, 0, 5, 4, 5, by decide⟩

/-- The three operations, one after another. -/
def hist : List OpRec := [w1, w2, r1]

/-- The history is linearizable in its own order: each earlier operation responds before each
later one is invoked, and every object sees a legal register sequence. -/
theorem linearizable_hist : Linearizable regSpec hist := by
  refine ⟨by decide, hist, List.Perm.refl _, by unfold RespectsRT; decide, ?_⟩
  intro o
  by_cases h1 : o = 1
  · subst h1; decide
  by_cases h2 : o = 2
  · subst h2; decide
  simp [regSpec, regOk, hist, w1, w2, r1, Ne.symm h1, Ne.symm h2]

/-- The projection onto object `1` keeps exactly its write and its read, in order. -/
theorem proj_hist_one : proj hist 1 = [w1, r1] := by decide

/-- The projection onto object `2` keeps exactly its write. -/
theorem proj_hist_two : proj hist 2 = [w2] := by decide

/-- The projection onto object `3` is empty. -/
theorem proj_hist_three : proj hist 3 = [] := by decide

/-- `linearizable_project` on object `1`: the read still follows the write it returns. -/
example : Linearizable regSpec [w1, r1] :=
  proj_hist_one ▸ linearizable_project regSpec regSpec_nil hist 1 linearizable_hist

/-- `linearizable_project` on object `3`: the empty projection is linearizable because the empty
sequence is legal. -/
example : Linearizable regSpec [] :=
  proj_hist_three ▸ linearizable_project regSpec regSpec_nil hist 3 linearizable_hist

/-! ### Boundary -/

/-- Boundary check: a one-operation history on object 1 is linearizable, so its projection to
object 1 is too. -/
example : Linearizable specAll (proj [⟨1, 5, 6, 7, 0, 1, by decide⟩] 1) := by
  apply linearizable_project specAll (fun _ => trivial)
  exact ⟨by decide, [⟨1, 5, 6, 7, 0, 1, by decide⟩], List.Perm.refl _,
    List.pairwise_singleton _ _, fun _ => trivial⟩

end Cslib.Distributed.Linearizability.Tests
