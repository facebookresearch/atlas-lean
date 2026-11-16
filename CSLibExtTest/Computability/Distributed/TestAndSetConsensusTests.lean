/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.TestAndSetConsensus

/-!
# Tests for test-and-set consensus

Process `0` proposes `10` and process `1` proposes `20`.

* Process `0` wins when it runs to completion first: after two steps it is about to decide its
  own input, and both processes decide `10`.
* Process `1` wins after both registers are written: process `0` loses, reads the register of
  process `1`, and both processes decide `20`.
* A process that has taken fewer than three steps may be undecided.
* `safety` and `decision_isSome_of_three_le_count` apply to both executions of `lts`.
-/

@[expose] public section

namespace Cslib.Distributed.TestAndSetConsensus.Tests

/-- The inputs: process `0` proposes `10` and process `1` proposes `20`. -/
def inp (i : Fin 2) : ℕ := if i = 0 then 10 else 20

/-! ### Process `0` wins -/

/-- Process `0` writes, wins the test-and-set, and decides; then process `1` writes, loses, and
reads. -/
def σ₀ : List (Fin 2) := [0, 0, 0, 1, 1, 1]

/-- After its write and its test-and-set, process `0` has won and is about to decide its own
input; the bit is set and process `1` has not started. -/
example : (run inp [0, 0]).pc 0 = .decideOwn ∧ (run inp [0, 0]).tas = true ∧
    (run inp [0, 0]).pc 1 = .write ∧ (run inp [0, 0]).decision 0 = none := by
  decide

/-- Process `1` loses the test-and-set and is about to read the register of process `0`. -/
example : (run inp [0, 0, 0, 1, 1]).pc 1 = .readOther := by
  decide

/-- Both processes decide the input `10` of process `0`. -/
example : (run inp σ₀).decision 0 = some 10 ∧ (run inp σ₀).decision 1 = some 10 := by
  decide

/-! ### Process `1` wins after both registers are written -/

/-- Process `0` writes, process `1` writes and wins the test-and-set, process `0` loses and
reads, and process `1` decides. -/
def σ₁ : List (Fin 2) := [0, 1, 1, 0, 0, 1]

/-- After both writes and the test-and-set of process `1`, process `1` has won, and the
test-and-set of process `0` then loses. -/
example : (run inp [0, 1, 1]).pc 1 = .decideOwn ∧ (run inp [0, 1, 1, 0]).pc 0 = .readOther := by
  decide

/-- The loser decides first, reading the input `20` of process `1`, while the winner has not yet
decided. -/
example : (run inp [0, 1, 1, 0, 0]).decision 0 = some 20 ∧
    (run inp [0, 1, 1, 0, 0]).decision 1 = none := by
  decide

/-- Both processes decide the input `20` of process `1`. -/
example : (run inp σ₁).decision 0 = some 20 ∧ (run inp σ₁).decision 1 = some 20 := by
  decide

/-! ### The safety and termination theorems on these executions -/

example : ∀ i j x y, (run inp σ₀).decision i = some x → (run inp σ₀).decision j = some y →
    x = y :=
  (safety inp _ (reachable_run inp σ₀)).1

example : ∀ i x, (run inp σ₁).decision i = some x → ∃ w, x = inp w :=
  (safety inp _ (reachable_run inp σ₁)).2

/-- The executions of `lts` along `σ₀` and `σ₁` end in `run inp σ₀` and `run inp σ₁`. -/
theorem mTr_σ₀ : (lts inp).MTr init σ₀ (run inp σ₀) := mTr_iff_eq_run.mpr rfl

theorem mTr_σ₁ : (lts inp).MTr init σ₁ (run inp σ₁) := mTr_iff_eq_run.mpr rfl

/-- Each process took three steps in `σ₀` and `σ₁`, so each has decided. -/
example (i : Fin 2) : ((run inp σ₀).decision i).isSome ∧ ((run inp σ₁).decision i).isSome :=
  ⟨decision_isSome_of_three_le_count mTr_σ₀ i (by revert i; decide),
    decision_isSome_of_three_le_count mTr_σ₁ i (by revert i; decide)⟩

/-- The bound of three steps is not vacuous: process `0` has taken two steps of `[0, 0]` and has
not decided. -/
example : ((run inp [0, 0]).decision 0).isSome = false := by
  decide

end Cslib.Distributed.TestAndSetConsensus.Tests

end
