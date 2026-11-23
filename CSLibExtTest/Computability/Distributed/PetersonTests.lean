/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Peterson

/-!
# Tests for Peterson's algorithm

* Both initial turns give reachable, noncritical initial states.
* Without contention, process `0` enters its critical section, leaves it, and lowers its flag.
* Under contention the process that assigned `turn` last is blocked while the other process
  enters, stays blocked while it is critical, and enters after it lowers its flag.
* `mutual_exclusion` rules out the critical stage for the other process, and rules out a
  concrete state with both processes critical.
-/

@[expose] public section

namespace Cslib.Distributed.Peterson.Tests

/-! ### Initial states -/

example : Reachable (init 0) := reachable_init 0

example : Reachable (init 1) := reachable_init 1

/-- Initial states are idle with both flags down, whatever the turn. -/
example (t : Fin 2) (i : Fin 2) : (init t).pc i = .idle ∧ (init t).flag i = false :=
  ⟨rfl, rfl⟩

/-! ### Entry and exit without contention, from initial turn `1` -/

/-- Process `0` raises its flag, gives priority to process `1`, and enters, since the flag of
process `1` is down. -/
def soloCritical : State := step 0 (step 0 (step 0 (init 1)))

example : Reachable soloCritical :=
  (((reachable_init 1).step 0).step 0).step 0

example : soloCritical.pc 0 = .critical ∧ soloCritical.flag 0 = true ∧
    soloCritical.turn = 1 := by
  decide

/-- Leaving the critical section and lowering the flag returns process `0` to idle. -/
example : (step 0 (step 0 soloCritical)).pc 0 = .idle ∧
    (step 0 (step 0 soloCritical)).flag 0 = false := by
  decide

/-! ### Contention, from initial turn `0` -/

/-- Both processes raise their flags, then process `0` and then process `1` assign `turn`;
process `1` assigned it last, so `turn = 0` and both are waiting. -/
def contended : State := step 1 (step 0 (step 1 (step 0 (init 0))))

theorem reachable_contended : Reachable contended :=
  ((((reachable_init 0).step 0).step 1).step 0).step 1

example : contended.pc 0 = .waiting ∧ contended.pc 1 = .waiting ∧ contended.turn = 0 := by
  decide

/-- Process `1` is blocked: its step leaves the state unchanged. -/
example : step 1 contended = contended := rfl

/-- Process `0` enters its critical section. -/
def zeroCritical : State := step 0 contended

example : zeroCritical.pc 0 = .critical ∧ zeroCritical.pc 1 = .waiting := by
  decide

/-- Process `1` stays blocked while process `0` is critical. -/
example : step 1 zeroCritical = zeroCritical := rfl

/-- Once process `0` leaves and lowers its flag, process `1` enters. -/
example : (step 1 (step 0 (step 0 zeroCritical))).pc 1 = .critical ∧
    (step 1 (step 0 (step 0 zeroCritical))).pc 0 = .idle := by
  decide

/-! ### The safety theorem -/

/-- While process `0` is critical in the contended run, process `1` is not. -/
example : zeroCritical.pc 1 ≠ .critical := fun h1 =>
  mutual_exclusion zeroCritical (reachable_contended.step 0) ⟨by decide, h1⟩

/-- In every reachable state, a critical process `0` excludes process `1`. -/
example (s : State) (hs : Reachable s) (h0 : s.pc 0 = .critical) : s.pc 1 ≠ .critical :=
  fun h1 => mutual_exclusion s hs ⟨h0, h1⟩

/-- A state with both processes critical is unreachable. -/
example : ¬ Reachable ⟨fun _ => .critical, fun _ => true, 0⟩ := fun h =>
  mutual_exclusion _ h ⟨rfl, rfl⟩

end Cslib.Distributed.Peterson.Tests

end
