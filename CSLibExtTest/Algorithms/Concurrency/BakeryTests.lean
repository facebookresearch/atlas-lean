/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Concurrency.Bakery

/-!
# Tests for the bakery algorithm

* Running alone, process `p0` reaches its critical section in six moves, so
  `bakery_mutex` is not vacuous: an infinite run from the initial state exists
  and reaches `cs0`.
* The `choosing` flag blocks: a process waits while the other is choosing.
* Ties are broken by process identity: with equal tickets `p0` enters and `p1`
  waits.
* Tickets grow: after `p0` takes ticket 1, `p1` reads it and takes ticket 2.
* The overlapping-read race, reached from the initial state: both processes
  read `0` and take ticket `1`; the `choosing` flag of `p0` holds `p1` back
  until `p0` has its ticket, then the tie is broken in favour of `p0`.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.Bakery.Tests

open Cslib.LTL

/-- `p0` moving alone. -/
def soloRun (k : ℕ) : State := (step .p0)^[k] initial

theorem soloRun_omegaRun :
    Cslib.LTS.OmegaRun (lts := bakery) soloRun := fun k =>
  ⟨.p0, by simp only [soloRun, Function.iterate_succ_apply']; rfl⟩

example : (soloRun 6).pc .p0 = .critical := rfl

example : (soloRun 5).pc .p0 = .waitNumber := rfl

/-- An infinite run from the initial state on which `p0` reaches its critical
section. -/
example : ExistsRun bakery valuation initial (Formula.eventually (.atom .cs0)) :=
  ⟨soloRun, rfl, soloRun_omegaRun, Satisfies.eventually_iff.mpr ⟨6, Satisfies.atomAt_iff.mpr rfl⟩⟩

/-- `p0` has passed its doorway (`waitChoosing`) while `p1` is choosing. -/
def blocked : State :=
  ⟨fun i => match i with | .p0 => .waitChoosing | .p1 => .write,
    fun i => match i with | .p0 => false | .p1 => true,
    fun i => match i with | .p0 => 1 | .p1 => 0,
    fun i => match i with | .p0 => 0 | .p1 => 1⟩

/-- `p0` waits while `p1` is choosing. -/
example : (step .p0 blocked).pc .p0 = .waitChoosing := rfl

/-- `p1` takes ticket `2`, one more than the ticket of `p0` it read. -/
example : (step .p1 blocked).number .p1 = 2 := rfl

/-- Both processes waiting with equal tickets. -/
def tie : State :=
  ⟨fun _ => .waitNumber, fun _ => false, fun _ => 1, fun _ => 0⟩

/-- `p0` wins the tie. -/
example : (step .p0 tie).pc .p0 = .critical := by
  simp [step, tie, CanEnter, Before, Proc.other]

/-- `p1` loses the tie. -/
example : (step .p1 tie).pc .p1 = .waitNumber := by
  simp [step, tie, CanEnter, Before, Proc.other]

/-- After `p0` takes ticket 1 and finishes choosing, `p1` runs its doorway and
takes ticket 2. -/
example : ((step .p1)^[4] (soloRun 4)).number .p1 = 2 := rfl

/-- The state after the given processes move, in order, from `initial`. -/
def runFrom (movers : List Proc) : State := movers.foldl (fun s i => step i s) initial

/-- `p0` reads `0`; then `p1` reads `0`, takes ticket `1` and finishes choosing. -/
def race : State := runFrom [.p0, .p0, .p1, .p1, .p1, .p1]

example : race.pc .p0 = .write ∧ race.pc .p1 = .waitChoosing ∧ race.number .p1 = 1 := by
  decide

/-- `p1` must wait: `p0` is still choosing. -/
example : (step .p1 race).pc .p1 = .waitChoosing := rfl

/-- `p0` also takes ticket `1`, having read `0` before `p1` wrote. -/
example : (runFrom [.p0, .p0, .p1, .p1, .p1, .p1, .p0]).number .p0 = 1 := rfl

/-- Once `p0` has finished choosing, both wait for the ticket order: the tie
keeps `p1` out and lets `p0` in. -/
example :
    (runFrom [.p0, .p0, .p1, .p1, .p1, .p1, .p0, .p0, .p1, .p1]).pc .p1 = .waitNumber ∧
      (runFrom [.p0, .p0, .p1, .p1, .p1, .p1, .p0, .p0, .p1, .p1, .p0, .p0]).pc .p0 =
        .critical := by
  decide

end Cslib.Algorithms.Concurrency.Bakery.Tests
