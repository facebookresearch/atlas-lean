/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.CDCL.Termination

/-!
# Tests for CDCL termination

* One decide step from the empty state, in the universe `vars = {0}`, `clauses = ∅`: the
  potential drops from `1` to `0`.
* A conflict step with backjumping: against `F = [[(0, false)]]`, after deciding `(0, true)` the
  solver learns `[(0, false)]` and backjumps to the empty trail. In the universe `vars = {0}`,
  `clauses = {[(0, false)]}` the potential drops from `2` to `1` although the trail got shorter.
-/

@[expose] public section

namespace Cslib.Algorithms.SAT.CDCL.Tests

open Cslib.Logic.PL

/-- One decide step from the empty state: the potential drops from `1` to `0`. -/
example : 0 * (1 + 1) + (1 - 1) < 0 * (1 + 1) + (1 - 0) :=
  cdcl_step_potential_decreases (F := []) ({0} : Finset ℕ) ∅
    (s₁ := ([], ∅)) (s₂ := ([(0, true)], ∅))
    (CDCLStep.decide [] ∅ (0, true) (by simp) (by simp))
    (by simp) (by simp) (by simp) (by simp) (by simp)

/-- The clause `[(0, false)]` of `F = [[(0, false)]]` is implied by `F`. -/
theorem impliedBy_unit : ImpliedBy [[(0, false)]] [(0, false)] :=
  fun _ hF => hF _ List.mem_cons_self

/-- Learning `[(0, false)]` after the decision `(0, true)` and backjumping to the empty trail:
the potential drops from `2` to `1`. -/
example : (1 - 1) * (1 + 1) + (1 - 0) < (1 - 0) * (1 + 1) + (1 - 1) :=
  cdcl_step_potential_decreases (F := [[(0, false)]]) ({0} : Finset ℕ) {[(0, false)]}
    (s₁ := ([(0, true)], ∅)) (s₂ := ([], {[(0, false)]}))
    (CDCLStep.learn [(0, true)] [] ∅ [(0, false)] impliedBy_unit (by simp) List.nil_suffix)
    (by simp) (by simp) (by simp) (by simp) (by simp)

end Cslib.Algorithms.SAT.CDCL.Tests
