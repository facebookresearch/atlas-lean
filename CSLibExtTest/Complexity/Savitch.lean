/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Savitch
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace CSLibExtTest.Complexity.Savitch

open Cslib.Complexity.Savitch

/-- Boundary check: on a two-point configuration space with one
edge, reachability in at most `2 ^ 0 = 1` step holds along the
edge, and the Savitch predicate accepts. -/
example : reachIn (fun x y : Fin 2 => x = 0 ∧ y = 1) 0 0 1 = true := by
  decide

/-- Soundness form at `k = 0`: acceptance gives a path of length
at most one. -/
example (h : reachIn (fun x y : Fin 2 => x = 0 ∧ y = 1) 0 0 1 = true) :
    ∃ n ≤ 2 ^ 0, GPath (fun x y : Fin 2 => x = 0 ∧ y = 1) 0 1 n :=
  reachIn_sound 0 0 1 h

/-- The two-edge path `0 → 1 → 2` on `Fin 3`. -/
abbrev twoEdge (x y : Fin 3) : Prop := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2)

/-- Recursive case: `2` is reachable from `0` within `2 ^ 1 = 2` steps, through the midpoint
`1`, so the predicate accepts at `k = 1`. -/
example : reachIn twoEdge 1 0 2 = true := by
  decide

/-- The same pair is rejected at `k = 0`: no walk of at most one step joins `0` to `2`. -/
example : reachIn twoEdge 0 0 2 = false := by
  decide

/-- The explicit two-step walk `0 → 1 → 2`. -/
theorem twoEdge_walk : GPath twoEdge 0 2 2 :=
  .step (y := 1) (by decide) (.step (y := 0) (by decide) .refl)

/-- Completeness applied to the constructed two-step walk at `k = 1`. -/
example : reachIn twoEdge 1 0 2 = true :=
  reachIn_complete 1 (by decide) twoEdge_walk

/-- Soundness at the recursive level: acceptance at `k = 1` yields a walk of at most two
steps. -/
example : ∃ n ≤ 2 ^ 1, GPath twoEdge 0 2 n :=
  reachIn_sound 1 0 2 (by decide)

/-- The walk transfers to CSLib's `Relation.RelatesInSteps`. -/
example : Relation.RelatesInSteps twoEdge 0 2 2 :=
  gPath_iff_relatesInSteps.mp twoEdge_walk

/-- Rejection at `k = 0`, read through `reachIn_iff_relatesWithinSteps`: `0` does not reach
`2` within one step. -/
example : ¬ Relation.RelatesWithinSteps twoEdge 0 2 (2 ^ 0) := by
  rw [← reachIn_iff_relatesWithinSteps]
  decide

end CSLibExtTest.Complexity.Savitch
