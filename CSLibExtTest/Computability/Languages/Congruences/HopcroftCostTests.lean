/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Languages.Congruences.HopcroftCost

/-!
# Client tests for Hopcroft's splitter trace and predecessor cost

The three-state DFA sends states `0` and `1` to `0`, while `2` stays at `2`.
The singleton splitter `{0}` therefore has two predecessors. Processing it
splits `{1, 2}`, so the one-step test checks both partition and waiting-list updates.
-/

namespace DFA.Hopcroft.CostTests

private def splitDFA : DFA Unit (Fin 3) where
  step q _ := if q = 2 then 2 else 0
  start := 0
  accept := {0}

private def initialPartition : List (Finset (Fin 3)) := [{0}, {1, 2}]

private def initialWaiting : List (Finset (Fin 3) × Unit) := [({0}, ())]

/-- Zero fuel records no splitter, charges no work, and leaves the loop state untouched. -/
example :
    hopcroftSplitters splitDFA 0 initialPartition initialWaiting = [] ∧
    hopcroftCost splitDFA (hopcroftSplitters splitDFA 0 initialPartition initialWaiting) = 0 ∧
    splitDFA.hopcroftLoop 0 initialPartition initialWaiting =
      (initialPartition, initialWaiting) := ⟨rfl, rfl, rfl⟩

/-- An empty waiting list stops the trace and loop even when fuel remains. -/
example :
    hopcroftSplitters splitDFA 5 initialPartition [] = [] ∧
    hopcroftCost splitDFA (hopcroftSplitters splitDFA 5 initialPartition []) = 0 ∧
    splitDFA.hopcroftLoop 5 initialPartition [] = (initialPartition, []) :=
  ⟨rfl, rfl, rfl⟩

/-- One popped splitter refines the partition and adds the smaller half to the queue.
The public trace/loop theorem applies through the client import. -/
example :
    hopcroftSplitters splitDFA 1 initialPartition initialWaiting = [({0}, ())] ∧
    splitDFA.hopcroftLoop 1 initialPartition initialWaiting =
      ([{0}, {1}, {2}], [({1}, ())]) ∧
    splitDFA.hopcroftLoop
        (hopcroftSplitters splitDFA 1 initialPartition initialWaiting).length
        initialPartition initialWaiting =
      splitDFA.hopcroftLoop 1 initialPartition initialWaiting := by
  refine ⟨rfl, ?_, ?_⟩
  · decide
  · exact hopcroftLoop_eq_hopcroftLoop_of_length splitDFA 1 initialPartition initialWaiting

/-- The singleton splitter has two predecessors, so its cost is `2 + 1`, rather than
the `1 + 1` that charging its own cardinality would give. -/
example :
    (preimage splitDFA ({0} : Finset (Fin 3)) ()).card ≠ ({0} : Finset (Fin 3)).card ∧
    (preimage splitDFA ({0} : Finset (Fin 3)) ()).card = 2 ∧
    ({0} : Finset (Fin 3)).card = 1 ∧
    hopcroftCost splitDFA (hopcroftSplitters splitDFA 1 initialPartition initialWaiting) = 3 := by
  decide

end DFA.Hopcroft.CostTests
