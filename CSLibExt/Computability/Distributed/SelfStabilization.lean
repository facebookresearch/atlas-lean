/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Self-stabilization under an admissibility condition

The general closure-and-convergence criterion for self-stabilization requires that the legitimate
states be closed under every transition and that every scheduler-admitted infinite execution
reach a legitimate state. The scheduler is represented by a predicate on the sequences of states
and labels. The initial state is unrestricted.

The convergence clause is vacuous at a state from which there is no admitted infinite execution.
Coverage (having an admitted infinite execution from each state) and non-deadlock (having an
outgoing transition at each state) are not assumptions of this criterion. Coverage implies
non-deadlock by the first step, but non-deadlock alone does not guarantee coverage for a given
admissibility predicate.

Dijkstra's original central-daemon model also requires that a privilege be present in every
legitimate state, that each privilege occur in some legitimate state, and that the legitimate
states be mutually reachable. We formalize only the general criterion, not these additional
requirements or convergence of any particular protocol.

## References

* E. W. Dijkstra, *Self-stabilizing systems in spite of distributed control* (1974),
  [EWD 426](https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD426.html), for the original
  central-daemon model.
* S. Dolev, *Self-Stabilization*, MIT Press (2000), for the general closure-and-convergence
  formulation.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

/-- An LTS is self-stabilizing for `L` under `admissible` if every transition out of an
`L`-state preserves `L` and every admitted infinite execution visits an `L`-state at some finite
index, possibly zero. No restriction is placed on the starting state. Closure applies even to
transitions not taken by any admitted execution. -/
def SelfStabilizing (lts : LTS State Label) (L : State → Prop)
    (admissible : ωSequence State → ωSequence Label → Prop) : Prop :=
  lts.TrInv L ∧ ∀ ss μs, lts.OmegaExecution ss μs → admissible ss μs → ∃ n, L (ss n)

/-- If every transition preserves legitimacy, self-stabilization is equivalent to every
admitted infinite execution remaining legitimate from some finite cutoff onward. The cutoff
may depend on the execution and includes the state at the cutoff itself. -/
theorem selfStabilizing_iff_eventually_always {lts : LTS State Label} {L : State → Prop}
    {admissible : ωSequence State → ωSequence Label → Prop} (hclosed : lts.TrInv L) :
    lts.SelfStabilizing L admissible ↔
      ∀ ss μs, lts.OmegaExecution ss μs → admissible ss μs → ∃ n, ∀ m ≥ n, L (ss m) := by
  constructor
  · rintro ⟨_, hentry⟩ ss μs hrun hadm
    obtain ⟨n, hn⟩ := hentry ss μs hrun hadm
    exact ⟨n, fun m hnm ↦ (mtrInv_of_trInv hclosed) _ _ _ (hrun.extract_mTr hnm) hn⟩
  · intro halways
    refine ⟨hclosed, ?_⟩
    intro ss μs hrun hadm
    obtain ⟨n, hn⟩ := halways ss μs hrun hadm
    exact ⟨n, hn n le_rfl⟩

end Cslib.LTS
