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

The closure-and-convergence criterion used here also requires coverage: from every state,
some scheduler-admitted infinite execution must start there. The scheduler is represented by a
predicate on the sequences of states and labels. Coverage rules out vacuous convergence at states
with no admitted run. It implies an outgoing transition at each state by taking the first step
of a witnessing run, but outgoing transitions alone do not ensure that the scheduler admits a
run from each state.

Dijkstra's original central-daemon model requires progress and convergence for every sequence of
daemon selections. It also requires that a privilege be present in every legitimate state, that
each privilege occur in some legitimate state, and that the legitimate states be mutually
reachable. The abstract LTS criterion does not impose this daemon model or its additional
requirements, nor does it establish convergence of any particular protocol.

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
`L`-state preserves `L`, every state starts some admitted infinite execution, and every admitted
infinite execution visits an `L`-state at some finite index, possibly zero. Closure applies even to
transitions not taken by any admitted execution. -/
def SelfStabilizing (lts : LTS State Label) (L : State → Prop)
    (admissible : ωSequence State → ωSequence Label → Prop) : Prop :=
  lts.TrInv L ∧
    (∀ s, ∃ ss μs, ss 0 = s ∧ lts.OmegaExecution ss μs ∧ admissible ss μs) ∧
    ∀ ss μs, lts.OmegaExecution ss μs → admissible ss μs → ∃ n, L (ss n)

/-- If every transition preserves legitimacy, self-stabilization is equivalent to every state
starting an admitted infinite execution and every admitted infinite execution remaining legitimate
from some finite cutoff onward. The cutoff may depend on the execution and includes the state at
the cutoff itself. -/
theorem selfStabilizing_iff_eventually_always {lts : LTS State Label} {L : State → Prop}
    {admissible : ωSequence State → ωSequence Label → Prop} (hclosed : lts.TrInv L) :
    lts.SelfStabilizing L admissible ↔
      (∀ s, ∃ ss μs, ss 0 = s ∧ lts.OmegaExecution ss μs ∧ admissible ss μs) ∧
      ∀ ss μs, lts.OmegaExecution ss μs → admissible ss μs → ∃ n, ∀ m ≥ n, L (ss m) := by
  constructor
  · rintro ⟨_, hcover, hentry⟩
    refine ⟨hcover, ?_⟩
    intro ss μs hrun hadm
    obtain ⟨n, hn⟩ := hentry ss μs hrun hadm
    exact ⟨n, fun m hnm ↦ (mtrInv_of_trInv hclosed) _ _ _ (hrun.extract_mTr hnm) hn⟩
  · rintro ⟨hcover, halways⟩
    refine ⟨hclosed, hcover, ?_⟩
    intro ss μs hrun hadm
    obtain ⟨n, hn⟩ := halways ss μs hrun hadm
    exact ⟨n, hn n le_rfl⟩

end Cslib.LTS
