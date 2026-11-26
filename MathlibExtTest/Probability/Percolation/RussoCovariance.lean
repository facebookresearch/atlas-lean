/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RussoCovariance

@[expose] public section

open StatMech StatMech.BeffaraDC

namespace MathlibExtTest.Probability.Percolation.RussoCovariance

/-- The event "the unique coordinate is closed", a decreasing event. -/
def closedEvent : Set (ConfigSpace (Fin 1)) := {ω | ω 0 = false}

/-- `closedEvent` is not increasing, so `russoFormula` does not apply to it. -/
example : ¬ IsIncreasing closedEvent := by
  intro h
  have hmem : (fun _ => false : ConfigSpace (Fin 1)) ∈ closedEvent := rfl
  have hle : (fun _ => false : ConfigSpace (Fin 1)) ≤ (fun _ => true) := fun _ => Bool.false_le _
  have := h hle hmem
  simp [closedEvent] at this

/-- Non-vacuity: the covariance form of Russo's formula applies to the decreasing event
`closedEvent` at the interior density `p = 1/3`. -/
example : HasDerivAt (fun p => prob p closedEvent)
    ((1 / ((1 / 3 : ℝ) * (1 - 1 / 3))) * ∑ e, (prob (1 / 3) (closedEvent ∩ openEdge e)
      - prob (1 / 3) (openEdge e) * prob (1 / 3) closedEvent)) (1 / 3) :=
  hasDerivAt_prob_eq_sum_cov closedEvent (by norm_num) (by norm_num)

end MathlibExtTest.Probability.Percolation.RussoCovariance
