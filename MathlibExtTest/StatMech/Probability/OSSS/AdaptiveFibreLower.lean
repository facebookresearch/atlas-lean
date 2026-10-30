/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.AdaptiveFibreLower
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.AdaptiveFibreLower`

* `finiteEventMass_adaptive_fibre_lower` with `μ = 1` on `Bool`, the constant projection,
  `Base = univ`, arm and goal `{true}`, `c = 1/2`: `1/2 · μ(univ) ≤ μ({true})`.
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.OSSS.AdaptiveFibreLower

/-- The constant projection onto `false`. -/
def P : Bool → Bool := fun _ => false

example : 1 / 2 * finiteEventMass (fun _ : Bool => (1 : ℝ)) Set.univ
    ≤ finiteEventMass (fun _ : Bool => (1 : ℝ)) {true} :=
  finiteEventMass_adaptive_fibre_lower _ (fun _ => zero_le_one) P (fun _ => rfl) Set.univ {true}
    (fun _ => {true}) (1 / 2) (by simp) (fun _ h => h) (by
      intro psi hpsi
      have hp : psi = false := by simpa [P] using hpsi
      subst hp
      simp [P, Finset.filter_true_of_mem, Set.indicator])

end MathlibExtTest.StatMech.Probability.OSSS.AdaptiveFibreLower
