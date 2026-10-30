/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.AdaptiveFibreStep
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.AdaptiveFibreStep`

* `finiteEventMass_eq_sum_projectionFibres` for the projection onto `false` on `Bool`.
* `finiteEventMass_adaptive_fibre_step` and `finiteEventMass_adaptive_fibre_step_on_base` with
  `μ = 1`, the constant projection, `Base = univ`, arm `{true}`, inserted event `{true}` and
  `a = 1/2`: the bound `μ({true}) ≤ 1/2 · μ(univ)` holds with equality.
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.OSSS.AdaptiveFibreStep

/-- The constant projection onto `false`. -/
def P : Bool → Bool := fun _ => false

example : finiteEventMass (fun _ : Bool => (1 : ℝ)) {true} =
    ∑ psi ∈ Finset.univ.image P, ∑ ω ∈ Finset.univ.filter (fun ω => P ω = psi),
      ({true} : Set Bool).indicator (fun _ => (1 : ℝ)) ω :=
  finiteEventMass_eq_sum_projectionFibres _ P _

theorem hcap : ∀ psi ∈ Finset.univ.image P,
    (∑ ω ∈ Finset.univ.filter (fun ω => P ω = psi),
        ((fun _ => ({true} : Set Bool)) psi).indicator (fun _ => (1 : ℝ)) ω) ≤
      1 / 2 * ∑ ω ∈ Finset.univ.filter (fun ω => P ω = psi), (fun _ => (1 : ℝ)) ω := by
  intro psi hpsi
  have hp : psi = false := by simpa [P] using hpsi
  subst hp
  simp [P, Finset.filter_true_of_mem, Set.indicator]

example : finiteEventMass (fun _ : Bool => (1 : ℝ)) {true}
    ≤ 1 / 2 * finiteEventMass (fun _ : Bool => (1 : ℝ)) Set.univ :=
  finiteEventMass_adaptive_fibre_step _ (fun _ => zero_le_one) P (fun _ => rfl) Set.univ {true}
    (fun _ => {true}) (by simp) (fun h => ⟨trivial, h⟩) hcap

example : finiteEventMass (fun _ : Bool => (1 : ℝ)) {true}
    ≤ 1 / 2 * finiteEventMass (fun _ : Bool => (1 : ℝ)) Set.univ :=
  finiteEventMass_adaptive_fibre_step_on_base _ (fun _ => zero_le_one) P (fun _ => rfl) Set.univ
    {true} (fun _ => {true}) (by simp) (fun h => ⟨trivial, h⟩) (fun psi hpsi _ => hcap psi hpsi)

end MathlibExtTest.StatMech.Probability.OSSS.AdaptiveFibreStep
