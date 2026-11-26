/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Configuration.FiniteWitnessUnionBound

/-!
# Tests for `MathlibExt.Probability.Configuration.FiniteWitnessUnionBound`

* `finiteEventMass` of the fair coin on `Bool` at an event.
* `finiteEventMass_tail_le_choose_mul_pow` for the fair coin with `K ω = 1` iff `ω = true`, one
  witness slot (`h = n = 1`) and `a = 1/2`: `μ(K ≥ 1) ≤ C(1, 1) (1/2)`.
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.Configuration.FiniteWitnessUnionBound

/-- The fair coin weight on `Bool`. -/
noncomputable def coin : Bool → ℝ := fun _ => 1 / 2

example : finiteEventMass coin {true} = 1 / 2 := by
  simp [finiteEventMass, coin]

example : finiteEventMass coin {ω | 1 ≤ (if ω then 1 else 0 : ℕ)} ≤ Nat.choose 1 1 * (1 / 2) ^ 1 :=
  finiteEventMass_tail_le_choose_mul_pow coin (fun _ => by norm_num [coin])
    (fun ω => if ω then 1 else 0) 1 1 (1 / 2) (fun _ ω => ω = true)
    (fun ω h => ⟨Finset.univ, rfl, by cases ω <;> simp_all⟩)
    (fun S _ => by simp [finiteEventMass, coin])

end MathlibExtTest.StatMech.Probability.Configuration.FiniteWitnessUnionBound
