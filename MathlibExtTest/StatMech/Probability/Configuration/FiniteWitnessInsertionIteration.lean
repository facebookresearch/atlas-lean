/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Configuration.FiniteWitnessInsertionIteration

/-!
# Tests for `MathlibExt.Probability.Configuration.FiniteWitnessInsertionIteration`

* `finiteEventMass_le_pow_erase_of_insert_step` on the one-point space with the always-true
  witness and `a = 1` (the insertion step holds with equality): the witness event of `{0, 1}` has
  mass at most `1`.
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.Configuration.FiniteWitnessInsertionIteration

example : finiteEventMass (fun _ : Unit => (1 : ℝ)) {_ω | True} ≤ 1 ^ (({0, 1} : Finset (Fin 2)).erase 0).card :=
  finiteEventMass_le_pow_erase_of_insert_step (I := Fin 2) (fun _ => 1) (fun _ => zero_le_one)
    (by simp) (fun _ _ => True) zero_le_one (fun _ _ _ _ _ => by simp) {0, 1} 0 (by simp)

end MathlibExtTest.StatMech.Probability.Configuration.FiniteWitnessInsertionIteration
