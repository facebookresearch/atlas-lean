/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.BigOperators.WeightedFiniteInjection
public import Mathlib.Tactic.Positivity

/-!
# Tests for `MathlibExt.Algebra.BigOperators.WeightedFiniteInjection`

* `Fintype.sum_le_mul_sum_of_injective` with the identity injection on `Fin 3`, source weight
  `i ↦ i` and target weight `i ↦ i + 1`, constant `C = 1`.
-/

@[expose] public section

open StatMech

namespace MathlibExtTest.StatMech.Algebra.BigOperators.WeightedFiniteInjection

example : (∑ i : Fin 3, (i : ℝ)) ≤ 1 * ∑ i : Fin 3, ((i : ℝ) + 1) :=
  Fintype.sum_le_mul_sum_of_injective id Function.injective_id (fun i : Fin 3 => (i : ℝ))
    (fun i : Fin 3 => (i : ℝ) + 1) 1 zero_le_one (fun _ => by positivity)
    (fun a => by simp)

end MathlibExtTest.StatMech.Algebra.BigOperators.WeightedFiniteInjection
