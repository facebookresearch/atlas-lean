/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Theorems/Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
Only the theorem statement is adapted from this source. The proof specializes
`HilbertSymbol.diagonal_unit_isotropic` to three variables.
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
import MathlibExt.NumberTheory.Padics.HilbertSymbol.Isotropic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Ternary isotropy over `ℚ_[p]` at odd primes

The form `z ^ 2 - a * x ^ 2 - b * y ^ 2` with `‖a‖ = ‖b‖ = 1` is the case `n = 3` of
`HilbertSymbol.diagonal_unit_isotropic`, with the unit coefficients `1, -a, -b`. Only the
statement comes from the upstream file named above; the upstream proof is not used.
-/

/-- **Ternary isotropy over `ℚ_[p]` for odd `p`.** If `p` is an odd prime and
`a, b` are p-adic numbers of norm `1`, then `z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0`
has a nontrivial solution in `ℚ_[p]`. -/
public theorem Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  obtain ⟨v, hv0, hv⟩ := HilbertSymbol.diagonal_unit_isotropic p hp (by decide : 2 < 3)
    ![1, -PadicInt.mkUnits ha, -PadicInt.mkUnits hb]
  refine ⟨v 0, v 1, v 2, fun ⟨h0, h1, h2⟩ ↦ hv0 (funext fun i ↦ ?_), ?_⟩
  · fin_cases i
    exacts [h0, h1, h2]
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Units.val_one, Units.val_neg, PadicInt.coe_one,
      PadicInt.coe_neg, PadicInt.mkUnits_eq, one_mul] at hv
    linear_combination hv
