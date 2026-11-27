/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_finite_setOf_criticalValue.lean`,
`Theorems/Thm_Polynomial_separable_sub_C_of_forall_eval_derivative.lean`
and
`P2M/Sol/S_Polynomial_finite_setOf_criticalValue.lean`,
`P2M/Sol/S_Polynomial_separable_sub_C_of_forall_eval_derivative.lean`
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
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable

@[expose] public section

namespace Polynomial

/-- A polynomial over a field with nonzero derivative has only finitely
many critical values: values taken at a root of the derivative. -/
theorem finite_setOf_criticalValue
    {k : Type*} [Field k] (P : k[X]) (hP : derivative P ≠ 0) :
    {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite := by
  have hfin : {x : k | (derivative P).eval x = 0}.Finite :=
    finite_setOfPred_isRoot hP
  refine (hfin.image fun x => P.eval x).subset ?_
  rintro c ⟨x, rfl, hx⟩
  exact ⟨x, hx, rfl⟩

/-- Over an algebraically closed field, `P - C c` is separable when `c`
is not a critical value of `P`: no root of the derivative maps to `c`. -/
theorem separable_sub_C_of_forall_eval_derivative
    {k : Type*} [Field k] [IsAlgClosed k] (P : k[X]) (c : k)
    (hc : ∀ x : k, (derivative P).eval x = 0 → P.eval x ≠ c) :
    (P - C c).Separable := by
  rw [separable_def, derivative_sub, derivative_C, sub_zero,
    isCoprime_iff_aeval_ne_zero_of_isAlgClosed k k]
  intro a
  by_cases h : (derivative P).eval a = 0
  · left
    rw [coe_aeval_eq_eval, eval_sub, eval_C]
    exact sub_ne_zero.mpr (hc a h)
  · right
    rwa [coe_aeval_eq_eval]

end Polynomial
