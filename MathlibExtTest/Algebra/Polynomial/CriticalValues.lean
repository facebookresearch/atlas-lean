/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.CriticalValues

@[expose] public section

open Polynomial

universe u

/-- Source consumer with the original universe binder. -/
example {k : Type u} [Field k] (P : k[X]) (hP : derivative P ≠ 0) :
    {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite :=
  Polynomial.finite_setOf_criticalValue P hP

/-- Source consumer with the original universe binder. -/
example {k : Type u} [Field k] [IsAlgClosed k] (P : k[X]) (c : k)
    (hc : ∀ x : k, (derivative P).eval x = 0 → P.eval x ≠ c) :
    (P - C c).Separable :=
  Polynomial.separable_sub_C_of_forall_eval_derivative P c hc

/-- Boundary: for `X ^ 2` over `ℚ`, the value `0` is a critical value, so
the avoidance hypothesis fails at the critical point `0`. -/
example : ∃ x : ℚ, (derivative (X ^ 2 : ℚ[X])).eval x = 0 ∧
    (X ^ 2 : ℚ[X]).eval x = 0 :=
  ⟨0, by simp⟩
