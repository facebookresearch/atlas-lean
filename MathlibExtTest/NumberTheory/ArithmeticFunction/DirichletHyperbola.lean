/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.DirichletHyperbola

/-!
# Tests for Dirichlet's hyperbola method
-/

@[expose] public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

-- The hyperbola identity for `d = ζ * ζ` at `x = 10`, `y = 3`.
example : ∑ n ∈ Ioc 0 ⌊(10 : ℝ)⌋₊, ((ζ : ArithmeticFunction ℤ) * ζ) n =
    ∑ d ∈ Ioc 0 ⌊(3 : ℝ)⌋₊, (ζ : ArithmeticFunction ℤ) d * ∑ e ∈ Ioc 0 ⌊(10 : ℝ) / d⌋₊,
        (ζ : ArithmeticFunction ℤ) e
      + ∑ e ∈ Ioc 0 ⌊(10 : ℝ) / 3⌋₊, (∑ d ∈ Ioc 0 ⌊(10 : ℝ) / e⌋₊,
        (ζ : ArithmeticFunction ℤ) d) * (ζ : ArithmeticFunction ℤ) e
      - (∑ d ∈ Ioc 0 ⌊(3 : ℝ)⌋₊, (ζ : ArithmeticFunction ℤ) d) *
        ∑ e ∈ Ioc 0 ⌊(10 : ℝ) / 3⌋₊, (ζ : ArithmeticFunction ℤ) e :=
  sum_Ioc_mul_eq_hyperbola _ _ 10 (by norm_num)

-- `∑_{n ≤ 10} d(n) = 27`, matching the left-hand side above.
example : ∑ n ∈ Ioc 0 10, ((ζ : ArithmeticFunction ℤ) * ζ) n = 27 := by
  decide +kernel

-- The floor-error estimate, with the empty set and with a single term.
example (a : ℕ → ℝ) (x : ℝ) :
    ‖∑ d ∈ (∅ : Finset ℕ), a d * (⌊x / d⌋ : ℝ) - (x : ℝ) * ∑ d ∈ (∅ : Finset ℕ), a d / d‖ ≤
      ∑ d ∈ (∅ : Finset ℕ), ‖a d‖ :=
  norm_sum_mul_floor_div_sub_mul_sum_div_le a x ∅

example (x : ℝ) (hx : 0 ≤ x) :
    ‖∑ d ∈ ({1} : Finset ℕ), (1 : ℝ) * (⌊x / d⌋₊ : ℝ) -
        (x : ℝ) * ∑ d ∈ ({1} : Finset ℕ), (1 : ℝ) / (d : ℝ)‖ ≤ ∑ _d ∈ ({1} : Finset ℕ), ‖(1 : ℝ)‖ :=
  norm_sum_mul_natFloor_div_sub_mul_sum_div_le (fun _ => (1 : ℝ)) hx {1}
