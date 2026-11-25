/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Approximation.ChebyshevLebesgue
import Mathlib.Tactic.FinCases

/-! # Regression tests for the Lebesgue bound at Chebyshev extrema -/

open Polynomial Real
open MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted

example {n : ℕ} (hn : 1 ≤ n) :
    ∑ j : Fin (n + 1),
        |(Lagrange.basis Finset.univ (fun i : Fin (n + 1) => Chebyshev.node n i) j).eval 1|
      ≤ 2 / π * log (n + 1) + 1 :=
  sum_abs_lagrange_basis_chebyshev_le (n := n) (hn := hn) (x := 1)
    (hx := ⟨by norm_num, le_rfl⟩)

example {n : ℕ} (hn : 1 ≤ n) :
    ∑ j : Fin (n + 1),
        |(Lagrange.basis Finset.univ (fun i : Fin (n + 1) => Chebyshev.node n i) j).eval (-1)|
      ≤ 2 / π * log (n + 1) + 1 :=
  sum_abs_lagrange_basis_chebyshev_le (n := n) (hn := hn) (x := -1)
    (hx := ⟨le_rfl, by norm_num⟩)

-- An interior node of the quadratic Lobatto grid.
example : ∑ j : Fin 3,
    |(Lagrange.basis Finset.univ (fun i : Fin 3 => Chebyshev.node 2 i) j).eval 0|
      ≤ 2 / π * log 3 + 1 := by
  have h : Chebyshev.node 2 1 = 0 := by norm_num [Chebyshev.node, cos_pi_div_two]
  rw [← h]
  simpa only [show (↑(2 : ℕ) + 1 : ℝ) = 3 by norm_num] using
    sum_abs_lagrange_basis_chebyshev_le (n := 2) (hn := by decide)
      (x := Chebyshev.node 2 1) (hx := Chebyshev.node_mem_Icc)

-- The test point lies strictly between the nodes at 0 and 1.
example (j : Fin 3) : (1 / 2 : ℝ) ≠ Chebyshev.node 2 j := by
  fin_cases j <;> norm_num [Chebyshev.node, cos_pi_div_two]

example : ∑ j : Fin 3,
    |(Lagrange.basis Finset.univ (fun i : Fin 3 => Chebyshev.node 2 i) j).eval (1 / 2)|
      ≤ 2 / π * log 3 + 1 := by
  simpa only [show (↑(2 : ℕ) + 1 : ℝ) = 3 by norm_num] using
    sum_abs_lagrange_basis_chebyshev_le (n := 2) (hn := by decide) (x := 1 / 2)
      (hx := ⟨by norm_num, by norm_num⟩)
