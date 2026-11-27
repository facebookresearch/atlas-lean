/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/NumberTheory/PellConvergent.lean` (leanprover/lean-eval),
problem `pell_solution_convergent` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The theorem statement was moved from `WantedExt/NumberTheory/PellConvergentWanted.lean`
with its ATLAS name. The proof is new.
-/

module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

/-!
# Pell solutions are convergents of the square root

Factoring the Pell equation gives the approximation error for `x / y`. Since the conjugate
factor `x / y + √d` exceeds two, Legendre's criterion applies.
-/

public section

namespace MathlibExt.NumberTheory.PellConvergentWanted.NumberTheory

open scoped Real

set_option linter.dupNamespace false in
/-- **Solutions of Pell's equation are continued-fraction convergents.** Let $d$ be a positive
squarefree integer and let $x$ and $y$ be positive integers with $x^2 - d y^2 = 1$. Then $x / y$
is a convergent of the regular continued fraction expansion of $\sqrt{d}$: there is a natural
number $n$ such that the $n$-th convergent of $\sqrt{d}$ (counting from the $0$-th) equals
$x / y$.

Source: J.-L. Lagrange (1770). Listed as §84 in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `pell_solution_convergent`. -/
theorem pell_solution_is_convergent
    (d : ℤ) (_hd : Squarefree d) (hd0 : 0 < d)
    (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (hsol : x ^ 2 - d * y ^ 2 = 1) :
    ∃ n : ℕ, (GenContFract.of (Real.sqrt (d : ℝ))).convs n = (x : ℝ) / (y : ℝ) := by
  let q := Rat.divInt x y
  have hq : (q : ℝ) = (x : ℝ) / y := by simp [q, Rat.divInt_eq_div]
  have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
  have hs : 1 ≤ √(d : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast Int.add_one_le_of_lt hd0)
  have hpell : (x : ℝ) ^ 2 - d * (y : ℝ) ^ 2 = 1 := by exact_mod_cast hsol
  have hprod : ((q : ℝ) - √d) * (q + √d) = 1 / (y : ℝ) ^ 2 := by
    calc
      _ = ((x : ℝ) ^ 2 - (√d) ^ 2 * y ^ 2) / y ^ 2 := by
        rw [hq]
        field_simp
        ring
      _ = _ := by rw [Real.sq_sqrt (by positivity), hpell]
  have hsum : 0 < (q : ℝ) + √d := by rw [hq]; positivity
  have hdiff : 0 < (q : ℝ) - √d :=
    (mul_pos_iff_of_pos_right hsum).mp (hprod ▸ by positivity)
  have htwo : 2 < (q : ℝ) + √d := by linarith
  have hden : (q.den : ℝ) ≤ y := by exact_mod_cast Int.le_of_dvd hy (Rat.den_dvd x y)
  rw [← hq]
  apply Real.exists_convs_eq_rat
  calc
    |√d - q| = (q : ℝ) - √d := by rw [abs_sub_comm, abs_of_pos hdiff]
    _ = 1 / ((y : ℝ) ^ 2 * (q + √d)) := by
      rw [← div_div, eq_div_iff hsum.ne']
      exact hprod
    _ < 1 / (2 * (y : ℝ) ^ 2) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      rw [mul_comm ((y : ℝ) ^ 2)]
      exact mul_lt_mul_of_pos_right htwo (sq_pos_of_pos hy')
    _ ≤ 1 / (2 * (q.den : ℝ) ^ 2) := by gcongr

end MathlibExt.NumberTheory.PellConvergentWanted.NumberTheory
