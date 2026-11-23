/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Ring

/-!
# Fibonacci coefficients in Tonien's series for `π²`
-/

namespace MetaMathlibExt

/-- **Fibonacci closed form of the sequence $a_n$.** Let $(a_n)_{n \ge 0}$ be real numbers with
$a_0 = -8\sqrt{5}/250$, $a_1 = (25 - 4\sqrt{5})/250$ and $a_{n+1} = a_n + a_{n-1}$ for $n \ge 1$,
and write $F_m$ for the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every $n \ge 0$,

$$a_{n+1} = \frac{25 - 4\sqrt{5}}{250} F_{n+1} - \frac{8\sqrt{5}}{250} F_n.$$

The paper states $a_n = \frac{25 - 4\sqrt{5}}{250} F_n - \frac{8\sqrt{5}}{250} F_{n-1}$ for all
$n \ge 0$ with the convention $F_{-1} = 1$; its case $n = 0$ is the initial value $a_0$.

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.3 (`fq-2024-tonien10292023-lem-2.3`). -/
public theorem fibPiSquared_coeff_eq_fib (a : ℕ → ℝ) (ha0 : a 0 = -(8 * √5) / 250)
    (ha1 : a 1 = (25 - 4 * √5) / 250) (ha : ∀ n, 1 ≤ n → a (n + 1) = a n + a (n - 1)) (n : ℕ) :
    a (n + 1) = (25 - 4 * √5) / 250 * Nat.fib (n + 1) - 8 * √5 / 250 * Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using ha1
  | one =>
    rw [ha 1 (by decide)]
    simp [ha0, ha1, sub_eq_add_neg, neg_div]
  | more n ih₀ ih₁ =>
    rw [ha (n + 2) (by omega), show n + 2 - 1 = n + 1 by rfl, ih₁, ih₀,
      Nat.fib_add_two (n := n + 1), Nat.fib_add_two (n := n)]
    push_cast
    ring

end MetaMathlibExt
