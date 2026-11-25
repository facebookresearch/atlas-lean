/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section
namespace MetaMathlibExt

/-! # k-Pell matrix as a Riordan array -/

/-- **Generalized Pell matrix as a Riordan array, for every k.** Let $k$ be a natural number
and let $p(n, m)$, for natural numbers $n$ and $m$, be natural numbers such that for every $n$
the power series $\sum_{m \ge 0} p(n, m)\, x^m$ over $\mathbb{Q}$ satisfies
$\left(\sum_{m \ge 0} p(n, m)\, x^m\right)(1 - x)^{n+1} = (1 + x + \dots + x^k)^n$. Then for all
natural numbers $n$ and $m$, the coefficient of $x^n$ in
$\frac{1}{1-x} \left(\frac{x(1 + x + \dots + x^k)}{1-x}\right)^m$ is $p(m, n - m)$ if $m \le n$
and $0$ otherwise. That is, the lower-triangular matrix whose entry in row $n$ and column $m$
is $p(m, n - m)$ is the Riordan array
$\left(\frac{1}{1-x}, \frac{x(1 + x + \dots + x^k)}{1-x}\right)$. -/
theorem pell_riordan_general (k : ℕ) (p : ℕ → ℕ → ℕ)
    (hgen : ∀ n : ℕ,
      PowerSeries.mk (fun m => (↑(p n m) : ℚ)) * (1 - PowerSeries.X (R := ℚ)) ^ (n + 1) =
      (Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ n)
    (n m : ℕ) :
    (if m ≤ n then (↑(p m (n - m)) : ℚ) else 0) =
      PowerSeries.coeff (R := ℚ) n (Ring.inverse (1 - PowerSeries.X (R := ℚ)) *
        (PowerSeries.X (R := ℚ) *
          Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i) *
          Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ m) := by
  have hA : IsUnit (1 - PowerSeries.X (R := ℚ)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hAm : IsUnit ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := hA.pow (m + 1)
  have hP : PowerSeries.mk (fun j => (↑(p m j) : ℚ)) =
      (Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ m *
        Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := by
    have h := hgen m
    calc PowerSeries.mk (fun j => (↑(p m j) : ℚ))
        = PowerSeries.mk (fun j => (↑(p m j) : ℚ)) * 1 := by rw [mul_one]
      _ = PowerSeries.mk (fun j => (↑(p m j) : ℚ)) *
            (((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) *
              Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1))) := by
            rw [Ring.mul_inverse_cancel _ hAm]
      _ = (PowerSeries.mk (fun j => (↑(p m j) : ℚ)) *
            ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1))) *
            Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := by rw [mul_assoc]
      _ = (Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ m *
            Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) := by rw [h]
  have hInv : Ring.inverse ((1 - PowerSeries.X (R := ℚ)) ^ (m + 1)) =
      (Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ (m + 1) := by
    rw [← Ring.inverse_pow]
  have hRHS : Ring.inverse (1 - PowerSeries.X (R := ℚ)) *
        (PowerSeries.X (R := ℚ) *
          Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i) *
          Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ m =
      PowerSeries.X (R := ℚ) ^ m * PowerSeries.mk (fun j => (↑(p m j) : ℚ)) := by
    have hring : Ring.inverse (1 - PowerSeries.X (R := ℚ)) *
        (PowerSeries.X (R := ℚ) *
          Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i) *
          Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ m =
        PowerSeries.X (R := ℚ) ^ m *
          ((Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ m *
            (Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ (m + 1)) := by ring
    rw [hring, ← hInv, ← hP]
  rw [hRHS, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]

set_option linter.unusedVariables false in
/-- **Generalized Pell matrix as a Riordan array.** Let $k \ge 2$ be a natural number and let
$p(n, m)$, for natural numbers $n$ and $m$, be natural numbers such that for every $n$ the power
series $\sum_{m \ge 0} p(n, m)\, x^m$ over $\mathbb{Q}$ satisfies
$\left(\sum_{m \ge 0} p(n, m)\, x^m\right)(1 - x)^{n+1} = (1 + x + \dots + x^k)^n$. Then for all
natural numbers $n$ and $m$, the coefficient of $x^n$ in
$\frac{1}{1-x} \left(\frac{x(1 + x + \dots + x^k)}{1-x}\right)^m$ is $p(m, n - m)$ if $m \le n$
and $0$ otherwise. That is, the lower-triangular matrix whose entry in row $n$ and column $m$
is $p(m, n - m)$ is the Riordan array
$\left(\frac{1}{1-x}, \frac{x(1 + x + \dots + x^k)}{1-x}\right)$.

Source: Jhon J. Bravo, Jose L. Herrera, and José L. Ramírez,
"Combinatorial Interpretation of Generalized Pell Numbers," Journal of
Integer Sequences 23 (2020), Article 20.2.1, Theorem (label Riordan),
lines 269–272,
https://cs.uwaterloo.ca/journals/JIS/VOL23/Bravo/bravo4.tex
It follows from `pell_riordan_general`; the hypothesis `hk` is unused and keeps the source's shape.
Proves `Wanted` entry `pell_riordan`.
-/
theorem pell_riordan :
    ∀ (k : ℕ) (hk : 2 ≤ k) (p : ℕ → ℕ → ℕ)
      (hgen : ∀ n : ℕ,
        PowerSeries.mk (fun m => (↑(p n m) : ℚ)) * (1 - PowerSeries.X (R := ℚ)) ^ (n + 1) =
        (Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i)) ^ n),
      ∀ (n m : ℕ), (if m ≤ n then (↑(p m (n - m)) : ℚ) else 0) =
        PowerSeries.coeff (R := ℚ) n (Ring.inverse (1 - PowerSeries.X (R := ℚ)) *
          (PowerSeries.X (R := ℚ) *
            Finset.sum (Finset.range (k + 1)) (fun i => PowerSeries.X (R := ℚ) ^ i) *
            Ring.inverse (1 - PowerSeries.X (R := ℚ))) ^ m) := by
  intro k _ p hgen n m
  exact pell_riordan_general k p hgen n m
end MetaMathlibExt
