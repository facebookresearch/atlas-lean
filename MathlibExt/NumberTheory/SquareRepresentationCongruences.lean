/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.PowerSeries.Inverse

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Prime congruences for square representation counts

This file defines the square theta series and its integer-power representation counts and proves
that prime divisibility of a coefficient below the prime is periodic in the exponent.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The square theta series.** The square theta series is the formal power series
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$ in $\mathbb{Z}[[q]]$: for each $n \ge 0$, its
coefficient of $q^n$ is the number of integers $m$ with $m^2 = n$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def squareThetaSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (((Finset.Icc (-(n : ℤ)) n).filter fun m : ℤ => m ^ 2 = (n : ℤ)).card : ℤ)

/-- **First coefficients of the square theta series.** In the square theta series
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$, the coefficients of $q^0$, $q^1$, $q^2$ and $q^4$ are
$1$, $2$, $0$ and $2$ respectively.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem coeff_squareThetaSeries_small :
    PowerSeries.coeff 0 squareThetaSeries = 1 ∧ PowerSeries.coeff 1 squareThetaSeries = 2 ∧
      PowerSeries.coeff 2 squareThetaSeries = 0 ∧ PowerSeries.coeff 4 squareThetaSeries = 2 := by
  simp only [squareThetaSeries, PowerSeries.coeff_mk]
  decide

/-- **The square theta series is a unit.** The square theta series
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$ is a unit of the ring $\mathbb{Z}[[q]]$ of formal
power series with integer coefficients, since its constant coefficient is $1$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem isUnit_squareThetaSeries : IsUnit squareThetaSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_squareThetaSeries_small.1]
  exact isUnit_one

/-- **Representation numbers for sums of squares.** For an integer $k$ and a natural number $n$,
$r_k(n)$ is the coefficient of $q^n$ in $\theta(q)^k$, where
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$. Since $\theta$ has constant coefficient $1$, it is a
unit of $\mathbb{Z}[[q]]$, so $\theta^k$ is a power series for negative $k$ as well.

For $k \ge 1$, $r_k(n)$ is the number of ways to write $n$ as an ordered sum of $k$ squares of
integers.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def sumOfSquaresRepCount (k : ℤ) (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((isUnit_squareThetaSeries.unit ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)

/-- **The one-square counts are the coefficients of the square theta series.** For an integer $k$
and $n \ge 0$, let $r_k(n)$ be the coefficient of $q^n$ in $\theta(q)^k$, where $\theta$ is the
square theta series. Then for every $n \ge 0$, $r_1(n)$ equals the coefficient of $q^n$ in
$\theta(q)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem sumOfSquaresRepCount_one (n : ℕ) :
    sumOfSquaresRepCount 1 n = PowerSeries.coeff n squareThetaSeries := by
  simp [sumOfSquaresRepCount]

set_option linter.unusedVariables false in
/-- **Divisibility of square representation counts by a large prime is periodic.** For an integer
$k$ and $n \ge 0$, let $r_k(n)$ be the coefficient of $q^n$ in $\theta(q)^k$, where $\theta$ is the
square theta series; for $k \ge 1$ it is the number of representations of $n$ as an ordered sum of
$k$ squares of integers. Let $n \ge 1$ and $k \ge 1$ be integers and let $p$ be a prime with
$p \ge n + 1$. If $p$ divides $r_k(n)$, then $p$ divides $r_{k+jp}(n)$ for every integer $j$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 3 (`integers-2026-A93-thm-3`). -/
public theorem sumOfSquaresRepCount_add_mul_prime {n k p : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hp : p.Prime) (hpn : n + 1 ≤ p) (h : (p : ℤ) ∣ sumOfSquaresRepCount k n) (r : ℤ) :
    (p : ℤ) ∣ sumOfSquaresRepCount (k + r * p) n := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p
  let reduce := PowerSeries.map (Int.castRingHom (ZMod p))
  let I : Ideal (PowerSeries (ZMod p)) := Ideal.span {PowerSeries.X ^ p}
  let u := isUnit_squareThetaSeries.unit
  let v := Units.map ((Ideal.Quotient.mk I).comp reduce).toMonoidHom u
  -- After reduction modulo p, Frobenius puts the nonconstant part in (X^p).
  have hX : PowerSeries.X ∣ reduce squareThetaSeries - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_map, coeff_squareThetaSeries_small.1, map_one, sub_self]
  have hv : v ^ p = 1 := by
    apply Units.ext
    change Ideal.Quotient.mk I (reduce squareThetaSeries) ^ p = 1
    rw [← map_pow, ← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    simpa only [sub_pow_char, one_pow] using pow_dvd_pow_of_dvd hX p
  -- Equality of the truncated powers applies to integer shifts, since v is a unit.
  have hshift : v ^ ((k : ℤ) + r * p) = v ^ (k : ℤ) := by
    rw [zpow_add, mul_comm r, zpow_mul, zpow_natCast v p, hv, one_zpow, mul_one]
  simp only [v, ← map_zpow] at hshift
  have hcoeff := Ideal.Quotient.eq.mp (congrArg Units.val hshift)
  change reduce (↑(u ^ ((k : ℤ) + r * p))) - reduce (↑(u ^ (k : ℤ))) ∈ I at hcoeff
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hcoeff
  have heq := hcoeff n (Nat.lt_of_succ_le hpn)
  rw [map_sub, PowerSeries.coeff_map, PowerSeries.coeff_map, sub_eq_zero] at heq
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  exact heq.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)

end

end MetaMathlibExt
