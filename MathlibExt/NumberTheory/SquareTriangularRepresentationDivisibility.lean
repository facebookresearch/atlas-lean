/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareRepresentationCongruences
public import MathlibExt.NumberTheory.TriangularRepresentationWindow

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Prime divisibility of square and triangular representation counts

Reduction modulo a prime and Frobenius give the divisibility of both counts.
-/

namespace MetaMathlibExt

private theorem dvd_coeff_pow_of_not_dvd {n q : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n)
    (f : PowerSeries ℤ) : (q : ℤ) ∣ PowerSeries.coeff n (f ^ q) := by
  let _ : Fact q.Prime := ⟨hq⟩
  let reduce := Int.castRingHom (ZMod q)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  change reduce (PowerSeries.coeff n (f ^ q)) = 0
  -- Frobenius sends the reduced series to one supported on multiples of q.
  rw [← PowerSeries.coeff_map, map_pow, ← PowerSeries.map_frobenius_expand q hq.ne_zero,
    PowerSeries.coeff_map, PowerSeries.coeff_expand_of_not_dvd q hq.ne_zero _ hn, map_zero]

-- The bounds already imply `¬ q ∣ p`; retain the source's assumptions on `p`.
set_option linter.unusedVariables false in
/-- **A prime between $p/2$ and $p$ divides the representation counts of $p$.** For integers
$k, n \ge 1$, let $r_k(n)$ be the number of representations of $n$ as an ordered sum of $k$ squares
of integers and $t_k(n)$ the number of representations of $n$ as an ordered sum of $k$ triangular
numbers $m(m+1)/2$ with $m \ge 0$. Let $p$ be an odd prime and $\ell$ a prime with
$p/2 < \ell < p$. Then $\ell$ divides both $r_\ell(p)$ and $t_\ell(p)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 11 (`integers-2026-A93-thm-11`). -/
public theorem prime_dvd_repCount_of_half_lt {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hpq : p < 2 * q) (hqp : q < p) :
    (q : ℤ) ∣ sumOfSquaresRepCount q p ∧ (q : ℤ) ∣ sumOfTriangularRepCount q p := by
  have hndvd : ¬ q ∣ p := Nat.not_dvd_of_lt_of_lt_mul_succ (k := 1)
    (by simpa only [Nat.mul_one] using hqp) (by simpa only [Nat.mul_comm] using hpq)
  constructor
  · simpa only [sumOfSquaresRepCount, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      using dvd_coeff_pow_of_not_dvd hq hndvd squareThetaSeries
  · simpa only [sumOfTriangularRepCount, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      using dvd_coeff_pow_of_not_dvd hq hndvd triangularThetaSeries

end MetaMathlibExt
