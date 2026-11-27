/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# A prime window congruence for triangular representation counts

Reducing the triangular theta series `f` modulo `p` turns the sum of `p` consecutive powers
into a power of `f` times `(f - 1) ^ (p - 1)`. Since `f` has constant coefficient `1`, the
coefficients of this sum below degree `p - 1` vanish.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Triangular theta series.** The triangular theta series is the formal power series
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$ with integer coefficients: for each natural number $n$,
its coefficient of $q^n$ is the number of natural numbers $m$ with $m(m+1)/2 = n$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def triangularThetaSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (((Finset.range (n + 1)).filter fun m => m * (m + 1) / 2 = n).card : ℤ)

/-- **First coefficients of the triangular theta series.** In the triangular theta series
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$, the coefficients of $q^0$, $q^1$, $q^2$ and $q^3$ are $1$,
$1$, $0$ and $1$ respectively.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem coeff_triangularThetaSeries_small :
    PowerSeries.coeff 0 triangularThetaSeries = 1 ∧ PowerSeries.coeff 1 triangularThetaSeries = 1 ∧
      PowerSeries.coeff 2 triangularThetaSeries = 0 ∧
        PowerSeries.coeff 3 triangularThetaSeries = 1 := by
  simp only [triangularThetaSeries, PowerSeries.coeff_mk]
  decide

/-- **The triangular theta series is a unit.** The triangular theta series
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$ is a unit of the ring $\mathbb{Z}[[q]]$ of formal power
series with integer coefficients, since its constant coefficient is $1$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem isUnit_triangularThetaSeries : IsUnit triangularThetaSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_triangularThetaSeries_small.1]
  exact isUnit_one

/-- **Representation numbers for sums of triangular numbers.** For an integer $k$ and a natural
number $n$, $t_k(n)$ is the coefficient of $q^n$ in $\psi(q)^k$, where
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. Since $\psi$ has constant coefficient $1$, it is a unit of
$\mathbb{Z}[[q]]$, so $\psi^k$ is a power series for negative $k$ as well.

For $k \ge 1$, $t_k(n)$ is the number of ways to write $n$ as an ordered sum of $k$ triangular
numbers $m(m+1)/2$ with $m \ge 0$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def sumOfTriangularRepCount (k : ℤ) (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((isUnit_triangularThetaSeries.unit ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)

set_option linter.unusedVariables false in
/-- **Prime divisibility of triangular representation numbers persists under prime shifts.** For an
integer $k$, let $t_k(n)$ be the coefficient of $q^n$ in $\psi(q)^k$, where
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. Let $n \ge 1$ and $k \ge 1$ be natural numbers and let $p$
be a prime with $p \ge n + 1$. If $p$ divides $t_k(n)$, then $p$ divides $t_{k+rp}(n)$ for every
integer $r$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 4 (`integers-2026-A93-thm-4`). -/
public theorem sumOfTriangularRepCount_add_mul_prime {n k p : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hp : p.Prime) (hpn : n + 1 ≤ p)
    (h : (p : ℤ) ∣ sumOfTriangularRepCount k n) (r : ℤ) :
    (p : ℤ) ∣ sumOfTriangularRepCount (k + r * p) n := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p
  let reduce := PowerSeries.map (Int.castRingHom (ZMod p))
  let I : Ideal (PowerSeries (ZMod p)) := Ideal.span {PowerSeries.X ^ p}
  let u := isUnit_triangularThetaSeries.unit
  let v := Units.map ((Ideal.Quotient.mk I).comp reduce).toMonoidHom u
  -- After reduction modulo p, Frobenius puts the nonconstant part in (X^p).
  have hX : PowerSeries.X ∣ reduce triangularThetaSeries - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_map, coeff_triangularThetaSeries_small.1, map_one, sub_self]
  have hv : v ^ p = 1 := by
    apply Units.ext
    change Ideal.Quotient.mk I (reduce triangularThetaSeries) ^ p = 1
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

set_option linter.unusedVariables false in
/-- **Window congruence for sums of triangular numbers.** For an integer $k$, let $t_k(n)$ be the
coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. Let $n \ge 1$,
let $p$ be an odd prime with $p - 1 \ge n + 1$, and let $s \ge p$ be an integer. Then $p$ divides
$\sum_{i=0}^{p-1} t_{s-i}(n)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 6 (`integers-2026-A93-thm-6`). -/
public theorem sum_sumOfTriangularRepCount_window {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) {s : ℤ} (hs : (p : ℤ) ≤ s) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, sumOfTriangularRepCount (s - i) n := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p
  let reduce := PowerSeries.map (Int.castRingHom (ZMod p))
  let f := reduce triangularThetaSeries
  have h0 : PowerSeries.constantCoeff f = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.coeff 0 (reduce triangularThetaSeries) = _
    rw [PowerSeries.coeff_map, coeff_triangularThetaSeries_small.1, map_one]
  have hX : PowerSeries.X ∣ f - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_one, h0, sub_self]
  have hf : f - 1 ≠ 0 := by
    intro h
    have h₁ := congrArg (PowerSeries.coeff 1) (sub_eq_zero.mp h)
    change PowerSeries.coeff 1 (reduce triangularThetaSeries) = _ at h₁
    rw [PowerSeries.coeff_map, coeff_triangularThetaSeries_small.2.1, map_one] at h₁
    simp at h₁
  -- Multiply by `f - 1` to compare the geometric sum and the Frobenius power.
  have hgeom : ∑ i ∈ Finset.range p, f ^ i = (f - 1) ^ (p - 1) := by
    apply mul_right_cancel₀ hf
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.pos, sub_pow_char, one_pow]
  let m := s.toNat - (p - 1)
  have hexp (i : ℕ) (hi : i < p) : s - (i : ℤ) = ((m + (p - 1 - i) : ℕ) : ℤ) := by
    dsimp [m]
    omega
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  calc
    (↑(∑ i ∈ Finset.range p, sumOfTriangularRepCount (s - i) n) : ZMod p) =
        ∑ i ∈ Finset.range p, PowerSeries.coeff n (f ^ (m + (p - 1 - i))) := by
      rw [Int.cast_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hexp i (Finset.mem_range.mp hi)]
      simp only [sumOfTriangularRepCount, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      change Int.castRingHom (ZMod p) (PowerSeries.coeff n _) = _
      rw [← PowerSeries.coeff_map, ← map_pow]
    _ = PowerSeries.coeff n (f ^ m * ∑ i ∈ Finset.range p, f ^ i) := by
      simp only [pow_add, Finset.mul_sum, map_sum]
      exact Finset.sum_range_reflect (fun i => PowerSeries.coeff n (f ^ m * f ^ i)) p
    _ = 0 := by
      rw [hgeom]
      exact PowerSeries.X_pow_dvd_iff.mp
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hX (p - 1)) _) n (Nat.lt_of_succ_le hpn)

end

end MetaMathlibExt
