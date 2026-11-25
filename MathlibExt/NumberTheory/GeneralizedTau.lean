/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Generalized tau coefficients

The generalized tau function is defined by the integer powers of Euler's pentagonal series,
with a shift of one degree. Modulo a prime `p`, the Frobenius map makes the `2p`-th power
of the series a power series in `X ^ p`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Euler's product has constant term $1$.** The constant coefficient of the integer power
series $\prod_{m \ge 1} (1 - X^m)$ in $\mathbb{Z}[[X]]$ is $1$.

Source: Euler's pentagonal number theorem as used in Sriram and Christopher, *Congruences
Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function
Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, identity (1). -/
public theorem constantCoeff_pentagonalSeries_int :
    constantCoeff (pentagonalSeries ℤ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  have h := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
  have h0 : pentagonal 0 = 0 := by simp [pentagonal_def]
  rw [h0] at h
  simp [h]

/-- **Euler's product is a unit in $\mathbb{Z}[[X]]$.** Euler's pentagonal series
$\sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k - 1)/2}$, which equals $\prod_{m \ge 1} (1 - X^m)$, is a
unit of the ring $\mathbb{Z}[[X]]$ of formal power series with integer coefficients, so all its
integer powers are defined.

Source: Sriram and Christopher, *Congruences Relating Regular Partition Functions, a Generalized
Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article
A39, Definition 1.1 (negative exponents). -/
public theorem isUnit_pentagonalSeries_int : IsUnit (pentagonalSeries ℤ) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_pentagonalSeries_int]
  exact isUnit_one

/-- **Generalized tau function.** For an integer $k$ and a natural number $n$, the generalized tau
function $\tau_k(n)$ is the coefficient of $q^n$ in the integer power series
$q \prod_{m \ge 1} (1 - q^m)^k$. For negative $k$ the power is taken in the group of units of
$\mathbb{Z}[[q]]$, where $\prod_{m \ge 1} (1 - q^m)$ is invertible because its constant term is $1$.

The paper requires $k \ne 0$; $k = 0$ gives $\tau_0(1) = 1$ and $\tau_0(n) = 0$ for $n \ne 1$.
$\tau_{24}$ is Ramanujan's tau function, and $\tau_1(n + 1)$ is Euler's $\omega(n)$, the
coefficient of $q^n$ in $\prod_{m \ge 1} (1 - q^m)$.

Source: Sriram and Christopher, *Congruences Relating Regular Partition Functions, a Generalized
Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article
A39, Definition 1.1, equation (2). -/
public noncomputable def generalizedTau (k : ℤ) (n : ℕ) : ℤ :=
  coeff n (X * ((isUnit_pentagonalSeries_int.unit ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧))

/-- **Generalized tau function at zero.** For every integer $k$, $\tau_k(0) = 0$, where $\tau_k$
is the generalized tau function: the series $q \prod_{m \ge 1} (1 - q^m)^k$ has no constant term.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_zero (k : ℤ) : generalizedTau k 0 = 0 := by
  simp [generalizedTau]

/-- **The generalized tau function at $1$.** For every integer $k$, $\tau_k(1) = 1$.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_one (k : ℤ) : generalizedTau k 1 = 1 := by
  rw [generalizedTau, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hu : Units.map (constantCoeff (R := ℤ)).toMonoidHom isUnit_pentagonalSeries_int.unit
      = 1 := by
    ext
    simp [constantCoeff_pentagonalSeries_int]
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (congrArg (· ^ k) hu)
  simp only [one_zpow, Units.val_one, ← map_zpow, Units.coe_map] at h
  exact h

/-- **The generalized tau function for natural exponents.** For natural numbers $k$ and $n$,
$\tau_k(n)$ is the coefficient of $q^n$ in the integer power series
$q \bigl(\prod_{m \ge 1} (1 - q^m)\bigr)^k$.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_natCast (k n : ℕ) :
    generalizedTau k n = coeff n (X * pentagonalSeries ℤ ^ k) := by
  simp [generalizedTau]

/-- **$\tau_{2p}(n + 1)$ vanishes modulo $p$ when $p \nmid n$.** Let $p$ be an odd prime and $n$ a
natural number not divisible by $p$. Then $\tau_{2p}(n + 1) \equiv 0 \pmod{p}$.

The record prints the hypothesis as $p \nmid n + 1$; that is false, and the corollary follows from
Theorem 3.26 (the record's Theorem 16) in its corrected form, which forces $p \mid n$ for a nonzero
residue.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Corollary 4 (`integers-2024-A39-cor-4`). -/
public theorem generalizedTau_two_mul_prime_succ_modEq_zero (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) (hn : ¬ p ∣ n) :
    generalizedTau (2 * p) (n + 1) ≡ 0 [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [show (2 : ℤ) * p = ((2 * p : ℕ) : ℤ) by simp, generalizedTau_natCast,
    coeff_succ_X_mul, pow_mul, ← ZMod.intCast_eq_intCast_iff, Int.cast_zero]
  change (Int.castRingHom (ZMod p)) _ = 0
  rw [← coeff_map, map_pow, ← map_frobenius_expand p hodd.pos.ne', coeff_map,
    coeff_expand_of_not_dvd p hodd.pos.ne' _ hn, map_zero]

end

end MetaMathlibExt
