/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Floor

/-!
# Base-$p$ digits of rational numbers

`MetaMathlibExt.basePDigit` is the $k$-th base-$p$ digit of a rational number, and
`MetaMathlibExt.basePDigit_div_periodic_one` says that the digits of $m/d$ after the radix
point are constant when $d$ divides $p - 1$.
-/

namespace MetaMathlibExt

/-- **Base-$p$ digits of a rational number.** For a natural number $p$, a rational number $x$ and
an integer $k$, the $k$-th base-$p$ digit of $x$ is $[p^k](x) = \lfloor x / p^k \rfloor \bmod p$;
for $p \ge 1$ this is the residue of $\lfloor x / p^k \rfloor$ modulo $p$ in $\{0, \dots, p - 1\}$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Section 2.2 (definition of `[p^k](x)`). -/
@[expose] public def basePDigit (p : ℕ) (x : ℚ) (k : ℤ) : ℤ := ⌊x / (p : ℚ) ^ k⌋ % p

/-- **Digits of $m/d$ after the radix point are constant.** Let $p$ be a prime, $d$ a divisor of
$p - 1$, and write $[p^j](x)$ for the $j$-th base-$p$ digit of a rational number $x$. For every
positive integer $m$ and every integer $k \ge 1$, $[p^{-(k+1)}](m/d) = [p^{-k}](m/d)$; that is,
the base-$p$ expansion of $m/d$ is periodic with period $1$ right after the radix point.

The source assumes $p$ odd; for $p = 2$ only $d = 1$ occurs.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 2 (`integers-2026-A78-cor-2`). -/
public theorem basePDigit_div_periodic_one (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (m : ℕ) (hm : 0 < m) (k : ℤ) (hk : 1 ≤ k) :
    basePDigit p ((m : ℚ) / d) (-(k + 1)) = basePDigit p ((m : ℚ) / d) (-k) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨t, ht⟩ := hd
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp at ht
      omega
    · exact h
  have hdQ : (p : ℚ) - 1 = (d : ℚ) * (t : ℚ) := by
    have h1 : ((p - 1 : ℕ) : ℚ) = ((d * t : ℕ) : ℚ) := by rw [ht]
    rw [Nat.cast_sub (by omega : 1 ≤ p)] at h1
    push_cast at h1
    linarith
  have hdne : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := by
    refine ⟨(k - 1).toNat, ?_⟩
    have h1 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    omega
  have hfloor : ∀ e : ℕ, ⌊(m : ℚ) / d * (p : ℚ) ^ e⌋ =
      ⌊(m : ℚ) / d⌋ + (m : ℤ) * (t : ℤ) * (∑ i ∈ Finset.range e, (p : ℤ) ^ i) := by
    intro e
    have hgeom : (p : ℚ) ^ e - 1 =
        ((p : ℚ) - 1) * ∑ i ∈ Finset.range e, (p : ℚ) ^ i := by
      rw [← geom_sum_mul]
      ring
    have hval : (m : ℚ) / d * (p : ℚ) ^ e = (m : ℚ) / d +
        (((m : ℤ) * (t : ℤ) * (∑ i ∈ Finset.range e, (p : ℤ) ^ i) : ℤ) : ℚ) := by
      have hcast' : (((m : ℤ) * (t : ℤ) * (∑ i ∈ Finset.range e, (p : ℤ) ^ i) : ℤ) : ℚ) =
          (m : ℚ) * (t : ℚ) * ∑ i ∈ Finset.range e, (p : ℚ) ^ i := by
        push_cast
        rfl
      rw [hcast']
      have h2 : (m : ℚ) / d * (p : ℚ) ^ e =
          (m : ℚ) / d + (m : ℚ) / d * ((p : ℚ) ^ e - 1) := by ring
      rw [h2, hgeom, hdQ]
      field_simp
    rw [hval, Int.floor_add_intCast]
  have hdigit : ∀ e : ℕ, basePDigit p ((m : ℚ) / d) (-(e : ℤ)) =
      ⌊(m : ℚ) / d * (p : ℚ) ^ e⌋ % (p : ℤ) := by
    intro e
    unfold basePDigit
    congr 1
    simp [zpow_neg, div_inv_eq_mul]
  rw [hn]
  have e1 : -((n : ℤ) + 1 + 1) = -(((n + 2 : ℕ) : ℤ)) := by push_cast; ring
  have e2 : -((n : ℤ) + 1) = -(((n + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [e1, e2, hdigit, hdigit, hfloor, hfloor]
  have hsum : ∑ i ∈ Finset.range (n + 2), (p : ℤ) ^ i =
      ∑ i ∈ Finset.range (n + 1), (p : ℤ) ^ i + (p : ℤ) ^ (n + 1) :=
    Finset.sum_range_succ _ _
  have hdvd : (p : ℤ) ∣
      (⌊(m : ℚ) / d⌋ + (m : ℤ) * (t : ℤ) * (∑ i ∈ Finset.range (n + 1), (p : ℤ) ^ i)) -
        (⌊(m : ℚ) / d⌋ + (m : ℤ) * (t : ℤ) * (∑ i ∈ Finset.range (n + 2), (p : ℤ) ^ i)) := by
    rw [hsum, pow_succ]
    use -((m : ℤ) * (t : ℤ) * (p : ℤ) ^ n)
    ring
  exact Int.modEq_iff_dvd.mpr hdvd

end MetaMathlibExt
