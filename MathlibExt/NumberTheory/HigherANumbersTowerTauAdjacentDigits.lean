/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Floor

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Adjacent base-`p` digits in the higher `a`-number tower

For a prime `p`, a natural number `d` dividing `p - 1`, and `τ = (p + 1)/d`, the two
base-`p` digits of `τ i` next to the radix point agree exactly when `p ∣ i`, for every
natural number `i`.

For the same `p` and `d` and any positive integer `m`, the digits of `m/d` at positions
`-(k + 1)` and `-k` agree for each integer `k ≥ 1`. The paper assumes `p` is odd; when
`p = 2`, `d = 1` and all digits after the radix point are zero.

## References

* Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
  *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026),
  Article A78, pp. 1–28, Notation 1 (i), Definition 5, Corollary 2, and Lemma 3.
* The paper's proof of Corollary 2 uses Lemma 2, which cites G. H. Hardy and E. M. Wright,
  *An Introduction to the Theory of Numbers*, 6th ed., Oxford University Press, 2008,
  Theorem 136. This proof uses the floor shift from `basePDigit_towerTau_neg_one_eq_zero_iff`
  in `MathlibExt.NumberTheory.HigherANumbersTowerTauAdjacentDigits` instead.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Base-$p$ digits of a rational number.** For a natural number $p$, a rational number $x$ and
an integer $k$, the $k$-th base-$p$ digit of $x$ is $[p^k](x) = \lfloor x / p^k \rfloor \bmod p$;
for $p \ge 1$ this is the residue of $\lfloor x / p^k \rfloor$ modulo $p$ in $\{0, \dots, p - 1\}$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Section 2.2 (definition of `[p^k](x)`). -/
def basePDigit (p : ℕ) (x : ℚ) (k : ℤ) : ℤ := ⌊x / (p : ℚ) ^ k⌋ % p

/-- **The ratio $\tau = (p + 1)/d$.** For natural numbers $p$ and $d$, $\tau$ is the rational
number $(p + 1)/d$, which is $0$ when $d = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 1 (i). -/
def towerTau (p d : ℕ) : ℚ := ((p : ℚ) + 1) / d

/-- **Digits of $\tau i$ next to the radix point.** Let $p$ be a prime, $d$ a divisor of $p - 1$
and $\tau = (p + 1)/d$, and write $[p^j](x)$ for the $j$-th base-$p$ digit of a rational number
$x$. For every natural number $i$, $[p^{-1}](\tau i) = [p^0](\tau i)$ if and only if $p$ divides
$i$.

The source's positivity assumption on $i$ is dropped (the claim holds at $i = 0$), and $p$ is any
prime.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 3 (`integers-2026-A78-lem-3`). -/
public theorem basePDigit_towerTau_neg_one_eq_zero_iff (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (i : ℕ) :
    basePDigit p (towerTau p d * i) (-1) = basePDigit p (towerTau p d * i) 0 ↔ p ∣ i := by
  have hp : p.Prime := Fact.out
  have hpSub : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨c, hc⟩ := hd
  have hdPos : 0 < d := Nat.pos_of_ne_zero fun h => hpSub.ne' (by simpa [h] using hc)
  have hcPos : 0 < c := Nat.pos_of_ne_zero fun h => hpSub.ne' (by simpa [h] using hc)
  have hcLe : c ≤ p - 1 := Nat.le_of_dvd hpSub ⟨d, hc.trans (Nat.mul_comm d c)⟩
  have hcLt : c < p := by omega
  have hq : (p : ℚ) - 1 = (d : ℚ) * (c : ℚ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp.one_lt.le, hc, Nat.cast_mul]
  let x : ℚ := towerTau p d * i
  let k : ℕ := (p + 1) * c * i
  have hstep : x * (p : ℚ) = x + (k : ℚ) := calc
    x * (p : ℚ) = x + x * ((p : ℚ) - 1) := by ring
    _ = x + (k : ℚ) := by
      rw [hq]
      simp only [x, k, towerTau, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [Nat.cast_ne_zero.mpr hdPos.ne']
  rw [← Int.cast_natCast k] at hstep
  change basePDigit p x (-1) = basePDigit p x 0 ↔ p ∣ i
  simp only [basePDigit, zpow_neg_one, div_inv_eq_mul, zpow_zero, div_one, hstep,
    Int.floor_add_intCast]
  change (⌊x⌋ + (k : ℤ) ≡ ⌊x⌋ [ZMOD (p : ℤ)]) ↔ p ∣ i
  rw [Int.modEq_comm, Int.modEq_iff_dvd, add_sub_cancel_left, Int.natCast_dvd_natCast]
  have hnext : ¬ p ∣ p + 1 := by
    rw [← Nat.dvd_add_iff_right (dvd_refl p), Nat.dvd_one]
    exact hp.one_lt.ne'
  have hcNotDvd : ¬ p ∣ c := fun h => (not_le_of_gt hcLt) (Nat.le_of_dvd hcPos h)
  simp only [k, hp.dvd_mul, hnext, hcNotDvd, false_or]

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
  have _ := hm -- The source requires positivity, although the digit calculation does not.
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  simp only [basePDigit, zpow_neg, div_inv_eq_mul, ← Int.natCast_succ, zpow_natCast]
  by_cases hpTwo : p = 2
  · subst p
    have hdOne : d = 1 := Nat.dvd_one.mp hd
    subst d
    simp only [Nat.cast_one, div_one, ← Nat.cast_pow, ← Nat.cast_mul, Int.floor_natCast]
    simp only [Nat.cast_mul, Nat.cast_pow, pow_succ, ← mul_assoc, Int.mul_emod_left]
  have hp : p.Prime := Fact.out
  have hd₀ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr
    (ne_zero_of_dvd_ne_zero (Nat.sub_pos_of_lt hp.one_lt).ne' hd)
  obtain ⟨c, hc⟩ := hd
  have hpc : (p : ℚ) - 1 = (d : ℚ) * c := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp.one_lt.le, hc, Nat.cast_mul]
  have hmul : (m : ℚ) / d * ((p : ℚ) - 1) = (m : ℚ) * c := by
    rw [hpc, ← mul_assoc, div_mul_cancel₀ _ hd₀]
  -- The difference between successive scaled rationals is an integer multiple of p.
  have hstep : (m : ℚ) / d * (p : ℚ) ^ (n + 1 + 1) =
      (m : ℚ) / d * (p : ℚ) ^ (n + 1) + ((m * c * p ^ n * p : ℕ) : ℚ) := by
    calc
      _ = (m : ℚ) / d * (p : ℚ) ^ (n + 1) +
          ((m : ℚ) / d * ((p : ℚ) - 1)) * (p : ℚ) ^ (n + 1) := by
        rw [pow_succ _ (n + 1)]
        ring
      _ = _ := by
        rw [hmul, pow_succ _ n]
        simp only [Nat.cast_mul, Nat.cast_pow, mul_assoc]
  rw [hstep, Int.floor_add_natCast, Nat.cast_mul, Int.add_mul_emod_self_right]

end

end MetaMathlibExt
