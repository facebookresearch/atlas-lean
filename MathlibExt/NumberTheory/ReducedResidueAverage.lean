/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Radical.Basic
public import MathlibExt.NumberTheory.ReducedResiduePrimeBound
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Radical.NatInt

/-!
# Average longest progression length in reduced residue windows

For a modulus greater than one whose largest prime factor minus one is at most the modulus
divided by its radical, every window attains this quotient. Averaging gives the formula for
non-squarefree moduli.
-/

namespace MetaMathlibExt

open UniqueFactorizationMonoid

namespace average_longestAPLength_of_not_squarefree

private theorem upper_bound (m : ℤ) {n : ℕ} (hn : 1 < n)
    (h : n.primeFactors.sup id - 1 ≤ n / radical n) :
    longestAPLength m n ≤ n / radical n := by
  apply csSup_le'
  rintro s ⟨b, d, hd, hmem⟩
  by_cases hsub : n.primeFactors ⊆ d.primeFactors
  · -- After n / rad(n) steps, the progression has advanced by at least n.
    have hrd := Nat.le_of_dvd hd ((Nat.radical_dvd_iff hd.ne').mpr hsub)
    let q := n / radical n
    have hspan : n ≤ q * d := calc
      n = q * radical n := (Nat.div_mul_cancel radical_dvd_self).symm
      _ ≤ q * d := Nat.mul_le_mul_left q hrd
    by_contra! hs
    have hfirst := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (by omega))).1).1
    have hlast := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem q hs)).1).2
    have hspan' : (n : ℤ) ≤ (q : ℤ) * d := by exact_mod_cast hspan
    simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    omega
  · obtain ⟨p, hpn, hpd⟩ := Finset.not_subset.mp hsub
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hs : s ≤ longestAPLengthWithDiff m n d :=
      le_csSup ⟨n, fun _ ⟨_, ht⟩ => apLength_le hd ht⟩ ⟨b, hmem⟩
    have hprime := longestAPLengthWithDiff_le_prime_sub_one m hn hd hp
      (Nat.dvd_of_mem_primeFactors hpn) (fun hdiv => hpd (hp.mem_primeFactors hdiv hd.ne'))
    have hmax : p ≤ n.primeFactors.sup id := Finset.le_sup (f := id) hpn
    omega

private theorem lower_bound (m : ℤ) {n : ℕ} (hn : n ≠ 0) :
    n / radical n ≤ longestAPLength m n := by
  let r := radical n
  have hr : 0 < r := Nat.radical_pos n
  -- Start at the representative of 1 modulo r in the first block of r integers.
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ioc (show (0 : ℤ) < r by exact_mod_cast hr) 1 m
  change m < 1 + k * (r : ℤ) ∧ 1 + k * (r : ℤ) ≤ m + r at hk
  unfold longestAPLength
  refine le_csSup ⟨n, fun _ ⟨_, _, hd, ht⟩ => apLength_le hd ht⟩
    ⟨1 + k * (r : ℤ), r, hr, fun i hi => ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · have hspan : (i + 1) * r ≤ n := calc
      (i + 1) * r ≤ (n / r) * r := Nat.mul_le_mul_right r hi
      _ = n := Nat.div_mul_cancel radical_dvd_self
    have hspan' : ((i : ℤ) + 1) * r ≤ n := by exact_mod_cast hspan
    have hi₀ : 0 ≤ (i : ℤ) * r := by positivity
    apply Finset.mem_Icc.mpr
    constructor <;> linarith [hk.1, hk.2]
  · -- Coprimality with r suffices, since n divides a power of r.
    have hcop : IsCoprime (1 + k * (r : ℤ) + i * r) (r : ℤ) := by
      simp [isCoprime_one_left]
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply (hcop.pow_right (n := n)).of_isCoprime_of_dvd_right
    exact_mod_cast Nat.dvd_radical_pow_self hn

end average_longestAPLength_of_not_squarefree

open average_longestAPLength_of_not_squarefree in
/-- **Every reduced residue window attains the radical quotient.** Let $n > 1$ be a natural
number, $\operatorname{rad}(n)$ the product of its distinct prime factors and
$\operatorname{gpf}(n)$ its largest prime factor, and suppose that
$\operatorname{gpf}(n) - 1 \le n / \operatorname{rad}(n)$. Then for every integer $m$ the length
$f_m(n)$ of the longest arithmetic progression with positive common difference contained in the
set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$ is
$n / \operatorname{rad}(n)$.

Source: Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a
Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6 (the window equality behind
Corollary 1). -/
public theorem longestAPLength_eq_div_radical (m : ℤ) {n : ℕ} (hn : 1 < n)
    (h : n.primeFactors.sup id - 1 ≤ n / radical n) :
    longestAPLength m n = n / radical n :=
  le_antisymm (upper_bound m hn h) (lower_bound m (by omega))

-- The prime-factor bound alone suffices for the window bounds.
set_option linter.unusedVariables false in
/-- **Average longest progression length for non-squarefree moduli.** Let $n > 1$ be a natural
number that is not squarefree, $\operatorname{rad}(n)$ the product of its distinct prime factors
and $\operatorname{gpf}(n)$ its largest prime factor, and suppose that
$\operatorname{gpf}(n) - 1 \le n / \operatorname{rad}(n)$. For an integer $m$ let $f_m(n)$ be the
length of the longest arithmetic progression with positive common difference contained in the
set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then
$\frac{1}{n} \sum_{m=0}^{n-1} f_m(n) = \frac{n}{\operatorname{rad}(n)}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Corollary 1 (`integers-2026-A6-cor-1`). -/
public theorem average_longestAPLength_of_not_squarefree {n : ℕ} (hn : 1 < n)
    (hsq : ¬ Squarefree n) (h : n.primeFactors.sup id - 1 ≤ n / radical n) :
    (1 / (n : ℚ)) * ∑ m ∈ Finset.range n, (longestAPLength m n : ℚ) = (n : ℚ) / radical n := by
  simp_rw [longestAPLength_eq_div_radical _ hn h]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    one_div_mul_cancel (by exact_mod_cast (show n ≠ 0 by omega)), one_mul]
  exact Nat.cast_div radical_dvd_self (by exact_mod_cast (radical_ne_zero (a := n)))

end MetaMathlibExt
