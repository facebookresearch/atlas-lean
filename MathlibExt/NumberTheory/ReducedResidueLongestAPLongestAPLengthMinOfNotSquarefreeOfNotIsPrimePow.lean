/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.RingTheory.Radical.Basic
public import MathlibExt.NumberTheory.ReducedResidueLongestAP
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Radical.NatInt
import MathlibExt.NumberTheory.ReducedResiduePrimeBound

/-!
# Minimum longest progression length for non-squarefree non-prime-power moduli

For a modulus that is neither squarefree nor a prime power, every reduced residue window
attains at least the radical quotient, some window attains at most the maximum of the radical
quotient and the largest prime factor minus one, and the minimum over all windows is the
radical quotient when the prime-factor bound does not exceed it.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

open UniqueFactorizationMonoid

namespace longestAPLength_min_of_not_squarefree_of_not_isPrimePow

private theorem lower_bound (m : ℤ) {n : ℕ} (hn : n ≠ 0) :
    n / radical n ≤ longestAPLength m n := by
  let r := radical n
  have hr : 0 < r := Nat.radical_pos n
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
  · have hcop : IsCoprime (1 + k * (r : ℤ) + i * r) (r : ℤ) := by
      simp [isCoprime_one_left]
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply (hcop.pow_right (n := n)).of_isCoprime_of_dvd_right
    exact_mod_cast Nat.dvd_radical_pow_self hn

private theorem span_bound {m b : ℤ} {n d s : ℕ} (hd : 0 < d)
    (hmem : ∀ i < s, b + i * d ∈ reducedResidueWindow m n)
    (hsub : n.primeFactors ⊆ d.primeFactors) : s ≤ n / radical n := by
  have hrd := Nat.le_of_dvd hd ((Nat.radical_dvd_iff hd.ne').mpr hsub)
  have hspan : n ≤ (n / radical n) * d := calc
    n = (n / radical n) * radical n := (Nat.div_mul_cancel radical_dvd_self).symm
    _ ≤ (n / radical n) * d := Nat.mul_le_mul_left _ hrd
  generalize n / radical n = q at hspan ⊢
  by_contra! hs
  have hfirst := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (by omega))).1).1
  have hlast := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem q hs)).1).2
  have hspan' : (n : ℤ) ≤ (q : ℤ) * d := by exact_mod_cast hspan
  simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
  omega

private theorem upper_bound_max (m : ℤ) {n : ℕ} (hn : 1 < n) :
    longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1) := by
  apply csSup_le'
  rintro s ⟨b, d, hd, hmem⟩
  by_cases hsub : n.primeFactors ⊆ d.primeFactors
  · exact (span_bound hd hmem hsub).trans (le_max_left _ _)
  · obtain ⟨p, hpn, hpd⟩ := Finset.not_subset.mp hsub
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hs : s ≤ longestAPLengthWithDiff m n d :=
      le_csSup ⟨n, fun _ ⟨_, ht⟩ => apLength_le hd ht⟩ ⟨b, hmem⟩
    have hprime := longestAPLengthWithDiff_le_prime_sub_one m hn hd hp
      (Nat.dvd_of_mem_primeFactors hpn) (fun hdiv => hpd (hp.mem_primeFactors hdiv hd.ne'))
    have hmax : p ≤ n.primeFactors.sup id := Finset.le_sup (f := id) hpn
    have hs' := hs.trans hprime
    have hle : s ≤ n.primeFactors.sup id - 1 := by omega
    exact hle.trans (le_max_right _ _)

end longestAPLength_min_of_not_squarefree_of_not_isPrimePow

-- The hypotheses are retained from the source statement; the bounds use only `1 < n`.
open longestAPLength_min_of_not_squarefree_of_not_isPrimePow in
set_option linter.unusedVariables false in
/-- **Minimum longest progression length when $n$ is neither squarefree nor a prime power.** Let
$n > 1$ be a natural number that is neither squarefree nor a prime power, $\operatorname{rad}(n)$
the product of its distinct prime factors and $\operatorname{gpf}(n)$ its largest prime factor.
For an integer $m$ let $f_m(n)$ be the length of the longest arithmetic progression with positive
common difference contained in the set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. Then $f_m(n) \ge n / \operatorname{rad}(n)$ for every integer $m$, and
$f_m(n) \le \max(n / \operatorname{rad}(n), \operatorname{gpf}(n) - 1)$ for some integer $m$.
If moreover $\operatorname{gpf}(n) - 1 \le n / \operatorname{rad}(n)$, then the least value of
$f_m(n)$ over all integers $m$ is $n / \operatorname{rad}(n)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem longestAPLength_min_of_not_squarefree_of_not_isPrimePow {n : ℕ}
    (hn : 1 < n) (hsq : ¬ Squarefree n) (hpp : ¬ IsPrimePow n) :
    ((∀ m : ℤ, n / radical n ≤ longestAPLength m n) ∧
      ∃ m : ℤ, longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1)) ∧
    (n.primeFactors.sup id - 1 ≤ n / radical n →
      IsLeast (Set.range fun m : ℤ => longestAPLength m n) (n / radical n)) := by
  refine ⟨⟨fun m => lower_bound m (by omega), ⟨0, upper_bound_max 0 hn⟩⟩, fun h => ?_⟩
  have heq : max (n / radical n) (n.primeFactors.sup id - 1) = n / radical n := max_eq_left h
  have hall : ∀ m : ℤ, longestAPLength m n = n / radical n := fun m =>
    le_antisymm (heq ▸ upper_bound_max m hn) (lower_bound m (by omega))
  constructor
  · exact ⟨0, hall 0⟩
  · rintro _ ⟨m, rfl⟩
    exact lower_bound m (by omega)

end MetaMathlibExt
