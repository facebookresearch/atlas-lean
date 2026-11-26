/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ReducedResidueLongestAP
import MathlibExt.NumberTheory.ReducedResiduePrimeBound
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Longest progressions of absolute least residues modulo prime powers

For a prime power `p ^ r` with `r ≥ 1` (and `r ≥ 2` when `p` is odd), every reduced residue
window has longest progression length `p ^ (r - 1)`, so the absolute least length is `p ^ (r - 1)`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

private theorem prime_sub_one_le_pow_pred (p r : ℕ) (hp : p.Prime)
    (h : p = 2 ∨ 2 ≤ r) : p - 1 ≤ p ^ (r - 1) := by
  rcases h with rfl | hr2
  · calc 2 - 1 = 1 := by decide
      _ ≤ 2 ^ (r - 1) := Nat.one_le_pow _ _ (by decide)
  · have h1 : 1 ≤ r - 1 := by omega
    have hpow : p ^ 1 ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos h1
    rw [pow_one] at hpow
    omega

private theorem lower_bound (m : ℤ) (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    p ^ (r - 1) ≤ longestAPLength m (p ^ r) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ioc hp0 (1 : ℤ) m
  change m < 1 + k * (p : ℤ) ∧ 1 + k * (p : ℤ) ≤ m + p at hk
  have hpow : p ^ (r - 1) * p = p ^ r := pow_sub_one_mul (by omega : r ≠ 0) p
  unfold longestAPLength
  refine le_csSup ⟨p ^ r, fun _ ⟨_, _, hd, ht⟩ => apLength_le hd ht⟩
    ⟨1 + k * (p : ℤ), p, hp.pos, fun i hi => ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · have hspan : (i + 1) * p ≤ p ^ r := calc
      (i + 1) * p ≤ p ^ (r - 1) * p := Nat.mul_le_mul_right p hi
      _ = p ^ r := hpow
    have hspan' : ((i : ℤ) + 1) * p ≤ p ^ r := by exact_mod_cast hspan
    have hi0 : (0 : ℤ) ≤ (i : ℤ) * p := by positivity
    apply Finset.mem_Icc.mpr
    constructor <;> push_cast <;> linarith [hk.1, hk.2, hspan', hi0]
  · apply Int.isCoprime_iff_gcd_eq_one.mp
    have hcop1 : IsCoprime (1 + k * (p : ℤ) + (i : ℤ) * p) (p : ℤ) := by
      have heq : 1 + k * (p : ℤ) + (i : ℤ) * p = 1 + (p : ℤ) * (k + i) := by ring
      rw [heq]
      exact IsCoprime.add_mul_left_left isCoprime_one_left _
    have hpow2 : IsCoprime (1 + k * (p : ℤ) + (i : ℤ) * p) ((p : ℤ) ^ r) := hcop1.pow_right
    have hcast : (((p ^ r : ℕ) : ℤ)) = (p : ℤ) ^ r := by push_cast; ring
    rw [hcast]
    exact hpow2

private theorem upper_bound (m : ℤ) (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    (h : p = 2 ∨ 2 ≤ r) : longestAPLength m (p ^ r) ≤ p ^ (r - 1) := by
  apply csSup_le'
  rintro s ⟨b, d, hd, hmem⟩
  by_cases hpd : p ∣ d
  · have hle : p ≤ d := Nat.le_of_dvd hd hpd
    have hpow : p ^ (r - 1) * p = p ^ r := pow_sub_one_mul (by omega : r ≠ 0) p
    have hspan : p ^ r ≤ p ^ (r - 1) * d := calc
      p ^ r = p ^ (r - 1) * p := hpow.symm
      _ ≤ p ^ (r - 1) * d := Nat.mul_le_mul_left _ hle
    by_contra! hs
    have hfirst := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (by omega))).1).1
    have hlast := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem (p ^ (r - 1)) hs)).1).2
    have hspan' : ((p ^ r : ℕ) : ℤ) ≤ ((p ^ (r - 1) : ℕ) : ℤ) * d := by exact_mod_cast hspan
    simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    omega
  · have hn : 1 < p ^ r := Nat.one_lt_pow (by omega) hp.one_lt
    have hpn : p ∣ p ^ r := dvd_pow_self p (by omega)
    have hs : s ≤ longestAPLengthWithDiff m (p ^ r) d :=
      le_csSup ⟨p ^ r, fun _ ⟨_, ht⟩ => apLength_le hd ht⟩ ⟨b, hmem⟩
    have hprime := longestAPLengthWithDiff_le_prime_sub_one m hn hd hp hpn hpd
    have hle : p - 1 ≤ p ^ (r - 1) := prime_sub_one_le_pow_pred p r hp h
    omega

/-- **Longest progressions of absolute least residues: prime powers.** Let $p$ be a prime and
$r \ge 1$, with $r \ge 2$ when $p$ is odd. Then the length $g(p^r)$ of the longest arithmetic
progression in the absolute least reduced residue system modulo $p^r$ is $p^{r-1}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem absLeastAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (h : p = 2 ∨ 2 ≤ r) : absLeastAPLength (p ^ r) = p ^ (r - 1) := by
  unfold absLeastAPLength
  exact le_antisymm (upper_bound _ _ _ hp hr h) (lower_bound _ _ _ hp hr)

end MetaMathlibExt
