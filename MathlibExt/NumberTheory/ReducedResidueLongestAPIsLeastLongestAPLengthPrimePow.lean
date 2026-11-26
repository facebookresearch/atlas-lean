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
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Minimum longest progression length modulo a prime power

For a prime `p` and a natural number `r > 1`, the least value over all integers `m` of the
length of the longest arithmetic progression with positive common difference in the reduced
residue system `R_m (p ^ r)` is `p ^ (r - 1)`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.

The two bounds adapt the `lower_bound` and `upper_bound` proofs in
`MathlibExt/NumberTheory/ReducedResidueAverage.lean`, with the radical of `p ^ r` equal to `p`.
-/

namespace MetaMathlibExt

@[expose] public section

namespace isLeast_longestAPLength_prime_pow

private theorem lower_bound (m : ℤ) {p t : ℕ} (hp : p.Prime) :
    p ^ t ≤ longestAPLength m (p ^ (t + 1)) := by
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ioc (show (0 : ℤ) < p by exact_mod_cast hp.pos)
    1 m
  change m < 1 + k * (p : ℤ) ∧ 1 + k * (p : ℤ) ≤ m + p at hk
  unfold longestAPLength
  refine le_csSup ⟨p ^ (t + 1), fun _ ⟨_, _, hd, ht⟩ => apLength_le hd ht⟩
    ⟨1 + k * (p : ℤ), p, hp.pos, fun i hi => ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · have hspan : (i + 1) * p ≤ p ^ (t + 1) := calc
      (i + 1) * p ≤ p ^ t * p := Nat.mul_le_mul_right p hi
      _ = p ^ (t + 1) := (pow_succ _ _).symm
    have hspan' : ((i : ℤ) + 1) * p ≤ ((p ^ (t + 1) : ℕ) : ℤ) := by exact_mod_cast hspan
    have hi₀ : 0 ≤ (i : ℤ) * p := by positivity
    apply Finset.mem_Icc.mpr
    constructor <;> linarith [hk.1, hk.2]
  · have hcop : IsCoprime (1 + k * (p : ℤ) + i * p) (p : ℤ) := by
      simp [isCoprime_one_left]
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact_mod_cast hcop.pow_right (n := t + 1)

private theorem upper_bound (m : ℤ) {p t : ℕ} (hp : p.Prime) (ht : 1 ≤ t) :
    longestAPLength m (p ^ (t + 1)) ≤ p ^ t := by
  apply csSup_le'
  rintro s ⟨b, d, hd, hmem⟩
  by_cases hdiv : p ∣ d
  · have hpd : p ≤ d := Nat.le_of_dvd hd hdiv
    have hspan : p ^ (t + 1) ≤ p ^ t * d := by
      rw [pow_succ]
      exact Nat.mul_le_mul_left _ hpd
    by_contra! hs
    have hfirst := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (by omega))).1).1
    have hlast := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem (p ^ t) hs)).1).2
    have hspan' : ((p ^ (t + 1) : ℕ) : ℤ) ≤ (p ^ t : ℤ) * d := by exact_mod_cast hspan
    simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    omega
  · have hs : s ≤ longestAPLengthWithDiff m (p ^ (t + 1)) d :=
      le_csSup ⟨p ^ (t + 1), fun _ ⟨_, hterm⟩ => apLength_le hd hterm⟩ ⟨b, hmem⟩
    have hprime := longestAPLengthWithDiff_le_prime_sub_one m (n := p ^ (t + 1)) (d := d)
      (p := p) (one_lt_pow' hp.one_lt (by omega)) hd hp (dvd_pow_self p (by omega)) hdiv
    have hsub : p - 1 ≤ p ^ t := (Nat.sub_le _ _).trans (le_self_pow hp.one_le (by omega))
    exact hs.trans (hprime.trans hsub)

end isLeast_longestAPLength_prime_pow

open isLeast_longestAPLength_prime_pow in
/-- **Minimum longest progression length modulo a prime power.** Let $p$ be a prime and $r > 1$ a
natural number. For an integer $m$ let $f_m(p^r)$ be the length of the longest arithmetic
progression with positive common difference contained in the set $R_m(p^r)$ of integers $a$ with
$m + 1 \le a \le m + p^r$ and $\gcd(a, p^r) = 1$. Then the least value of $f_m(p^r)$ over all
integers $m$ is $p^{r-1}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem isLeast_longestAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 < r) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m (p ^ r)) (p ^ (r - 1)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have ht : 1 ≤ t := by omega
  constructor
  · exact ⟨0, le_antisymm (upper_bound 0 hp ht) (lower_bound 0 hp)⟩
  · rintro _ ⟨m, rfl⟩
    exact lower_bound m hp

end

end MetaMathlibExt
