/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ReducedResidueLongestAP

import Mathlib.Algebra.Field.ZMod

/-! # A prime divisor bound in reduced residue windows

A progression with a difference invertible modulo a prime reaches zero modulo that prime
among its first `p` terms.
-/

namespace MetaMathlibExt

-- The bounds on the modulus and difference are retained from the statement in the source.
set_option linter.unusedVariables false in
/-- **Prime bound for progressions with a fixed difference.** Let $m$ be an integer, $n > 1$ and
$d > 0$ natural numbers, and $p$ a prime that divides $n$ but not $d$. Then $f_m(d, n) \le p - 1$,
where $f_m(d, n)$ is the length of the longest arithmetic progression with common difference $d$
contained in the set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Lemma 1(i) (`integers-2026-A6-lem-1`). -/
public theorem longestAPLengthWithDiff_le_prime_sub_one (m : ℤ) {n d p : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hp : p.Prime) (hpn : p ∣ n) (hpd : ¬ p ∣ d) :
    longestAPLengthWithDiff m n d ≤ p - 1 := by
  apply csSup_le'
  rintro s ⟨b, h⟩
  let : Fact p.Prime := ⟨hp⟩
  -- Take the least residue of the same zero-producing index used for the squarefree bound.
  let x : ZMod p := -(b : ZMod p) / (d : ZMod p)
  have hx : x.val < p := x.val_lt
  have hpterm : (p : ℤ) ∣ b + (x.val : ℤ) * d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    have hd₀ : (d : ZMod p) ≠ 0 := fun hz => hpd ((ZMod.natCast_eq_zero_iff ..).mp hz)
    rw [ZMod.natCast_zmod_val, show x = -(b : ZMod p) / (d : ZMod p) from rfl,
      div_mul_cancel₀ _ hd₀, add_neg_cancel]
  have hs : s ≤ x.val := by
    by_contra! hi
    have hgcd := (Finset.mem_filter.mp (h x.val hi)).2
    have hcommon := Int.dvd_coe_gcd hpterm (Int.natCast_dvd_natCast.mpr hpn)
    rw [hgcd] at hcommon
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hcommon)
  omega

end MetaMathlibExt
