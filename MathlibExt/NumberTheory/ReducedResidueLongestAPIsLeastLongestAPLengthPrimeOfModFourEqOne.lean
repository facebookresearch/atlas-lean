/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ReducedResidueLongestAP
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Minimum longest progression length modulo a prime `p ≡ 1 mod 4`

For a prime `p` with `p % 4 = 1`, the least value over all integers `m` of the length `f_m(p)`
of the longest arithmetic progression with positive common difference in the reduced residue
window `R_m(p)` is `(p - 1) / 2`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

namespace isLeast_longestAPLength_prime_of_mod_four_eq_one

-- All points of the window except its unique multiple of `p` are reduced residues.
private theorem window_except_multiple (m : ℤ) {p : ℕ} (hp : p.Prime) :
    ∃ z : ℤ, ∀ x : ℤ, m < x → x ≤ m + p → x ≠ z → x ∈ reducedResidueWindow m p := by
  have h : ∃! j : ℤ, (p : ℤ) * j ∈ Set.Ioc m (m + p) := by
    simpa only [zsmul_eq_mul, Int.cast_id, zero_add, mul_comm] using
      existsUnique_add_zsmul_mem_Ioc (show (0 : ℤ) < p by exact_mod_cast hp.pos) 0 m
  obtain ⟨j, _, hj⟩ := h
  refine ⟨p * j, fun x hx hx' hne => ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hx'⟩, ?_⟩
  change x.natAbs.Coprime p
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hdiv
  obtain ⟨k, rfl⟩ := Int.natCast_dvd.mpr hdiv
  exact hne (congrArg ((p : ℤ) * ·) (hj k ⟨hx, hx'⟩))

-- Every window contains a progression of length `2 * k` on the side away from the multiple.
private theorem lower_bound (m : ℤ) {p k : ℕ} (hp : p.Prime) (hpk : p = 4 * k + 1) :
    2 * k ≤ longestAPLength m p := by
  obtain ⟨z, hmem⟩ := window_except_multiple m hp
  unfold longestAPLength
  refine le_csSup ⟨p, fun _ ⟨_, _, hd, h⟩ => apLength_le hd h⟩ ?_
  rcases lt_or_ge z (m + 2 * k + 1) with h | h
  · refine ⟨m + 2 * k + 1, 1, one_pos, fun i hi => ?_⟩
    apply hmem <;> push_cast <;> omega
  · refine ⟨m + 1, 1, one_pos, fun i hi => ?_⟩
    apply hmem <;> push_cast <;> omega

-- The centered window has no progression longer than `2 * k`.
private theorem centered_upper_bound {p k : ℕ} (hp : p.Prime) (hpk : p = 4 * k + 1) :
    longestAPLength (-(2 * (k : ℤ) + 1)) p ≤ 2 * k := by
  have hk : 1 ≤ k := by
    have h2 := hp.two_le
    omega
  apply csSup_le'
  rintro s ⟨b, d, hd, h⟩
  by_contra! hs
  have hfirst := (Finset.mem_Icc.mp (Finset.mem_filter.mp (h 0 (by omega))).1).1
  have hlast := (Finset.mem_Icc.mp (Finset.mem_filter.mp (h (2 * k) hs)).1).2
  push_cast at hfirst hlast
  -- A step of three or more would already put this term outside the window.
  have hd2 : d ≤ 2 := by
    by_contra hcon
    have hmul := mul_le_mul_of_nonneg_left (show (3 : ℤ) ≤ d by omega)
      (show (0 : ℤ) ≤ 2 * k by positivity)
    omega
  have hd12 : d = 1 ∨ d = 2 := by omega
  rcases hd12 with rfl | rfl
  · -- With step one the progression must pass through zero.
    have hb : b ≤ 0 := by omega
    have hi : (-b).toNat < s := by omega
    have hzero := (Finset.mem_filter.mp (h (-b).toNat hi)).2
    apply hp.ne_one
    simpa [Int.toNat_of_nonneg (neg_nonneg.mpr hb)] using hzero
  · -- With step two the progression spans the window, so it passes through zero.
    have hb : b = -(2 * (k : ℤ)) := by omega
    have hi : k < s := by omega
    have hzero := (Finset.mem_filter.mp (h k hi)).2
    have hterm : b + (k : ℤ) * 2 = 0 := by omega
    apply hp.ne_one
    simpa [hterm] using hzero

end isLeast_longestAPLength_prime_of_mod_four_eq_one

open isLeast_longestAPLength_prime_of_mod_four_eq_one in
/-- **Minimum longest progression length modulo a prime $p \equiv 1 \pmod 4$.** Let $p$ be a prime
with $p \equiv 1 \pmod 4$. For an integer $m$ let $f_m(p)$ be the length of the longest arithmetic
progression with positive common difference contained in the set $R_m(p)$ of integers $a$ with
$m + 1 \le a \le m + p$ and $\gcd(a, p) = 1$. Then the least value of $f_m(p)$ over all integers
$m$ is $(p - 1) / 2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem isLeast_longestAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m p) ((p - 1) / 2) := by
  let k := p / 4
  have hpk : p = 4 * k + 1 := by dsimp [k]; omega
  rw [show (p - 1) / 2 = 2 * k by omega]
  constructor
  · exact ⟨_, le_antisymm (centered_upper_bound hp hpk) (lower_bound _ hp hpk)⟩
  · rintro _ ⟨m, rfl⟩
    exact lower_bound m hp hpk

end MetaMathlibExt
