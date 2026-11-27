/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Brown's theorem on minimal palindromic base one less than the number

This module defines the minimum palindromic base `MetaMathlibExt.minPalindromicBase` and proves
Brown's theorem `MetaMathlibExt.minPalindromicBase_eq_pred`: if the smallest base `b ≥ 2` in
which `N ≥ 1` is a palindrome equals `N - 1`, then `N ∈ {3, 4, 6}` or `N > 6` is prime.

Statements from D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69
(arXiv:2401.07351).

The base-`b` representation `(c_k, …, c_0)_b` of `N` (leading digit nonzero) is
Mathlib's little-endian `Nat.digits b N = [c_0, …, c_k]`; `N` is a palindrome in
base `b` when this list is a `List.Palindrome`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Minimum palindromic base.** For a natural number $N$, $b(N)$ is the smallest base $b \ge 2$
in which $N$ is a palindrome, that is, in which the base-$b$ digits of $N$ read the same forwards
and backwards. Such a base exists: $0$ has no digits and is a palindrome in every base, and for
$N \ge 1$ the number $N$ is written with the single digit $N$ in base $N + 1$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1. -/
public noncomputable def minPalindromicBase (N : ℕ) : ℕ :=
  sInf {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome}

private theorem digits_two_mul_succ (b a : ℕ) (hb : 2 ≤ b) (ha0 : a ≠ 0)
    (hab : a < b) : Nat.digits b (a * (b + 1)) = [a, a] := by
  have h : Nat.ofDigits b [a, a] = a * (b + 1) := by
    simp [Nat.ofDigits_cons, Nat.mul_add]
    ring
  rw [← h]
  exact Nat.digits_ofDigits b (by omega) [a, a] (by simp [hab]) (by simp [ha0])

private theorem digits_sq_succ (b : ℕ) (hb : 2 < b) :
    Nat.digits b ((b + 1) ^ 2) = [1, 2, 1] := by
  have h : Nat.ofDigits b [1, 2, 1] = (b + 1) ^ 2 := by
    simp [Nat.ofDigits_cons]
    ring
  rw [← h]
  exact Nat.digits_ofDigits b (by omega) [1, 2, 1] (by simp; omega) (by simp)

private theorem palSet_nonempty (N : ℕ) (hN : 1 ≤ N) :
    {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome}.Nonempty := by
  refine ⟨N + 1, by omega, ?_⟩
  rw [Nat.digits_of_lt (N + 1) N (by omega) (by omega)]
  exact List.Palindrome.singleton N

private theorem false_of_mem_lt_pred (N b : ℕ) (h : minPalindromicBase N = N - 1)
    (hmem : b ∈ {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome}) (hlt : b < N - 1) :
    False := by
  have hle : sInf {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome} ≤ b := Nat.sInf_le hmem
  unfold minPalindromicBase at h
  omega

/-- **Brown's theorem on minimal palindromic base one less than the number.** Let $N \ge 1$ be a
natural number and let $b(N)$ be the smallest base $b \ge 2$ in which $N$ is a palindrome. If
$b(N) = N - 1$, then $N \in \{3, 4, 6\}$, or $N > 6$ and $N$ is prime.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 1
(`integers-2024-A69-thm-1`), credited to K. Brown. -/
public theorem minPalindromicBase_eq_pred (N : ℕ) (hN : 1 ≤ N)
    (h : minPalindromicBase N = N - 1) : N = 3 ∨ N = 4 ∨ N = 6 ∨ (6 < N ∧ N.Prime) := by
  have hne : {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome}.Nonempty := palSet_nonempty N hN
  have hmem : N - 1 ∈ {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome} := by
    rw [← h]
    exact Nat.sInf_mem hne
  have h3 : 3 ≤ N := by
    have hb := hmem.1
    omega
  by_cases h6 : N ≤ 6
  · have hdisj : N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 := by omega
    rcases hdisj with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hmem2 : 2 ∈ {b | 2 ≤ b ∧ (Nat.digits b 5).Palindrome} := by
        refine ⟨by norm_num, ?_⟩
        rw [show Nat.digits 2 5 = [1, 0, 1] by norm_num]
        exact List.Palindrome.of_reverse_eq rfl
      have hlt : (2 : ℕ) < 5 - 1 := by norm_num
      exact false_of_mem_lt_pred 5 2 h hmem2 hlt
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have h6lt : 6 < N := by omega
    by_cases hprime : N.Prime
    · exact Or.inr (Or.inr (Or.inr ⟨h6lt, hprime⟩))
    · exfalso
      set p := N.minFac
      set q := N / p
      have hN1 : N ≠ 1 := by omega
      have hp_prime : p.Prime := Nat.minFac_prime hN1
      have hp_dvd : p ∣ N := Nat.minFac_dvd N
      have hp2 : 2 ≤ p := hp_prime.two_le
      have hN0 : 0 < N := by omega
      have hple : p ≤ q := Nat.minFac_le_div hN0 hprime
      have hdiv : q * p = N := Nat.div_mul_cancel hp_dvd
      have hN_eq : N = p * q := by
        rw [← hdiv]
        exact mul_comm q p
      by_cases hq : p + 1 < q
      · have hb2 : 2 ≤ q - 1 := by omega
        have hplt : p < q - 1 := by omega
        have hp0 : p ≠ 0 := by omega
        have hq1 : p * q = p * ((q - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
        have hdigits : Nat.digits (q - 1) N = [p, p] := by
          rw [hN_eq, hq1]
          exact digits_two_mul_succ (q - 1) p hb2 hp0 hplt
        have hmem2 : q - 1 ∈ {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome} := by
          refine ⟨hb2, ?_⟩
          rw [hdigits]
          exact List.Palindrome.of_reverse_eq rfl
        have hlt : q - 1 < N - 1 := by
          have hq0 : 0 < q := by omega
          have hp1 : 1 < p := by omega
          have hlt2 : q < p * q := by
            have hmul := (Nat.mul_lt_mul_right hq0).mpr hp1
            simpa using hmul
          omega
        exact false_of_mem_lt_pred N (q - 1) h hmem2 hlt
      · have hqq : q = p ∨ q = p + 1 := by omega
        rcases hqq with hqp | hqp1
        · have hNsq : N = p * p := by
            rw [hN_eq, hqp]
          have hp345 : p = 2 ∨ p = 3 ∨ 3 < p := by omega
          rcases hp345 with hp2eq | hp3eq | hp3
          · exfalso
            rw [hp2eq] at hNsq
            norm_num at hNsq
            omega
          · exfalso
            have hN9 : N = 9 := by
              rw [hp3eq] at hNsq
              norm_num at hNsq
              exact hNsq
            have hmem2 : 2 ∈ {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome} := by
              refine ⟨by norm_num, ?_⟩
              have hdig : Nat.digits 2 N = [1, 0, 0, 1] := by
                rw [hN9]
                norm_num
              rw [hdig]
              exact List.Palindrome.of_reverse_eq rfl
            have hlt : (2 : ℕ) < N - 1 := by omega
            exact false_of_mem_lt_pred N 2 h hmem2 hlt
          · exfalso
            have hb2 : 2 < p - 1 := by omega
            have hpp : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : 1 ≤ p)
            have hNeq : N = (p - 1 + 1) ^ 2 := by
              rw [hpp, hNsq]
              ring
            have hdigits : Nat.digits (p - 1) N = [1, 2, 1] := by
              rw [hNeq]
              exact digits_sq_succ (p - 1) hb2
            have hmem3 : p - 1 ∈ {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome} := by
              refine ⟨by omega, ?_⟩
              rw [hdigits]
              exact List.Palindrome.of_reverse_eq rfl
            have hlt : p - 1 < N - 1 := by
              have hp0 : 0 < p := by omega
              have hp1 : 1 < p := by omega
              have hlt2 : p < p * p := by
                have hmul := (Nat.mul_lt_mul_right hp0).mpr hp1
                simpa using hmul
              omega
            exact false_of_mem_lt_pred N (p - 1) h hmem3 hlt
        · exfalso
          have hNp : N = p * (p + 1) := by
            rw [hN_eq, hqp1]
          by_cases hp2eq : p = 2
          · rw [hp2eq] at hNp
            norm_num at hNp
            omega
          · have hodd : Odd p := hp_prime.odd_of_ne_two hp2eq
            obtain ⟨k, hk⟩ := hodd
            have hpdvd : p + 1 ∣ N := by
              rw [hNp]
              exact ⟨p, by ring⟩
            have h2dvd : 2 ∣ p + 1 := by omega
            have hdvd2 : 2 ∣ N := dvd_trans h2dvd hpdvd
            have hle2 : p ≤ 2 := Nat.minFac_le_of_dvd (by norm_num : (2 : ℕ) ≤ 2) hdvd2
            omega

end

end MetaMathlibExt
