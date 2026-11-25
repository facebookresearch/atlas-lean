/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PalindromeAPCountOfDvdBase
import Mathlib.Data.List.GetD

/-!
# Closed forms for palindrome counts

The theorem `palindromeCount_closed_form` gives formulas for the total number of palindromes
up to a bound and, in even bases, for the counts of even and odd palindromes.
-/

namespace MetaMathlibExt

open Finset Int

@[expose] public section

/-- **Counting palindromes up to $m$ and by parity.** Let $b \ge 2$ and $m \ge 1$, and write
$m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$, with leading digit $a_k \ne 0$. For natural numbers
$q$ and $r$, let $A_b(m, q, r)$ be the number of $b$-adic palindromes $n$ with $1 \le n \le m$
and $n \equiv r \pmod q$, and let $C_b(m)$ be the palindromic half copy of $m$. Put $\delta = 1$
if $C_b(m) \le m$ and $\delta = 0$ otherwise. Then
$A_b(m, 1, 0) = b^{\lceil k/2 \rceil} +
\sum_{i=0}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i} + \delta - 2$.
If moreover $b$ is even, let
$\alpha = (b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2)/(b - 1)$ and
$S = \sum_{i=1}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i}$, let $\varepsilon_0 = 1$
if $a_k$ is even and $\varepsilon_0 = 0$ otherwise, and let $\varepsilon_1 = 1 - \varepsilon_0$.
Then $A_b(m, 2, 0) = (b/2 - 1)\alpha + \lfloor (a_k - 1)/2 \rfloor b^{\lfloor k/2 \rfloor} +
\varepsilon_0 (S + \delta)$ and
$A_b(m, 2, 1) = b\alpha/2 + \lceil (a_k - 1)/2 \rceil b^{\lfloor k/2 \rfloor} +
\varepsilon_1 (S + \delta)$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 8. -/
public theorem palindromeCount_closed_form {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
    let S : ℚ := ∑ i ∈ Finset.Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
    let δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
    (palindromeAPCount b m 1 0 : ℚ) =
        (b : ℚ) ^ ((k + 1) / 2) +
          ∑ i ∈ Finset.range (k / 2 + 1), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i) + δ - 2 ∧
      (Even b →
        (palindromeAPCount b m 2 0 : ℚ) =
            ((b : ℚ) / 2 - 1) * α + (((a k - 1) / 2 : ℕ) : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Even (a k) then 1 else 0) * (S + δ) ∧
          (palindromeAPCount b m 2 1 : ℚ) =
            (b : ℚ) * α / 2 + (⌈((a k : ℚ) - 1) / 2⌉ : ℚ) * (b : ℚ) ^ (k / 2) +
              (if Odd (a k) then 1 else 0) * (S + δ)) := by
  dsimp only
  set k := (b.digits m).length - 1
  set a := fun i : ℕ => (b.digits m).getD i 0
  set α : ℚ := ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)
  set S : ℚ := ∑ i ∈ Icc 1 (k / 2), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i)
  set δ : ℚ := if palindromicHalfCopy b m ≤ m then 1 else 0
  constructor
  · have H := (palindromeAPCount_of_dvd_base hb hm (le_refl 1) (one_dvd b)).1
    have hlen : k < (b.digits m).length := by
      have := List.length_pos_iff.mpr ((Nat.digits_ne_nil_iff_ne_zero (b := b)).mpr
        (by omega : m ≠ 0))
      dsimp [k]
      omega
    have ha : 1 ≤ a k := by
      rw [show a k = (b.digits m).getLast (List.ne_nil_of_length_pos (by omega)) by
        rw [List.getLast_eq_getElem, ← List.getD_eq_getElem _ 0 hlen]]
      exact Nat.pos_iff_ne_zero.mpr (Nat.getLast_digit_ne_zero b (by omega))
    have hα : α * ((b : ℚ) - 1) = (b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2 := by
      have hb' : (b : ℚ) ≠ 1 := by exact_mod_cast (show b ≠ 1 by omega)
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr hb')
    have hs : ∑ i ∈ range (k / 2 + 1), (a (k - i) : ℚ) * (b : ℚ) ^ (k / 2 - i) =
        (a k : ℚ) * (b : ℚ) ^ (k / 2) + S := by
      rw [sum_range_succ']
      have hi : Icc 1 (k / 2) = Ico 1 (k / 2 + 1) := by ext i; simp
      dsimp [S]
      rw [hi, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      simp only [add_comm]
    change (palindromeAPCount b m 1 0 : ℚ) =
      ((b : ℚ) / (1 : ℕ) - 1) * α + (((a k - 1) / 1 : ℕ) : ℚ) * (b : ℚ) ^ (k / 2) +
        (if a k ≡ 0 [MOD 1] then 1 else 0) * (S + δ) at H
    simp only [Nat.cast_one, div_one, Nat.div_one, Nat.cast_sub ha, Nat.modEq_one, ite_true,
      one_mul] at H
    rw [H, hs]
    linarith
  · intro hbEven
    have H := palindromeAPCount_of_dvd_base hb hm (q := 2) (by decide) (even_iff_two_dvd.mp hbEven)
    have he (n : ℕ) : (n ≡ 0 [MOD 2]) ↔ Even n := Nat.even_iff.symm
    have ho (n : ℕ) : (n ≡ 1 [MOD 2]) ↔ Odd n := Nat.odd_iff.symm
    refine ⟨?_, ?_⟩
    · simpa only [he, Nat.cast_ofNat] using H.1
    · simpa only [ho, show 1 % 2 = 1 by decide, Nat.cast_one, Nat.cast_ofNat] using
        H.2 1 (by decide)

end

end MetaMathlibExt
