/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas
public import MathlibExt.NumberTheory.DigitSumCongruenceCount
public import MathlibExt.NumberTheory.FloorIdentities
public import MathlibExt.NumberTheory.PalindromeAPCountBasePow
public import MathlibExt.NumberTheory.PalindromeAPCountOfDvdBase
public import MathlibExt.NumberTheory.PalindromeCountClosedForm
public import MathlibExt.NumberTheory.PalindromesArithmeticProgressions

/-!
# Palindromes in arithmetic progressions (statements)

Statement-only targets from Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon
Napp Phunphayap and Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in
Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8 (TeX
source read).

Conventions. For `m ≥ 1` with base-`b` expansion `m = (a_k ⋯ a_0)_b`, the digit `a_i` is
`(Nat.digits b m).getD i 0` (Mathlib's little-endian digit list) and `k` is
`(Nat.digits b m).length - 1`. A positive `n` is a `b`-adic palindrome when
`(Nat.digits b n).Palindrome`. `A_b(m, q, r)` is `palindromeAPCount b m q r` and
`A_b(m) = A_b(m, 1, 0)`; `C_b(m)` is `palindromicHalfCopy b m`; `N_b(k, q, r, x, y)` is
`digitSumCongruenceCount b k q r x y`. Iverson brackets `[P]` are written `if P then 1 else 0`.
-/

namespace MetaMathlibExt

open Int

@[expose] public section

/-- **Two small palindrome counts.** Write $A_b(m, q, r)$ for the number of base-$b$ palindromes
$n$ with $1 \le n \le m$ and $n \equiv r \pmod q$. Then $A_{10}(100, 1, 0) = 18$, the palindromes
being $1, \dots, 9$ and $11, 22, \dots, 99$, and $A_2(9, 2, 1) = 5$, the odd base-$2$ palindromes
up to $9$ being $1$, $3 = (11)_2$, $5 = (101)_2$, $7 = (111)_2$ and $9 = (1001)_2$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Section 1. -/
public theorem palindromeAPCount_small :
    palindromeAPCount 10 100 1 0 = 18 ∧ palindromeAPCount 2 9 2 1 = 5 := by
  decide +kernel

/-- **Palindromic half copies of $5570$ in bases $5$ and $8$.** Write $C_b(m)$ for the
palindromic half copy of $m$ in base $b$. For $m = 5570 = (134240)_5 = (12702)_8$,
$C_5(m) = (134431)_5 = 5616$ and $C_8(m) = (12721)_8 = 5585$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 1 (example). -/
public theorem palindromicHalfCopy_example :
    palindromicHalfCopy 5 5570 = 5616 ∧ palindromicHalfCopy 8 5570 = 5585 := by
  decide +kernel

/-- **A small value of the digit-sum congruence count.** In the notation $N_b(k, q, r, x, y)$
of the digit-sum congruence count, $N_3(2, 2, 0, 0, 3) = 5$: exactly five pairs $(x_1, x_2)$ of
natural numbers with $x_1, x_2 < 3$ have even sum.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 3. -/
public theorem digitSumCongruenceCount_small : digitSumCongruenceCount 3 2 2 0 0 3 = 5 := by
  decide +kernel

/-- **Palindromes in residue classes modulo a divisor of the base minus one.** Let $b \ge 2$,
$m \ge 1$ and $q \ge 1$ be natural numbers with $b \equiv 1 \pmod q$, and let $r$ be a natural
number with $r < q$. Write $m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$. Write $A_b(m, q, r)$ for
the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r \pmod q$, $C_b(m)$
for the palindromic half copy of $m$, $[P]$ for $1$ if $P$ holds and $0$ otherwise, and
$t \bmod d$ for the least nonnegative residue of an integer $t$ modulo a positive integer $d$.
For $j \ge 0$ define integers $s_j$ and $r_j$ as follows. If $q$ is even and $2j \ne k$, let
$s_j = a_{k-j} \bmod (q/2)$ and
$r_j = \bigl(\lfloor r/2 \rfloor - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod (q/2)$. If $q$ is odd
and $2j \ne k$, let $s_j = a_{k-j} \bmod q$ and
$r_j = \bigl(\frac{q+1}{2} r - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod q$. If $2j = k$, let
$s_j = a_{k-j} \bmod q$ and $r_j = \bigl(r - 2 \sum_{i=0}^{k/2-1} a_{k-i}\bigr) \bmod q$. Put
$\delta = [C_b(m) \le m] \, [r_{\lfloor k/2 \rfloor} = s_{\lfloor k/2 \rfloor}]$ and

$$m_1^* = \sum_{j=0}^{\lfloor (k-1)/2 \rfloor}
\left( \frac{2 a_{k-j} b^{\lfloor (k-1)/2 \rfloor - j} - 2 s_j}{q} + [r_j < s_j] \right),$$

$$m_2^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\frac{a_{k-j} (b - 1) b^{\lfloor k/2 \rfloor - j - 1}}{q},$$

$$m_3^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\left( \frac{a_{k-j} (b + 1) b^{\lfloor k/2 \rfloor - j - 1} - 2 s_j}{q} + [r_j < s_j] \right).$$

Then, as rational numbers, if $q$ is odd,

$$A_b(m, q, r) = \frac{b^{\lfloor (k+1)/2 \rfloor} - 1}{q} +
\sum_{j=0}^{\lfloor k/2 \rfloor} \left( \left\lfloor \frac{a_{k-j} b^{\lfloor k/2 \rfloor - j}}{q}
\right\rfloor + [r_j < s_j] \right) - [r = 0] + \delta,$$

and if $q$ is even, $A_b(m, q, r)$ equals $(b - 1) b^{(k-1)/2}/q$ when $k$ and $r$ are odd,
$((b + 1) b^{(k-1)/2} - 2)/q + m_1^* - [r = 0] + \delta$ when $k$ is odd and $r$ is even,
$\lfloor a_{k/2}/q \rfloor + m_2^* + [r_{k/2} < s_{k/2}] + \delta$ when $k$ is even and $r$ is
odd, and $2(b^{k/2} - 1)/q + \lfloor a_{k/2}/q \rfloor + m_3^* - [r = 0] +
[r_{k/2} < s_{k/2}] + \delta$ when $k$ and $r$ are both even.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Theorem 9. -/
public theorem_wanted palindromeAPCount_of_modEq_one {b m q r : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hr : r < q) (hbq : b ≡ 1 [MOD q]) :
    let a : ℕ → ℕ := fun i => (Nat.digits b m).getD i 0
    let k : ℕ := (Nat.digits b m).length - 1
    let rr : ℕ → ℤ := fun j =>
      if 2 * j = k then ((r : ℤ) - 2 * ∑ i ∈ Finset.range (k / 2), (a (k - i) : ℤ)) % q
      else if Even q then (((r / 2 : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % (q / 2 : ℕ)
      else ((((q + 1) / 2 * r : ℕ) : ℤ) - ∑ i ∈ Finset.range j, (a (k - i) : ℤ)) % q
    let ss : ℕ → ℤ := fun j =>
      if Even q ∧ 2 * j ≠ k then ((a (k - j) % (q / 2) : ℕ) : ℤ) else ((a (k - j) % q : ℕ) : ℤ)
    let δ : ℚ :=
      (if palindromicHalfCopy b m ≤ m then 1 else 0) * (if rr (k / 2) = ss (k / 2) then 1 else 0)
    let m₁ : ℚ := ∑ j ∈ Finset.range ((k - 1) / 2 + 1),
      ((2 * (a (k - j) : ℚ) * (b : ℚ) ^ ((k - 1) / 2 - j) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    let m₂ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (a (k - j) : ℚ) * ((b : ℚ) - 1) * (b : ℚ) ^ (k / 2 - j - 1) / q
    let m₃ : ℚ := ∑ j ∈ Finset.range (k / 2),
      (((a (k - j) : ℚ) * ((b : ℚ) + 1) * (b : ℚ) ^ (k / 2 - j - 1) - 2 * (ss j : ℚ)) / q +
        (if rr j < ss j then 1 else 0))
    (Odd q →
      (palindromeAPCount b m q r : ℚ) =
        ((b : ℚ) ^ ((k + 1) / 2) - 1) / q +
          ∑ j ∈ Finset.range (k / 2 + 1),
            ((((a (k - j) * b ^ (k / 2 - j)) / q : ℕ) : ℚ) + (if rr j < ss j then 1 else 0)) -
          (if r = 0 then 1 else 0) + δ) ∧
    (Even q →
      (palindromeAPCount b m q r : ℚ) =
        if Odd k ∧ Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
        else if Odd k then
          (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) - 2) / q + m₁ - (if r = 0 then 1 else 0) + δ
        else if Odd r then
          ((a (k / 2) / q : ℕ) : ℚ) + m₂ + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ
        else
          2 * ((b : ℚ) ^ (k / 2) - 1) / q + ((a (k / 2) / q : ℕ) : ℚ) + m₃ -
            (if r = 0 then 1 else 0) + (if rr (k / 2) < ss (k / 2) then 1 else 0) + δ)

end

end MetaMathlibExt
