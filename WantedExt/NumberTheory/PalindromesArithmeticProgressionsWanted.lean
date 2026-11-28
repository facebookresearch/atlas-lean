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
public import MathlibExt.NumberTheory.PalindromeAPCountBaseMinusOne
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

end

end MetaMathlibExt
