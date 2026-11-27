/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
import MathlibExt.NumberTheory.Digits.ReverseDivisorHasPropertyPStarIffDvd
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Palindromes with property $P^*$

A positive decimal palindrome with property $P^*$ is one of $1$, $3$, $9$, $11$, $33$, and $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which Integer Divides the Reverse of Any of Its
Multiples?", *INTEGERS* 25 (2025), Article A37, Proposition 3
(<https://math.colgate.edu/~integers/vol25.html>).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **Palindromes with property $P^*$.** Let $n \ge 1$ be a natural number that is a decimal
palindrome, that is, whose decimal reversal equals $n$. If $n$ has the property $P^*$, then $n$
is one of $1$, $3$, $9$, $11$, $33$ and $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 3. -/
theorem palindrome_hasPropertyPStar (n : ℕ) (hn : 1 ≤ n)
    (hpal : Nat.reverseDigits 10 n = n) (h : HasPropertyPStar n) :
    n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 11 ∨ n = 33 ∨ n = 99 := by
  have hdvd := (hasPropertyPStar_iff_dvd n hn).mp h
  have hle : n ≤ 99 := Nat.le_of_dvd (by decide) hdvd
  interval_cases n <;> norm_num at hdvd
  all_goals norm_num

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
