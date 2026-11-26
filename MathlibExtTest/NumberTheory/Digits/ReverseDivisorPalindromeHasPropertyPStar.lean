/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ReverseDivisorPalindromeHasPropertyPStar

/-!
# Tests for palindromes with property $P^*$

The classification excludes $121$ and implies that every positive decimal palindrome with
property $P^*$ divides $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which Integer Divides the Reverse of Any of Its
Multiples?", *INTEGERS* 25 (2025), Article A37, Proposition 3
(<https://math.colgate.edu/~integers/vol25.html>).
-/

namespace MathlibExtTest.NumberTheory.Digits.ReverseDivisorPalindromeHasPropertyPStar

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

example : ¬ HasPropertyPStar 121 := by
  intro h
  have hc := palindrome_hasPropertyPStar 121 (by decide) (by decide) h
  omega

example (n : ℕ) (hn : 1 ≤ n) (hpal : Nat.reverseDigits 10 n = n)
    (h : HasPropertyPStar n) : n ∣ 99 := by
  rcases palindrome_hasPropertyPStar n hn hpal h with h | h | h | h | h | h <;>
    subst n <;> decide

end MathlibExtTest.NumberTheory.Digits.ReverseDivisorPalindromeHasPropertyPStar
