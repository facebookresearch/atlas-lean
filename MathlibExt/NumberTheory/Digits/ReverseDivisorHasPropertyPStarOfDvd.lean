/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
import MathlibExt.NumberTheory.Digits.ReverseDivisibility

/-!
# Divisors of `99` have property `P*`

Every divisor of `99` has property `P*`: it divides the decimal reversal of each of its
multiples.

Statements from Mohamed Ayad and Rachid Bouchenna, "Which Integer Divides the Reverse of Any
of Its Multiples?", *INTEGERS* 25 (2025), Article A37
(<https://math.colgate.edu/~integers/vol25.html>).
-/

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **Divisors of $99$ have property $P^*$.** Every divisor of $99$ has property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 1. -/
theorem hasPropertyPStar_of_dvd (n : ℕ) (hn : n ∣ 99) :
    HasPropertyPStar n := by
  intro m hm
  exact dvd_reverseDigits_of_dvd 10 n (by decide) (by simpa using hn) m hm

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
