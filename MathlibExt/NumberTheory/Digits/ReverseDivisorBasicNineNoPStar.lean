/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisorHasPropertyPStarIffDvd

/-!
# Basic quotient-nine reverse divisors lack property $P^*$

## References

* Mohamed Ayad and Rachid Bouchenna, *Which Integer Divides the Reverse of Any of Its Multiples?*,
  INTEGERS 25 (2025), Article A37, pp. 1–10, Lemma 2 and Theorem 3. Here Lemma 2 follows from
  Theorem 3 rather than from an explicit multiple whose reversal is not divisible.
* R. Webster and G. Williams, *On the trail of reverse divisors: 1089 and all that follow*,
  Mathematical Spectrum 45 (2012/2013), pp. 96–102. Ayad and Bouchenna credit them for the
  classification in Theorem 1, which identifies the basic quotient-nine family.
-/

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **For $k \ge 2$, the number $11 \cdot (10^k - 1)$ lacks property $P^*$.** For every natural
number $k \ge 2$, the number $11 \cdot (10^k - 1)$ does not have the property $P^*$.

In the source these numbers $1089, 10989, 109989, \dots$ are the basic reverse divisors with
quotient $9$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 2. -/
theorem not_hasPropertyPStar_basic_nine (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasPropertyPStar (11 * (10 ^ k - 1)) := by
  intro hP
  have hpow : (100 : ℕ) ≤ 10 ^ k := Nat.pow_le_pow_right (by decide : 0 < 10) hk
  have hlarge : 99 < 11 * (10 ^ k - 1) := by omega
  have hdvd := (hasPropertyPStar_iff_dvd (11 * (10 ^ k - 1)) (by omega)).mp hP
  exact (not_le_of_gt hlarge) (Nat.le_of_dvd (by decide) hdvd)

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
