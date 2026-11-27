/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Fine numbers.** For a natural number $n$, the Fine number $F(n)$, indexed from $0$ so
that $F(0) = 1$, is the rational number
$$F(n) = \frac{1}{n+1} \sum_{i=0}^{n} (-2)^i \, (i+1) \binom{2(n+1)}{n-i}.$$

Source: Fine numbers (OEIS A000957), zero-based: `fineNumber n` is source `𝔽_(n+1)`.
Source explicit formula `𝔽_n = (1/n) * ∑_{i=1}^n (-2)^(i-1) * i * C(2n, n-i)`
with `𝔽_1 = 1`, from JIS VOL21/Janjic3/janjic96.tex lines 105-108 and 157-158.
Phrase concept `jis_term_dfac4b97dfaf92729d46eb23`; source statement
`jis_5d8bd849271ecf8ace5bbc6f`; source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL21/Janjic3/janjic96.tex`. -/
public def fineNumber (n : Nat) : ℚ :=
  (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
    (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ)

/-- **Explicit formula for the Fine numbers.** For every natural number $n$, the Fine number
$F(n)$, indexed from $0$ so that $F(0) = 1$, satisfies
$$F(n) = \frac{1}{n+1} \sum_{i=0}^{n} (-2)^i \, (i+1) \binom{2(n+1)}{n-i}.$$

The source indexes from $1$: writing $\mathbb{F}_m = F(m - 1)$ for $m \ge 1$, it states
$\mathbb{F}_m = \frac{1}{m} \sum_{i=1}^{m} (-2)^{i-1} \, i \binom{2m}{m-i}$, which becomes the
formula above on setting $m = n + 1$ and shifting the summation index down by one. -/
public theorem fineNumber_eq_sum (n : Nat) :
    fineNumber n = (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ) :=
  rfl

end

end MetaMathlibExt
