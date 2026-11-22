/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Type-1 b-nomial coefficients

For a base `b ≥ 2`, the type-1 `b`-nomial coefficients are the coefficients of
`(1 + X + ⋯ + X ^ (b - 1)) ^ n`. The coefficient is defined to be zero at negative
integer indices.

Source: Ji Young Choi, *Digit Sums Generalizing Binomial Coefficients*,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Choi/choi15.tex>.

JIS concept: `jis_sem_aa36cef0f9c151f781c75a07`.
-/

open scoped BigOperators
open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Base polynomial of the $b$-nomial coefficients.** For a natural number $b \ge 2$, this is
the integer polynomial $1 + X + \dots + X^{b-1} = \sum_{i=0}^{b-1} X^i \in \mathbb{Z}[X]$. -/
noncomputable def bNomialBase (b : ℕ) (_hb : 2 ≤ b) : Polynomial ℤ :=
  ∑ i ∈ Finset.range b, X ^ i

/-- **Type-1 $b$-nomial coefficients.** For natural numbers $b \ge 2$ and $n$ and an integer
$k$, the type-1 $b$-nomial coefficient in row $n$ and column $k$ is the coefficient of $X^k$ in
$(1 + X + \dots + X^{b-1})^n \in \mathbb{Z}[X]$ when $k \ge 0$, and $0$ when $k < 0$. -/
noncomputable def bNomialCoefficient (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (k : ℤ) : ℤ :=
  if k < 0 then 0 else ((bNomialBase b hb) ^ n).coeff k.toNat

end

end MetaMathlibExt
