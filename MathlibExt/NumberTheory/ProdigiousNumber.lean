/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **Product of the nonzero digits.** For natural numbers $b$ and $n$, this is the product of the
nonzero digits of $n$ in base $b$; it equals $1$ when $n = 0$. In the degenerate bases, the digits
of $n > 0$ are the single digit $n$ when $b = 0$, and $n$ copies of $1$ when $b = 1$. -/
public def nonzeroDigitProd (b n : ℕ) : ℕ :=
  ((Nat.digits b n).filter (· != 0)).prod

/-- **Prodigious numbers.** For natural numbers $b$ and $n$, the number $n$ is $b$-prodigious when
$b \ge 2$, $n > 0$, and $n$ is divisible by the product of the nonzero digits of $n$ in base $b$. -/
public def IsProdigious (b n : ℕ) : Prop :=
  2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n

public instance instDecidableIsProdigious (b n : ℕ) :
    Decidable (IsProdigious b n) :=
  inferInstanceAs (Decidable (2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n))

end

end MetaMathlibExt
