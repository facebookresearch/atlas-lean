/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
Witt's multigraded dimension formula for free Lie algebras.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Witt's multigraded value.** For natural numbers $n_1, \dots, n_r$, let
$n = n_1 + \dots + n_r$ and $g = \gcd(n_1, \dots, n_r)$. The rational number
$M(n_1, \dots, n_r)$ is $0$ if $n = 0$, and otherwise
$M(n_1, \dots, n_r) = \frac{1}{n} \sum_{d \mid g} \mu(d) \binom{n/d}{n_1/d, \ldots, n_r/d}$,
where the sum runs over the positive divisors $d$ of $g$, $\mu$ is the Möbius function, and the
last factor is the multinomial coefficient of $n_1/d, \dots, n_r/d$.

Source: Pieter Moree, *Convoluted Convolved Fibonacci Numbers*, Journal of
Integer Sequences 7 (2004), Article 04.2.2, equations `witty`/`basaal`,
lines 598–613 (Möbius inversion of the circular-word count; context
*Circular words and Witt's dimension formula*, lines 574–597),
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Moree/moree12.tex>. -/
def wittMultigradedValue {r : ℕ} (degree : Fin r → ℕ) : ℚ :=
  let n := Finset.sum Finset.univ degree
  let g := Finset.univ.gcd degree
  if n = 0 then 0
  else (1 / (n : ℚ)) * Finset.sum (Nat.divisors g) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
      (Nat.multinomial Finset.univ (fun i => degree i / d) : ℚ))

end

end MetaMathlibExt
