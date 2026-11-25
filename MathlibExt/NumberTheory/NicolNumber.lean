/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Nicol numbers.** A Nicol number is a positive integer $n$ that divides
$\varphi(n) + \sigma(n)$, where $\varphi$ is Euler's totient function and $\sigma(n)$ is the sum
of the positive divisors of $n$.

Source: concept `jis_term_45b9093105e27ac81a42edd6`; JIS VOL14/Tang,
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Tang2/tang72.tex>, lines 77–90,
SHA-256 `c3e4694f79de76d0563faff13e7ebd325202b73fa5e8fc02045f0fc7b6d3ce0c`. -/
def IsNicolNumber (n : ℕ) : Prop :=
  0 < n ∧ n ∣ Nat.totient n + ∑ d ∈ n.divisors, d

/-- **$t$-Nicol numbers.** For a natural number $t$, a $t$-Nicol number is a positive integer $n$
such that $\varphi(n) + \sigma(n) = t n$, where $\varphi$ is Euler's totient function and
$\sigma(n)$ is the sum of the positive divisors of $n$. -/
def IsTNicolNumber (t n : ℕ) : Prop :=
  0 < n ∧ Nat.totient n + ∑ d ∈ n.divisors, d = t * n

/-- **Every $t$-Nicol number is a Nicol number.** For all natural numbers $t$ and $n$, if $n$ is a
$t$-Nicol number, then $n$ is a Nicol number. -/
theorem IsTNicolNumber.isNicolNumber {t n : ℕ} (h : IsTNicolNumber t n) :
    IsNicolNumber n := by
  refine ⟨h.1, ⟨t, ?_⟩⟩
  simpa [Nat.mul_comm] using h.2

end

end MetaMathlibExt
