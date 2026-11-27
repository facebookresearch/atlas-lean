/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Initial values of the truncated binomial sums for the k-Fibonacci numbers

Farhi's truncated binomial sum equals a power of two for indices from `2` to `k + 1`.
At index `k + 2` its second term lowers that power by one.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Truncated binomial sum $G_n^{(k)}$.** For an integer $x$ and a natural number $j$ let
$\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. For natural numbers $k$ and $n$, the rational number
$G_n^{(k)}$ is
$$
G_n^{(k)} = 2^{n-2} \sum_{\ell=0}^{m}
\left(\binom{(k+1)\ell - n}{\ell} - \binom{(k+1)\ell - n}{\ell - 1}\right) 2^{-(k+1)\ell},
$$
where $m = \lfloor (n-1)/(k+1) \rfloor$ for $n \ge 1$ and $m = 0$ for $n = 0$, and the term
$\binom{(k+1)\ell - n}{\ell - 1}$ is taken to be $0$ for $\ell = 0$.

The paper defines $G_n^{(k)}$ only for $n, k \ge 2$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, definition
before Proposition 10. -/
public def kFibonacciBinomialTruncation (k n : ℕ) : ℚ :=
  2 ^ ((n : ℤ) - 2) * ∑ ℓ ∈ Finset.range ((n - 1) / (k + 1) + 1),
    ((Ring.choose (((k + 1) * ℓ : ℕ) - (n : ℤ)) ℓ -
      (if ℓ = 0 then 0 else Ring.choose (((k + 1) * ℓ : ℕ) - (n : ℤ)) (ℓ - 1)) : ℤ) : ℚ) /
      2 ^ ((k + 1) * ℓ)

/-- **Value $G_2^{(2)} = 1$.** The truncated binomial sum satisfies $G_2^{(2)} = 1$.

This is the Fibonacci number $F_2$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, definition
before Proposition 10. -/
public theorem kFibonacciBinomialTruncation_two_two : kFibonacciBinomialTruncation 2 2 = 1 := by
  norm_num [kFibonacciBinomialTruncation]

/-- **Value $G_4^{(2)} = 3$.** The truncated binomial sum satisfies $G_4^{(2)} = 3$.

This is the Fibonacci number $F_4$, and $n = 4$ is the first index for which the sum defining
$G_n^{(2)}$ has two terms.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, definition
before Proposition 10. -/
public theorem kFibonacciBinomialTruncation_two_four : kFibonacciBinomialTruncation 2 4 = 3 := by
  norm_num [kFibonacciBinomialTruncation, Finset.sum_range_succ, Ring.choose_one_right]

/-- **Initial values of the truncated binomial sums.** Let $k \ge 2$ be a natural number and let
$G_n^{(k)}$ be the truncated binomial sum. Then $G_n^{(k)} = 2^{n-2}$ for every natural number $n$
with $2 \le n \le k + 1$, and $G_{k+2}^{(k)} = 2^k - 1$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Proposition 10 (`jis-2024-24.1.1-prop-10`). -/
public theorem kFibonacciBinomialTruncation_initial_values (k : ℕ) (hk : 2 ≤ k) :
    (∀ n, 2 ≤ n → n ≤ k + 1 → kFibonacciBinomialTruncation k n = 2 ^ (n - 2)) ∧
      kFibonacciBinomialTruncation k (k + 2) = 2 ^ k - 1 := by
  constructor
  · intro n hn hnk
    have hm : (n - 1) / (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
    have he : (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) := by omega
    simp [kFibonacciBinomialTruncation, hm, he]
  · have hm : (k + 2 - 1) / (k + 1) = 1 := by
      rw [show k + 2 - 1 = k + 1 by omega, Nat.div_self (by omega)]
    norm_num [kFibonacciBinomialTruncation, hm, Finset.sum_range_succ,
      Ring.choose_one_right, pow_succ]
    field_simp
    ring

end

end MetaMathlibExt
