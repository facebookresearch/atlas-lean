/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GenocchiNumber
public import Mathlib.Combinatorics.Enumerative.Stirling
import MathlibExt.Combinatorics.Enumerative.GarabedianBernoulliStirling
import MathlibExt.NumberTheory.GenocchiBernoulli

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

section

/-- **Garabedian's formula for the Genocchi numbers, including $n = 0$.** For every natural
number $n$, the Genocchi number $G_n$, defined by $\sum_{m \ge 0} G_m x^m / m! = 2x/(e^x + 1)$,
satisfies

$$G_n = n \sum_{k=1}^{n} \frac{(-1)^{n-k} (k-1)!\, S(n, k)}{2^{k-1}},$$

where $S(n, k)$ is the Stirling number of the second kind. At $n = 0$ both sides are $0$. -/
theorem genocchiNumber_eq_stirlingSecond_sum_general (n : ℕ) :
    genocchiNumber n =
      (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
          (2 : ℚ) ^ (k - 1) :=
  (genocchiNumber_eq_bernoulli n).trans (garabedian_genocchi_formula_general n)

set_option linter.unusedVariables false in
/-- **Garabedian's formula for the Genocchi numbers.** For every natural number $n \ge 1$, the
Genocchi number $G_n$, defined by $\sum_{m \ge 0} G_m x^m / m! = 2x/(e^x + 1)$, satisfies

$$G_n = n \sum_{k=1}^{n} \frac{(-1)^{n-k} (k-1)!\, S(n, k)}{2^{k-1}},$$

where $S(n, k)$ is the Stirling number of the second kind.

The identity also holds for $n = 0$, where both sides are $0$.

The formula is due to H. L. Garabedian, "A new formula for the Bernoulli numbers," Bulletin of
the American Mathematical Society 46 (1940), 531–533, DOI 10.1090/S0002-9904-1940-07255-6.

Proves `Wanted` entry `genocchiNumber_eq_stirlingSecond_sum`.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas
for Bernoulli and Genocchi Numbers," Journal of Integer Sequences 28 (2025),
Article 25.6.7, lines 184–194 of the official TeX:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Zerroukhat/zerrou3.tex>.
-/
@[nolint unusedArguments]
theorem genocchiNumber_eq_stirlingSecond_sum (n : ℕ)
    (hn : 1 ≤ n) :
    genocchiNumber n =
      (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
          (2 : ℚ) ^ (k - 1) :=
  genocchiNumber_eq_stirlingSecond_sum_general n

end

end MetaMathlibExt
