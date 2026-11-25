/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Quadrinomial coefficients

This file formalizes the binomial sum from Remark 3.3 of Zhang,
*Realizability of Some Combinatorial Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex>.
-/

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-- **Zhang's six-parameter binomial sum.** For natural numbers $n$, $r_1$, $r_2$, $s$, $t$, $u$,
Zhang's binomial sum is
$$
V(n, r_1, r_2, s, t, u) = \sum_{k=0}^{n} \binom{n}{k}^{r_1} \binom{n}{2k}^{r_2}
\binom{n+k}{k}^{s} \binom{2k}{k}^{t} \binom{2(n-k)}{n-k}^{u}.
$$

The source uses the convention $0^0 = 1$, which is also Lean's convention for natural-number
powers. -/
def zhangVSum (n r₁ r₂ s t u : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    n.choose k ^ r₁ * n.choose (2 * k) ^ r₂ *
      ((n + k).choose k ^ s * ((2 * k).choose k ^ t * (2 * (n - k)).choose (n - k) ^ u))

/-- **Quadrinomial sequence A005725.** For a natural number $n$, the quadrinomial number is
$Q(n) = \sum_{k=0}^{n} \binom{n}{k} \binom{n}{2k}$. This is OEIS sequence A005725. -/
def quadrinomialCoeff (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * n.choose (2 * k)

/-- **Quadrinomial numbers as a specialization of Zhang's V-sum.** For every natural number $n$,
the quadrinomial number $Q(n) = \sum_{k=0}^{n} \binom{n}{k} \binom{n}{2k}$ equals Zhang's
six-parameter binomial sum $V(n, 1, 1, 0, 0, 0)$. -/
theorem quadrinomialCoeff_eq_zhangVSum (n : ℕ) :
    quadrinomialCoeff n = zhangVSum n 1 1 0 0 0 := by
  simp [quadrinomialCoeff, zhangVSum]

end MetaMathlibExt
