/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Log.GuzmanSanchezLuca

/-! # Concatenations of two repdigits in a general base -/

namespace MetaMathlibExt

@[expose] public section

/-- **Concatenations of two repdigits in a general base.** A natural number $n$ is a
concatenation of two repdigits in base $b$ if there are digits $a_1, a_2$ with
$1 \le a_1 \le b - 1$, $0 \le a_2 \le b - 1$ and $a_1 \ne a_2$, and block lengths $l, m \ge 1$,
such that $(b - 1) n = a_1 (b^l - 1) b^m + a_2 (b^m - 1)$. The digit conditions force
$b \ge 2$, and the equation says that the base-$b$ expansion of $n$ is $l$ copies of $a_1$
followed by $m$ copies of $a_2$.

Because of the condition $a_1 \ne a_2$, a repdigit such as $4 = (11)_3$ is not a concatenation
of two repdigits in base $3$. For $b = 10$ this is the notion of a concatenation of two decimal
repdigits.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Section 1 (Equation (1)). -/
public def IsConcatTwoRepdigitsBase (b n : ℕ) : Prop :=
  ∃ a₁ a₂ l m : ℕ, 1 ≤ a₁ ∧ a₁ < b ∧ a₂ < b ∧ 1 ≤ l ∧ 1 ≤ m ∧ a₁ ≠ a₂ ∧
    (b - 1) * n = a₁ * (b ^ l - 1) * b ^ m + a₂ * (b ^ m - 1)

/-- **Examples of two-repdigit concatenations in bases 2 and 5.** The number $4$ is a
concatenation of two repdigits in base $2$, since $4 = (100)_2$, and the number $406$ is a
concatenation of two repdigits in base $5$, since $406 = (3111)_5$.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Theorem 1. -/
public theorem isConcatTwoRepdigitsBase_examples :
    IsConcatTwoRepdigitsBase 2 4 ∧ IsConcatTwoRepdigitsBase 5 406 :=
  ⟨⟨1, 0, 1, 2, by norm_num⟩, ⟨3, 1, 1, 3, by norm_num⟩⟩

end

end MetaMathlibExt
