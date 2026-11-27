/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import MathlibExt.Dynamics.NExpansionGaps
public import MathlibExt.Dynamics.NExpansionGapsPointLtIff

/-!
# Intervals of N-expansions with many gaps

Statements from Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026),
Article A75. The N-expansion map and its digit with three basic properties, the alternation in
order of orbits with the same digits, the ideal period words (Definition 7), their first values
and their formulas for digit lengths and block counts are in `MathlibExt.Dynamics.NExpansionGaps`,
which this module imports. The comparison of the ideal periodic points is in
`MathlibExt.Dynamics.NExpansionGapsPointLtIff`, which this module also imports.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The ideal periodic point is the least point of its orbit.** Let $N$ be a natural number,
let $\alpha$ be a real number with $0 < \alpha \le \sqrt N - 1$, and let $T_\alpha$ be the
$N$-expansion map on $I_\alpha = [\alpha, \alpha + 1]$. Let $n \ge 1$, write $|d_n|$ for the
length of the digit string of the ideal period word $d_n$, and let $x \in I_\alpha$ be such that
for every $i \ge 0$ the digit of $T_\alpha^i(x)$ is entry $i \bmod |d_n|$ (counting from $0$) of
that digit string, so that the expansion of $x$ is purely periodic with period word $d_n$. Then
$x \le T_\alpha^j(x)$ for every $j \ge 0$.

The source assumes Phase I; only the assumption $0 < \alpha \le \sqrt N - 1$ is kept here.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 5 (`integers-2026-A75-lem-5`). -/
public theorem_wanted idealPeriodWord_point_le_orbit {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc α (α + 1))
    (hxd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      ((idealPeriodWord n).flatten.getD (i % (idealPeriodWord n).flatten.length) 0 : ℤ))
    (j : ℕ) :
    x ≤ (nExpansionMap N α)^[j] x

end

end MetaMathlibExt
