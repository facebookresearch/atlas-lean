/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of a set and a transcendental dilate (AIM additive combinatorics, Problem 4.8)

Problems presented at the AIM workshop on recent trends in additive combinatorics (collected by E.
Croot and V. F. Lev), Problem 4.8 (I. Łaba): suppose that `α` is transcendental and `|A| = n`. What
is the best lower bound for `|A + αA|`? Remarks: Konyagin and Łaba have shown that this cardinality
is `≫ n log n / log log n`; the best example (lowest known cardinality) is `n e^{c √(log n)}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.TranscendentalDilateSumsetAIMCombinatoricsProblem264Wanted

open scoped Pointwise

/-!
Source: Problems presented at the workshop on recent trends in additive combinatorics, collected by
E. Croot and V. F. Lev, AIM workshop problem list, Problem 4.8 (I. Łaba),
https://aimath.org/WWN/additivecomb/additivecomb.pdf. UnsolvedMath record UM-20001139
(`AIM-COMBINATORICS-0264`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is a finite set of reals and `α` a real number transcendental over `ℚ`, the setting of the
Konyagin–Łaba bounds and of the resolving theorem. The target is the lower bound `|A + αA| ≥ e^{c
√(log |A|)} |A|` with an absolute constant `c > 0`, which matches the Konyagin–Łaba example `n e^{c
√(log n)}` up to the constant; the matching construction and the optimal constant are not stated.
-/

/-- **Lower bound for sums of transcendental dilates.** There is a real constant $c > 0$ such that
for every real number $\alpha$ transcendental over $\mathbb{Q}$ and every finite set $A$ of real
numbers,
$$e^{c\sqrt{\log |A|}}\,|A| \le |A + \alpha \cdot A|,$$
where $A + \alpha \cdot A = \{a + \alpha b : a, b \in A\}$. -/
def transcendentalDilateLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (α : ℝ), Transcendental ℚ α → ∀ A : Finset ℝ,
    Real.exp (c * Real.sqrt (Real.log A.card)) * A.card ≤ ((A + α • A).card : ℝ)

/-- **Conlon–Lim theorem on sums of transcendental dilates.** There is a real constant $c > 0$
such that for every real number $\alpha$ transcendental over $\mathbb{Q}$ and every finite set $A$
of real numbers,
$$e^{c\sqrt{\log |A|}}\,|A| \le |A + \alpha \cdot A|,$$
where $A + \alpha \cdot A = \{a + \alpha b : a, b \in A\}$.

Resolved true: Conlon and Lim prove that there is an absolute constant `c > 0` such that `|A + λ·A|
≥ e^{c √(log |A|)} |A|` for every finite `A ⊆ ℝ` and every transcendental `λ ∈ ℝ`, best possible up
to the constant `c` by the construction of Konyagin and Łaba.

Source: Problems presented at the
workshop on recent trends in additive combinatorics, collected by E. Croot and V. F. Lev, AIM
workshop problem list, Problem 4.8 (I. Łaba), https://aimath.org/WWN/additivecomb/additivecomb.pdf;
resolution: D. Conlon and J. Lim, Sums of transcendental dilates, Bull. London Math. Soc. 55 (2023)
2400-2406, arXiv:2212.10128, abstract and main theorem, https://arxiv.org/abs/2212.10128.
-/
public theorem_wanted transcendentalDilateLowerBound_holds : transcendentalDilateLowerBound

end MathlibExt.Combinatorics.TranscendentalDilateSumsetAIMCombinatoricsProblem264Wanted
