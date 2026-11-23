/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic pairwise sums of an ℵ₁-sized set of reals (Erdős Problem 965)

Erdős Problem 965: is it true that, for any `2`-colouring of `ℝ`, there is a set `A ⊆ ℝ` of
cardinality `ℵ₁` such that all sums `a + b` with `a ≠ b` and `a, b ∈ A` are the same colour?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticPairSumsRealsErdosProblem965Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #965, https://www.erdosproblems.com/965 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007102 (`EP-965`), dataset ulamai/UnsolvedMath v1.8.0.

A `2`-colouring is a function `ℝ → Fin 2` and `|A| = ℵ₁` is `Cardinal.mk A = Cardinal.aleph 1`. The
refutation is a ZFC theorem (no continuum hypothesis). Compared with the formal-conjectures
statement `ErdosProblems/965.lean` (which asks for an uncountable `A`; its refutation implies this
one; no code imported).
-/

/-- **Erdős Problem 965.** The statement that for every colouring of the real numbers with two
colours there is a set $A \subseteq \mathbb{R}$ of cardinality $\aleph_1$ such that all sums
$a + b$ with $a, b \in A$ and $a \ne b$ have the same colour. -/
def alephOneMonochromaticPairSums : Prop :=
  ∀ c : ℝ → Fin 2, ∃ A : Set ℝ, Cardinal.mk A = Cardinal.aleph 1 ∧ ∃ i : Fin 2,
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → c (a + b) = i

/--
**Erdős Problem 965 is false.** It is not the case that for every colouring of the real
numbers with two colours there is a set $A \subseteq \mathbb{R}$ of cardinality $\aleph_1$ such
that all sums $a + b$ with $a, b \in A$ and $a \ne b$ have the same colour.

Komjáth, and independently Soukup and Weiss, constructed in ZFC a $2$-colouring of $\mathbb{R}$
such that for every uncountable $A \subseteq \mathbb{R}$, in particular every $A$ of cardinality
$\aleph_1$, the sums $a + b$ of distinct $a, b \in A$ take both colours.

Source: T. F. Bloom, Erdős Problems, Problem #965, https://www.erdosproblems.com/965
(status DISPROVED (LEAN)); resolution: P. Komjáth, A certain 2-coloring of the reals, Real Anal.
Exchange (2016), 227-231, erdosproblems.com/965: Komjáth, and independently Soukup and Weiss, proved
without the continuum hypothesis that some 2-colouring of ℝ makes the sums of k distinct elements of
any uncountable A ⊆ ℝ non-monochromatic, for every k ≥ 1 (the case k = 2 disproves the question),
https://www.erdosproblems.com/965.
-/
public theorem_wanted alephOneMonochromaticPairSums_refuted : ¬ alephOneMonochromaticPairSums

end MathlibExt.Combinatorics.MonochromaticPairSumsRealsErdosProblem965Wanted
