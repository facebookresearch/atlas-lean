/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Concentration of subset sums (Erdős Problem 362)

Erdős Problem 362: for a finite set `A ⊆ ℕ` of size `N` and fixed `t`, are there `≪ 2^N / N^{3/2}`
sets `S ⊆ A` with `∑_{n ∈ S} n = t`? If also `|S| = l` is fixed, is the number `≪ 2^N / N^2`,
uniformly in `l` and `t`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.SubsetSumConcentrationErdosProblem362Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #362, https://www.erdosproblems.com/362 (status PROVED
(LEAN)). UnsolvedMath record UM-30006838 (`EP-362`), dataset ulamai/UnsolvedMath v1.8.0.

The implied constants are absolute (uniform in `A`, `t` and `l`); `A` is nonempty so that the powers
of `N` are positive. `A` may contain `0`, which at most doubles the counts. Each question is a
separate target. Compared with the formal-conjectures statement `ErdosProblems/362.lean`
(equivalent; no code imported).
-/

/-- **Erdős Problem 362: subsets with a given sum.** There is a real constant $C$ such that for
every nonempty finite set $A \subseteq \mathbb{N}$ with $N$ elements and every $t \in \mathbb{N}$,
the number of subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ is at most
$C \cdot 2^N / N^{3/2}$. -/
def subsetSumCountBound : Prop :=
  ∃ C : ℝ, ∀ (A : Finset ℕ) (t : ℕ), A.Nonempty →
    ((A.powerset.filter fun S => ∑ n ∈ S, n = t).card : ℝ) ≤
      C * 2 ^ A.card / (A.card : ℝ) ^ (3 / 2 : ℝ)

/-- **Erdős Problem 362: subsets of a given size with a given sum.** There is a real constant $C$
such that for every nonempty finite set $A \subseteq \mathbb{N}$ with $N$ elements and all
$l, t \in \mathbb{N}$, the number of $l$-element subsets $S \subseteq A$ with
$\sum_{n \in S} n = t$ is at most $C \cdot 2^N / N^2$. -/
def fixedSizeSubsetSumCountBound : Prop :=
  ∃ C : ℝ, ∀ (A : Finset ℕ) (l t : ℕ), A.Nonempty →
    (((A.powersetCard l).filter fun S => ∑ n ∈ S, n = t).card : ℝ) ≤
      C * 2 ^ A.card / (A.card : ℝ) ^ 2

/--
**Sárközy–Szemerédi bound on subsets with a given sum.** There is a real constant $C$ such that for
every nonempty finite set $A \subseteq \mathbb{N}$ with $N$ elements and every $t \in \mathbb{N}$,
the number of subsets $S \subseteq A$ with $\sum_{n \in S} n = t$ is at most
$C \cdot 2^N / N^{3/2}$.

Sárközy and Szemerédi removed the factor $(\log N)^{3/2}$ from the Erdős–Moser bound; Stanley later
found the extremal sets.

Source: T. F. Bloom, Erdős Problems,
Problem #362, https://www.erdosproblems.com/362 (status PROVED (LEAN)); resolution: A. Sárközy and
E. Szemerédi, Über ein Problem von Erdős und Moser, Acta Arith. (1965), 205-208; G. Halász,
Estimates for the concentration function of combinatorial number theory and probability, Period.
Math. Hungar. (1977), 197-211, erdosproblems.com/362: the first question answered by Sárközy and
Szemerédi, the second by Halász as a consequence of a multi-dimensional result.
-/
public theorem_wanted subsetSumCountBound_holds : subsetSumCountBound

/--
**Halász's bound on subsets of a given size with a given sum.** There is a real constant $C$ such
that for every nonempty finite set $A \subseteq \mathbb{N}$ with $N$ elements and all
$l, t \in \mathbb{N}$, the number of $l$-element subsets $S \subseteq A$ with
$\sum_{n \in S} n = t$ is at most $C \cdot 2^N / N^2$.

Halász proved this as a consequence of a multi-dimensional concentration estimate.

Source: T. F. Bloom, Erdős Problems, Problem #362,
https://www.erdosproblems.com/362 (status PROVED (LEAN)); resolution: A. Sárközy and E. Szemerédi,
Über ein Problem von Erdős und Moser, Acta Arith. (1965), 205-208; G. Halász, Estimates for the
concentration function of combinatorial number theory and probability, Period. Math. Hungar. (1977),
197-211, erdosproblems.com/362: the first question answered by Sárközy and Szemerédi, the second by
Halász as a consequence of a multi-dimensional result.
-/
public theorem_wanted fixedSizeSubsetSumCountBound_holds : fixedSizeSubsetSumCountBound

end MathlibExt.Combinatorics.SubsetSumConcentrationErdosProblem362Wanted
