/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The number of maximal sum-free subsets of `{1, …, n}` (Erdős Problem 877)

Erdős Problem 877 (Cameron and Erdős): let `f_m(n)` count the maximal sum-free subsets `A ⊆ {1, …,
n}` (no solutions to `a = b + c` in `A`, and `A` maximal with this property). Estimate `f_m(n)`; is
it true that `f_m(n) = o(2^{n/2})`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WantedExt.Combinatorics.GreenProblem1LargeSumFreeWanted

@[expose] public section

namespace MathlibExt.Combinatorics.MaximalSumFreeSetsCountErdosProblem877Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #877, https://www.erdosproblems.com/877 (status
PROVED). UnsolvedMath record UM-30007069 (`EP-877`), dataset ulamai/UnsolvedMath v1.8.0.

Sum-free is `IsSumFree` of the Green Problem 1 entry, reused here: no `x + y ∈ A` with `x, y ∈ A`
(`x = y` allowed). Maximality is within `{1, …, n}`. The open-ended 'estimate `f_m(n)`'
(Balogh, Liu, Sharifzadeh and Treglown: `f_m(n) = 2^{(1/4 + o(1)) n}`) is not formalized. Compared
with the formal-conjectures statement `ErdosProblems/877.lean` (equivalent; no code imported).
-/

open MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted (IsSumFree)

open Classical in
/-- **Number of maximal sum-free subsets of $\{1, \dots, n\}$.** For a natural number $n$,
$f_m(n)$ is the number of sets $A \subseteq \{1, \dots, n\}$ that are sum-free, meaning
$x + y \notin A$ for all $x, y \in A$ (including $x = y$), and maximal with this property:
every sum-free set $B$ with $A \subseteq B \subseteq \{1, \dots, n\}$ equals $A$. -/
noncomputable def maximalSumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A =>
    IsSumFree A ∧ ∀ B ⊆ Finset.Icc 1 n, A ⊆ B → IsSumFree B → B = A).card

/-- **Erdős Problem 877 on maximal sum-free sets.** Let $f_m(n)$ be the number of maximal
sum-free subsets of $\{1, \dots, n\}$. This is the statement, asked by Cameron and Erdős, that
$f_m(n) / 2^{n/2} \to 0$ as $n \to \infty$, that is, $f_m(n) = o(2^{n/2})$. -/
def maximalSumFreeCountSmall : Prop :=
  Filter.Tendsto (fun n : ℕ => (maximalSumFreeCount n : ℝ) / 2 ^ ((n : ℝ) / 2))
    Filter.atTop (nhds 0)

/-- **Maximal sum-free subsets of $\{1, \dots, n\}$ number $o(2^{n/2})$.** Let $f_m(n)$ be the
number of maximal sum-free subsets of $\{1, \dots, n\}$. Then $f_m(n) / 2^{n/2} \to 0$ as
$n \to \infty$, that is, $f_m(n) = o(2^{n/2})$.

Source: T. F. Bloom, Erdős Problems, Problem #877, https://www.erdosproblems.com/877 (status
PROVED); resolution: T. Łuczak and T. Schoen, On the number of maximal sum-free sets, Proc. Amer.
Math. Soc. 129 (2001), 2205-2207, abstract: {1, 2, …, n} contains at most 2^{n/2 - 2^{-28} n}
maximal sum-free subsets, provided n is large enough; erdosproblems.com/877: this resolves the
question, and Balogh, Liu, Sharifzadeh and Treglown later proved f_m(n) = 2^{(1/4 + o(1)) n},
https://doi.org/10.1090/S0002-9939-00-05815-9.
-/
public theorem_wanted maximalSumFreeCountSmall_holds : maximalSumFreeCountSmall

end MathlibExt.Combinatorics.MaximalSumFreeSetsCountErdosProblem877Wanted
