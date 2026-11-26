/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Cameron-Erdős conjecture (Erdős Problem 748)

Erdős Problem 748: let `f(n)` count the number of sum-free `A ⊆ {1, …, n}`, i.e. `A` contains no
solutions to `a = b + c` with `a, b, c ∈ A`. Is it true that `f(n) = 2^{(1 + o(1)) n / 2}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace MathlibExt.Combinatorics.SumFreeSubsetCountErdosProblem748Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #748, https://www.erdosproblems.com/748 (status
PROVED). UnsolvedMath record UM-30007010 (`EP-748`), dataset ulamai/UnsolvedMath v1.8.0.

`b = c` is allowed, as in the problem; the empty set counts. `f(n) = 2^{(1 + o(1)) n / 2}` is `log₂
f(n) / n → 1/2`. Compared with the formal-conjectures statement `ErdosProblems/748.lean`
(equivalent; no code imported).
-/

/-- **Number of sum-free subsets of $\{1, \dots, n\}$.** For a natural number $n$, $f(n)$ is the
number of sets $A \subseteq \{1, \dots, n\}$ that are sum-free, meaning that there are no
$a, b, c \in A$ with $a = b + c$ (the case $b = c$ included). The empty set is counted. -/
def sumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A => ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c).card

/-- **Erdős Problem 748 on the number of sum-free sets.** Let $f(n)$ be the number of sum-free
subsets of $\{1, \dots, n\}$. This is the statement that $\log_2 f(n) / n \to 1/2$ as
$n \to \infty$, that is, $f(n) = 2^{(1 + o(1)) n / 2}$. -/
def sumFreeCountExponent : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.logb 2 (sumFreeCount n) / n) Filter.atTop (nhds (1 / 2))

/-- **Sum-free subsets of $\{1, \dots, n\}$ number $2^{(1 + o(1)) n / 2}$.** Let $f(n)$ be the
number of sum-free subsets of $\{1, \dots, n\}$, that is, of sets $A \subseteq \{1, \dots, n\}$
with no $a, b, c \in A$ satisfying $a = b + c$ (the case $b = c$ included). Then
$\log_2 f(n) / n \to 1/2$ as $n \to \infty$, that is, $f(n) = 2^{(1 + o(1)) n / 2}$.

Source: T. F. Bloom, Erdős Problems, Problem #748, https://www.erdosproblems.com/748 (status
PROVED); resolution: B. Green, The Cameron-Erdős conjecture, Bull. London Math. Soc. 36 (2004),
769-778; A. A. Sapozhenko, The Cameron-Erdős conjecture, Dokl. Akad. Nauk 393 (2003), 749-752,
abstract of arXiv:math/0304058 (Green): the number of sum-free subsets of {1, …, N} is
O(2^{N/2}); erdosproblems.com/748: true, in fact f(n) ≪ 2^{n/2} (Green; Sapozhenko), with the
trivial lower bound from subsets of the upper half, https://arxiv.org/abs/math/0304058.
-/
public theorem_wanted sumFreeCountExponent_holds : sumFreeCountExponent

end MathlibExt.Combinatorics.SumFreeSubsetCountErdosProblem748Wanted
