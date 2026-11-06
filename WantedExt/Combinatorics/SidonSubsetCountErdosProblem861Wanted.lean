/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The number of Sidon subsets of `{1, …, N}` (Erdős Problem 861)

Erdős Problem 861 (Cameron and Erdős): let `f(N)` be the size of the largest Sidon subset of `{1, …,
N}` and `A(N)` the number of Sidon subsets of `{1, …, N}`. Is it true that `A(N) / 2^{f(N)} → ∞`? Is
it true that `A(N) = 2^{(1 + o(1)) f(N)}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #861, https://www.erdosproblems.com/861 (status
SOLVED). UnsolvedMath record UM-30007063 (`EP-861`), dataset ulamai/UnsolvedMath v1.8.0.

Sidon is `MathlibExt`'s `Set.IsSidon`; `A(N)` counts all Sidon subsets, including the empty set and
singletons. `A(N) = 2^{(1 + o(1)) f(N)}` is `log₂ A(N) / f(N) → 1`. formal-conjectures has no
statement of this problem.
-/

open Classical in
/-- **Sidon subsets of $\{1, \dots, N\}$.** For a natural number $N$, this is the finite family
of all subsets of $\{1, \dots, N\}$ that are Sidon sets of natural numbers, including the empty
set and the singletons. -/
noncomputable def sidonSubsetsUpTo (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter fun S => (S : Set ℕ).IsSidon

/-- **Largest Sidon subset of $\{1, \dots, N\}$ (Erdős Problem 861).** For a natural number $N$,
$f(N)$ is the largest cardinality of a Sidon subset of $\{1, \dots, N\}$. -/
noncomputable def maxSidonSize (N : ℕ) : ℕ :=
  (sidonSubsetsUpTo N).sup Finset.card

/-- **Erdős Problem 861, first question.** Let $A(N)$ be the number of Sidon subsets of
$\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. The statement is that
$A(N) / 2^{f(N)} \to \infty$ as $N \to \infty$. -/
def sidonCountOverTwoPowMaxDiverges : Prop :=
  Filter.Tendsto (fun N : ℕ => ((sidonSubsetsUpTo N).card : ℝ) / 2 ^ maxSidonSize N)
    Filter.atTop Filter.atTop

/-- **Erdős Problem 861, second question.** Let $A(N)$ be the number of Sidon subsets of
$\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. The statement is that
$\log_2 A(N) / f(N) \to 1$ as $N \to \infty$, that is, $A(N) = 2^{(1 + o(1)) f(N)}$. -/
def sidonCountExponentAsymptotic : Prop :=
  Filter.Tendsto (fun N : ℕ => Real.logb 2 (sidonSubsetsUpTo N).card / maxSidonSize N)
    Filter.atTop (nhds 1)

/--
**Erdős Problem 861, first question: positive answer.** Let $A(N)$ be the number of Sidon
subsets of $\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. Then $A(N) / 2^{f(N)} \to \infty$ as
$N \to \infty$.

Saxton and Thomason proved $A(N) \ge 2^{(1.16 + o(1)) \sqrt{N}}$ (Theorem 2.11), and
$f(N) \sim \sqrt{N}$, so $A(N) / 2^{f(N)} \ge 2^{(0.16 + o(1)) \sqrt{N}} \to \infty$.

Source: T. F. Bloom, Erdős Problems, Problem #861,
https://www.erdosproblems.com/861 (status SOLVED); resolution: D. Saxton and A. Thomason, Hypergraph
containers, Invent. Math. (2015), 925-992, arXiv:1204.6595 (lower bound); Y. Kohayakawa, S. J. Lee,
V. Rödl and W. Samotij, The number of Sidon sets and the maximum size of Sidon sets contained in a
sparse random set of integers, Random Structures Algorithms (2015), 1-25 (upper bound),
Saxton-Thomason Theorem 2.11: there are between 2^{(1.16 + o(1)) √n} and 2^{(55 + o(1)) √n} Sidon
subsets of [n], the lower bound answering negatively whether there are only 2^{(1 + o(1)) √n};
erdosproblems.com/861: f(N) ∼ N^{1/2}, both questions are settled, the first positively and the
second negatively, and 2^{1.16 f(N)} ≤ A(N) ≤ 2^{6.442 f(N)} for large N,
https://arxiv.org/abs/1204.6595.
-/
public theorem_wanted sidonCountOverTwoPowMaxDiverges_holds : sidonCountOverTwoPowMaxDiverges

/--
**Erdős Problem 861, second question: negative answer.** Let $A(N)$ be the number of Sidon
subsets of $\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. Then the ratio $\log_2 A(N) / f(N)$ does not
tend to $1$ as $N \to \infty$; that is, $A(N) = 2^{(1 + o(1)) f(N)}$ fails.

Saxton and Thomason proved $A(N) \ge 2^{(1.16 + o(1)) \sqrt{N}}$ (Theorem 2.11), and
$f(N) \sim \sqrt{N}$, so $\log_2 A(N) / f(N) \ge 1.16 + o(1)$.

Source: T. F. Bloom, Erdős Problems, Problem #861, https://www.erdosproblems.com/861 (status
SOLVED); resolution: D. Saxton and A. Thomason, Hypergraph containers, Invent. Math. (2015),
925-992, arXiv:1204.6595 (lower bound); Y. Kohayakawa, S. J. Lee, V. Rödl and W. Samotij, The number
of Sidon sets and the maximum size of Sidon sets contained in a sparse random set of integers,
Random Structures Algorithms (2015), 1-25 (upper bound), Saxton-Thomason Theorem 2.11: there are
between 2^{(1.16 + o(1)) √n} and 2^{(55 + o(1)) √n} Sidon subsets of [n], the lower bound answering
negatively whether there are only 2^{(1 + o(1)) √n}; erdosproblems.com/861: f(N) ∼ N^{1/2}, both
questions are settled, the first positively and the second negatively, and 2^{1.16 f(N)} ≤ A(N) ≤
2^{6.442 f(N)} for large N, https://arxiv.org/abs/1204.6595.
-/
public theorem_wanted sidonCountExponentAsymptotic_refuted : ¬ sidonCountExponentAsymptotic

end MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted
