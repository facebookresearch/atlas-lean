/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 857: weak sunflower conjecture for k ≥ 4

See https://www.erdosproblems.com/857 and P. Erdős and E. Szemerédi,
"Combinatorial properties of systems of sets,"
Journal of Combinatorial Theory, Series A 24(3) (1978), 308–313.
UnsolvedMath record id 2345 / EP-857. Proved by Bucić, He and Lee,
arXiv:2610.26686 (2026), Theorem 1; this repository records no Lean proof.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem857WeakSunflowerWanted

/-- **Families containing a sunflower.** Let $n$ and $k$ be natural numbers. A family $F$ of
subsets of $\{0, \dots, n-1\}$ contains a $k$-sunflower if some subfamily $T \subseteq F$ with
exactly $k$ members satisfies $A \cap B = C \cap D$ for all $A, B, C, D \in T$ with $A \ne B$ and
$C \ne D$, that is, all pairwise intersections of distinct members of $T$ are equal. -/
def ContainsKSunflower {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∃ (T : Finset (Finset (Fin n))), T ⊆ F ∧ T.card = k ∧
    ∀ ⦃a⦄, a ∈ T → ∀ ⦃b⦄, b ∈ T → a ≠ b → ∀ ⦃c⦄, c ∈ T → ∀ ⦃d⦄, d ∈ T → c ≠ d → a ∩ b = c ∩ d

/-- **Sunflower-free families.** Let $n$ and $k$ be natural numbers. A family $F$ of subsets of
$\{0, \dots, n-1\}$ is $k$-sunflower-free if it does not contain a $k$-sunflower. -/
def IsKSunflowerFree {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ¬ ContainsKSunflower (n := n) k F

/-- **Erdős–Szemerédi sunflower conjecture for $k \ge 4$.** The proposition asserts that for every
natural number $k \ge 4$ there is a real number $c$ with $0 < c < 2$ such that, for all
sufficiently large $n$, every $k$-sunflower-free family of subsets of $\{0, \dots, n-1\}$ has at
most $c^n$ members.

The bound is required only for large $n$ because for $2^n < k$ the family of all subsets of
$\{0, \dots, n-1\}$ is $k$-sunflower-free. The case $k = 3$, proved by Naslund and Sawin, is
omitted. -/
def conjecture : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ c : ℝ, 0 < c ∧ c < 2 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ F : Finset (Finset (Fin n)),
          IsKSunflowerFree k F →
            (F.card : ℝ) ≤ c ^ n

/--
**The Erdős–Szemerédi sunflower bound for $k \ge 4$.** For every natural number $k \ge 4$ there
is a real number $c$ with $0 < c < 2$ such that, for all sufficiently large $n$, every family of
subsets of $\{0, \dots, n-1\}$ that contains no $k$-sunflower has at most $c^n$ members. Here a
$k$-sunflower in a family is a choice of $k$ distinct members whose pairwise intersections are
all equal.

Resolved true: Proved: Bucić, He and Lee (arXiv:2610.26686, 2026, Theorem 1) show that for every
k >= 3 and n >= 1 a family of subsets of [n] with no k-sunflower has at most 3(2 - 1/(16k^3))^n
members, which gives the formalized bound c^n with c < 2 for each k >= 4 and all large n.
erdosproblems.com/857 (checked 2026-10-22) records this bound as known. The paper states that
the proof of its vector-sunflower bound (Theorem 2) was found by ChatGPT 6 Astra Pro and
verified by the authors. Source: Matija Bucić, Fankang He and Hyunwoo Lee, Proof of the
Erdős-Szemerédi sunflower conjecture, arXiv:2610.26686 (2026), https://arxiv.org/abs/2610.26686;
T. F. Bloom, Erdős Problem #857, erdosproblems.com, https://www.erdosproblems.com/857. Moved
from `OpenConjectures/Combinatorics/ErdosProblem857WeakSunflower`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem857WeakSunflowerWanted
