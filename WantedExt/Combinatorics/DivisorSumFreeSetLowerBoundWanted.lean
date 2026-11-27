/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-131: Is F(N) > N^{1/2-o(1)}, where F(N) is the maximal size of a subset
of {1,...,N} with no element dividing the sum of any distinct others?

Since F(N) is a maximum over a finite family, F(N) > b holds iff some
divisor-sum-free S ⊆ {1,...,N} has |S| > b; the entry uses that form.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Divisors
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.DivisorSumFreeSetLowerBoundWanted

/-! Source record `EP-131`. -/

/-- **Divisor-sum-free sets.** A finite set $S$ of natural numbers is divisor-sum-free if no
element $x \in S$ divides the sum of the elements of any nonempty subset of $S \setminus \{x\}$. -/
def IsDivisorSumFree (S : Finset Nat) : Prop :=
  ∀ x ∈ S, ∀ T ∈ (S.erase x).powerset, T.Nonempty → ¬ (x ∣ T.sum id)

/-- **Erdős Problem 131: large divisor-sum-free sets.** The proposition that for every real
$\varepsilon > 0$ there is a natural number $N_0$ such that for every natural number $N \ge 1$ with
$N \ge N_0$ there is a set $S \subseteq \{1, \dots, N\}$ with $|S| > N^{1/2 - \varepsilon}$ that is
divisor-sum-free: no element $x \in S$ divides the sum of the elements of any nonempty subset of
$S \setminus \{x\}$. -/
def conjecture : Prop :=
  ∀ ε : Real, 0 < ε →
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → 1 ≤ N →
      ∃ S : Finset Nat, (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧
        IsDivisorSumFree S ∧
          (S.card : Real) > (N : Real) ^ ((1 / 2 : Real) - ε)

/--
**Erdős Problem 131 has a negative answer.** It is not true that for every real
$\varepsilon > 0$ there is a natural number $N_0$ such that for every natural number $N \ge 1$ with
$N \ge N_0$ there is a set $S \subseteq \{1, \dots, N\}$ with $|S| > N^{1/2 - \varepsilon}$ that is
divisor-sum-free, meaning that no element $x \in S$ divides the sum of the elements of any nonempty
subset of $S \setminus \{x\}$.

Let $F(N)$ be the largest size of a divisor-sum-free subset of $\{1, \dots, N\}$. Every
divisor-sum-free set is non-averaging, that is, none of its elements is the average of other
elements of the set (an element equal to the average of $k$ others divides their sum), and Pham
and Zakharov (arXiv:2410.14624) prove that the largest non-averaging subset of $\{1, \dots, N\}$
has size $N^{1/4 + o(1)}$, so $F(N) \le N^{1/4 + o(1)}$; erdosproblems.com/131 (checked
2026-10-22) records that this answers the question negatively. The page also links a formal proof
of $F(N) \le N^{1/5 + o(1)}$, which with Csaba's $F(N) \gg N^{1/5}$ would give the order of growth.

Source: H. T.
Pham and D. Zakharov, Sharp bound for the Erdős-Straus non-averaging set problem,
arXiv:2410.14624 (2024), https://arxiv.org/abs/2410.14624. Moved from
`OpenConjectures/Combinatorics/DivisorSumFreeSetLowerBound`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.DivisorSumFreeSetLowerBoundWanted
