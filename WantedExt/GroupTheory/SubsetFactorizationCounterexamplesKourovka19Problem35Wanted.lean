/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subset factorizations of finite groups fail for every length (Kourovka Notebook Problem 19.35)

Kourovka Notebook, Archive of Solved Problems, Problem 19.35 (M. H. Hooshmand): let `G` be a finite
group of order `n`. Is it true that for every factorization `n = a₁ ⋯ a_k` there exist subsets `A₁,
…, A_k` such that `|A₁| = a₁, …, |A_k| = a_k` and `G = A₁ ⋯ A_k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.SubsetFactorizationCounterexamplesKourovka19Problem35Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.35 (M. H.
Hooshmand). UnsolvedMath record UM-00701583 (`KOU-19.35`), dataset ulamai/UnsolvedMath v1.8.0.

Reading. The Archive answers "No" with Bergman's counterexample (`A₄`, `k = 3`, `(2, 3, 2)`) and
adds that counterexamples for all `k ≥ 3` are constructed by McCulloch (an unrefereed preprint with
no journal record as of 2026-10-24, accepted by the Archive's own answer; its Theorem 2.3 has a
one-page proof extending Bergman's argument). One explicit group of order 12 is a finite check, so
the plain refutation is not stated; the module states the recorded family answer. As in McCulloch's
Definition 1.1 the factors satisfy `1 < aᵢ`: with factors `1` allowed, padding Bergman's example
with singletons would give every `k ≥ 3` trivially. Products of subsets are taken in the given
order, `A₀ A₁ ⋯ A_{k-1}`.
-/

/-- **Factorization of a group into subsets of given sizes.** Let $G$ be a group, $k$ a natural
number and $a_0, \dots, a_{k-1}$ natural numbers. The group $G$ has a subset factorization of
type $(a_0, \dots, a_{k-1})$ when there are finite subsets $A_0, \dots, A_{k-1}$ of $G$ with
$|A_i| = a_i$ for every $i$ such that $G = A_0 A_1 \cdots A_{k-1}$, that is, every $g \in G$ can be
written as $g = x_0 x_1 \cdots x_{k-1}$ with $x_i \in A_i$ for every $i$. -/
def HasSubsetFactorization (G : Type) [Group G] (k : ℕ) (a : Fin k → ℕ) : Prop :=
  ∃ A : Fin k → Finset G, (∀ i, (A i).card = a i) ∧
    ∀ g : G, ∃ x : Fin k → G, (∀ i, x i ∈ A i) ∧ (List.ofFn x).prod = g

/-- **Kourovka Problem 19.35: counterexamples to subset factorization of every length.** The
statement that for every natural number $k \ge 3$ there are a finite group $G$ and natural numbers
$a_0, \dots, a_{k-1}$, each at least $2$, with $a_0 a_1 \cdots a_{k-1} = |G|$, such that $G$ has
no subset factorization of type $(a_0, \dots, a_{k-1})$: there are no subsets
$A_0, \dots, A_{k-1}$ of $G$ with $|A_i| = a_i$ for every $i$ and $G = A_0 A_1 \cdots A_{k-1}$. -/
def subsetFactorizationCounterexampleEveryLength : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ (G : Type) (_ : Group G) (_ : Finite G) (a : Fin k → ℕ),
    (∀ i, 2 ≤ a i) ∧ ∏ i, a i = Nat.card G ∧ ¬ HasSubsetFactorization G k a

/--
**Finite groups without subset factorizations exist for every length.** For every natural number
$k \ge 3$ there are a finite group $G$ and natural numbers $a_0, \dots, a_{k-1}$, each at least
$2$, with $a_0 a_1 \cdots a_{k-1} = |G|$, such that there are no subsets $A_0, \dots, A_{k-1}$ of
$G$ with $|A_i| = a_i$ for every $i$ and $G = A_0 A_1 \cdots A_{k-1}$, that is, with every element
of $G$ a product $x_0 x_1 \cdots x_{k-1}$ where $x_i \in A_i$ for every $i$.

In McCulloch's Theorem 2.3, $G$ is a Frobenius group of order $2^{k-1}(2^{k-1} - 1)$ and the
factors are $(2, \dots, 2, 2^{k-1} - 1, 2)$; the case $k = 3$ is Bergman's example in the
alternating group $A_4$. This answers Kourovka Problem 19.35 (M. H. Hooshmand) in the negative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 19.35 (M. H. Hooshmand); resolution: R. McCulloch, Some answers regarding factorizations of
finite groups, arXiv:2607.20569 (2026); counterexamples first given by M. Kabenyuk, Factorizations
of finite groups, arXiv:2102.08605, Kourovka Archive, Problem 19.35: No (Bergman's A4 example for k
= 3); counterexamples for all k ≥ 3 are constructed in (McCulloch); paper, Theorem 2.3: the
Frobenius group of order 2^(k-1)(2^(k-1) - 1) has no k-fold factorization for (2, …, 2, 2^(k-1) - 1,
2), https://arxiv.org/abs/2607.20569.
-/
public theorem_wanted subsetFactorizationCounterexampleEveryLength_holds :
    subsetFactorizationCounterexampleEveryLength

end MathlibExt.GroupTheory.SubsetFactorizationCounterexamplesKourovka19Problem35Wanted
