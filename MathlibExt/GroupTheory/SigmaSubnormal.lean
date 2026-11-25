/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.CompletePartialOrder

/-!
# σ-subnormal subgroups

A partition of the primes defines σ-primary integers and σ-subnormal subgroup chains.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Partitions of the primes.** A family $\sigma = (\sigma_i)_{i \in I}$ of sets of natural
numbers is a partition of the primes if every $\sigma_i$ is a nonempty set of primes, $\sigma_i$
and $\sigma_j$ are disjoint whenever $i \ne j$, and every prime lies in some $\sigma_i$. -/
def IsPrimePartition {I : Type} (σ : I → Set ℕ) : Prop :=
  (∀ i, (σ i).Nonempty ∧ ∀ p ∈ σ i, p.Prime) ∧ (∀ i j, i ≠ j → Disjoint (σ i) (σ j)) ∧
    ∀ p : ℕ, p.Prime → ∃ i, p ∈ σ i

/-- **$\sigma$-primary numbers.** For a family $\sigma = (\sigma_i)_{i \in I}$ of sets of natural
numbers, a natural number $n$ is $\sigma$-primary if there is an index $i$ such that every prime
divisor of $n$ lies in $\sigma_i$. For $n = 0$ this means that some $\sigma_i$ contains every
prime.

A finite group is called $\sigma$-primary when its order is. -/
def IsSigmaPrimary {I : Type} (σ : I → Set ℕ) (n : ℕ) : Prop :=
  ∃ i, ∀ p : ℕ, p.Prime → p ∣ n → p ∈ σ i

/-- **$\sigma$-subnormal subgroups.** For a family $\sigma = (\sigma_i)_{i \in I}$ of sets of
natural numbers, a subgroup $A$ of a group $G$ is $\sigma$-subnormal in $G$ if there is a chain of
subgroups $A = A_0 \le A_1 \le \cdots \le A_n = G$ such that for every $i < n$ either $A_i$ is
normal in $A_{i+1}$, or the index in $A_{i+1}$ of the normal core of $A_i$ in $A_{i+1}$ is
$\sigma$-primary (an infinite index counts as $0$). -/
def IsSigmaSubnormal {I : Type} (σ : I → Set ℕ) {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  ∃ (n : ℕ) (K : ℕ → Subgroup G), K 0 = A ∧ K n = ⊤ ∧ ∀ i < n, K i ≤ K (i + 1) ∧
    (((K i).subgroupOf (K (i + 1))).Normal ∨
      IsSigmaPrimary σ ((K i).subgroupOf (K (i + 1))).normalCore.index)

end MathlibExt.GroupTheory.KourovkaNotebookShared
