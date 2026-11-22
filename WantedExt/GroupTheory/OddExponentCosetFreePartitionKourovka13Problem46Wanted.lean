/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Coset-free partitions of abelian groups of odd exponent (Kourovka Notebook Problem 13.46)

Kourovka Notebook, Archive of Solved Problems, Problem 13.46 (I. V. Protasov): can every uncountable
abelian group of finite odd exponent be partitioned into two subsets neither of which contains a
coset of an infinite subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Exponent
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.OddExponentCosetFreePartitionKourovka13Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.46 (I. V.
Protasov). UnsolvedMath record UM-00700964 (`KOU-13.46`), dataset ulamai/UnsolvedMath v1.8.0.

Finite odd exponent is `Monoid.exponent G ≠ 0` and odd. "Contains cosets of infinite subgroups" is
read as containing some coset `g H` of some infinite subgroup `H`, so the partition must avoid every
such coset in both cells.
-/

open scoped Pointwise

/-- **Kourovka Problem 13.46: coset-free partitions.** The proposition that every uncountable
abelian group $G$ of finite odd exponent can be written as $G = A_1 \cup A_2$ with $A_1$ and $A_2$
disjoint, so that for every infinite subgroup $H$ of $G$ and every $g \in G$, the coset $gH$ is
contained neither in $A_1$ nor in $A_2$. The problem is due to I. V. Protasov. -/
def oddExponentCosetFreePartition : Prop :=
  ∀ (G : Type) [CommGroup G], Uncountable G → Monoid.exponent G ≠ 0 →
    Odd (Monoid.exponent G) →
    ∃ A₁ A₂ : Set G, A₁ ∪ A₂ = Set.univ ∧ Disjoint A₁ A₂ ∧
      ∀ H : Subgroup G, (H : Set G).Infinite → ∀ g : G,
        ¬ g • (H : Set G) ⊆ A₁ ∧ ¬ g • (H : Set G) ⊆ A₂

/--
**Uncountable abelian groups of odd exponent have coset-free partitions.** Every uncountable
abelian group $G$ of finite odd exponent can be written as $G = A_1 \cup A_2$ with $A_1$ and $A_2$
disjoint, so that for every infinite subgroup $H$ of $G$ and every $g \in G$, the coset $gH$ is
contained neither in $A_1$ nor in $A_2$. This answers Kourovka Problem 13.46 in the affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 13.46 (I. V. Protasov); resolution: E. G. Zelenyuk, Math. Notes 67 (2000), 599-602, Kourovka
Archive, Problem 13.46 (answer: Yes, it can).
-/
public theorem_wanted oddExponentCosetFreePartition_holds : oddExponentCosetFreePartition

end MathlibExt.GroupTheory.OddExponentCosetFreePartitionKourovka13Problem46Wanted
