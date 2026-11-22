/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partitions of `⊕_{ω₁} ℤ/3ℤ` meeting every infinite coset (Kourovka Notebook Problem 16.43)

Kourovka Notebook, Archive of Solved Problems, Problem 16.43 (E. G. Zelenyuk): is there a partition
of the group `⊕_{ω₁} ℤ/3ℤ` into three subsets whose complements do not contain cosets modulo
infinite subgroups? (There is a partition into two such subsets.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

namespace MathlibExt.GroupTheory.PartitionMeetingInfiniteCosetsKourovka16Problem43Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.43 (E. G.
Zelenyuk). UnsolvedMath record UM-00701235 (`KOU-16.43`), dataset ulamai/UnsolvedMath v1.8.0.

`⊕_{ω₁} ℤ/3ℤ` is the group `ι →₀ ZMod 3` of finitely supported functions on an index set `ι` of
cardinality `ℵ₁`. A partition into three subsets is a colouring `c : G → Fin 3`; the complement of a
part contains no coset of an infinite subgroup exactly when the part meets every such coset.
-/

/-- **Kourovka 16.43: partitioning $\bigoplus_{\omega_1} \mathbb{Z}/3\mathbb{Z}$ into three parts
meeting every infinite coset.** The proposition that for every set $I$ of cardinality $\aleph_1$,
the group $A = \bigoplus_{i \in I} \mathbb{Z}/3\mathbb{Z}$ of finitely supported functions from $I$
to $\mathbb{Z}/3\mathbb{Z}$ can be partitioned into three subsets $A_0, A_1, A_2$ such that for
every infinite subgroup $H$ of $A$ and every $x \in A$, the coset $x + H$ meets each $A_i$. -/
def threePartitionMeetsInfiniteCosets : Prop :=
  ∀ ι : Type, Cardinal.mk ι = Cardinal.aleph 1 →
    ∃ c : (ι →₀ ZMod 3) → Fin 3, ∀ H : AddSubgroup (ι →₀ ZMod 3),
      (H : Set (ι →₀ ZMod 3)).Infinite → ∀ (x : ι →₀ ZMod 3) (i : Fin 3), ∃ h ∈ H, c (x + h) = i

/--
**A partition of $\bigoplus_{\omega_1} \mathbb{Z}/3\mathbb{Z}$ into three parts meeting every
infinite coset.** Let $I$ be a set of cardinality $\aleph_1$ and let $A = \bigoplus_{i \in I}
\mathbb{Z}/3\mathbb{Z}$ be the group of finitely supported functions from $I$ to
$\mathbb{Z}/3\mathbb{Z}$. Then $A$ can be partitioned into three subsets $A_0, A_1, A_2$ such that
for every infinite subgroup $H$ of $A$ and every $x \in A$, the coset $x + H$ meets each $A_i$.

The Kourovka Archive records more: every infinite abelian group with finitely many involutions can
be partitioned into infinitely many subsets such that every coset modulo an infinite subgroup meets
each subset of the partition.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.43 (E. G.
Zelenyuk); resolution: Y. Zelenyuk, J. Combin. Theory Ser. A 115 (2008), 331-339, Kourovka Archive,
Problem 16.43 (Yes; moreover every infinite abelian group with finitely many involutions can be
partitioned into infinitely many subsets such that every coset modulo an infinite subgroup meets
each subset).
-/
public theorem_wanted threePartitionMeetsInfiniteCosets_holds : threePartitionMeetsInfiniteCosets

end MathlibExt.GroupTheory.PartitionMeetingInfiniteCosetsKourovka16Problem43Wanted
