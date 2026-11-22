/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

namespace MetaMathlibExt

@[expose] public section

/-- **Highly homogeneous permutation groups.** Let $G$ be a group of permutations of a set
$\alpha$. Then $G$ is highly homogeneous when, for every natural number $k$, it acts transitively
on the $k$-element subsets of $\alpha$: for any two $k$-element subsets $X$ and $Y$ of $\alpha$
there is some $g \in G$ with $g(X) = Y$. -/
def IsHighlyHomogeneous {α : Type*} [DecidableEq α]
    (G : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ k : ℕ, MulAction.IsPretransitive G ↑(Set.powersetCard α k)

/-- **The full symmetric group is highly homogeneous.** For every set $\alpha$, the group of all
permutations of $\alpha$ is highly homogeneous: for every natural number $k$, any $k$-element
subset of $\alpha$ can be carried to any other $k$-element subset of $\alpha$ by some permutation
of $\alpha$. -/
theorem isHighlyHomogeneous_top {α : Type*} [DecidableEq α] :
    IsHighlyHomogeneous (⊤ : Subgroup (Equiv.Perm α)) := by
  intro k
  have hbase : MulAction.IsPretransitive (Equiv.Perm α) ↥(Set.powersetCard α k) :=
    Set.powersetCard.isPretransitive
  constructor
  intro x y
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Equiv.Perm α) x y
  exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩

end

end MetaMathlibExt
