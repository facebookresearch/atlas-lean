/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

@[expose] public section

/-!
# Cyclic sublattices of additive commutative groups

This module introduces a reusable predicate recording when one additive
subgroup is a cyclic sublattice of another: the smaller subgroup is
contained in the larger one, and the quotient formed inside the larger
subgroup is cyclic.
-/

namespace AddSubgroup

variable {A : Type*} [AddCommGroup A]

/-- **Cyclic sublattice of a subgroup.** Let $A$ be an abelian group and let $L'$ and $L$ be
subgroups of $A$. Then $L'$ is a cyclic sublattice of $L$ when $L' \subseteq L$ and the quotient
group $L/L'$ is cyclic; formally the quotient is taken by $L' \cap L$, regarded as a subgroup
of $L$. -/
def IsCyclicSublattice (L' L : AddSubgroup A) : Prop :=
  L' ≤ L ∧ IsAddCyclic (L ⧸ L'.addSubgroupOf L)

/-- **Characterization of cyclic sublattices.** Let $L'$ and $L$ be subgroups of an abelian
group $A$. Then $L'$ is a cyclic sublattice of $L$ if and only if $L' \subseteq L$ and the
quotient group $L/(L' \cap L)$, with $L' \cap L$ regarded as a subgroup of $L$, is cyclic. -/
theorem isCyclicSublattice_iff {L' L : AddSubgroup A} :
    IsCyclicSublattice L' L ↔
      L' ≤ L ∧ IsAddCyclic (L ⧸ L'.addSubgroupOf L) :=
  Iff.rfl

/-- **A cyclic sublattice is contained in its ambient subgroup.** Let $L'$ and $L$ be subgroups
of an abelian group $A$. If $L'$ is a cyclic sublattice of $L$, then $L' \subseteq L$. -/
theorem IsCyclicSublattice.le {L' L : AddSubgroup A}
    (h : IsCyclicSublattice L' L) : L' ≤ L :=
  h.1

/-- **The quotient by a cyclic sublattice is cyclic.** Let $L'$ and $L$ be subgroups of an
abelian group $A$. If $L'$ is a cyclic sublattice of $L$, then the quotient group $L/L'$ is
cyclic. -/
theorem IsCyclicSublattice.isAddCyclic_quotient {L' L : AddSubgroup A}
    (h : IsCyclicSublattice L' L) :
    IsAddCyclic (L ⧸ L'.addSubgroupOf L) :=
  h.2

/-- **Criterion for a cyclic sublattice.** Let $L'$ and $L$ be subgroups of an abelian group $A$.
If $L' \subseteq L$ and the quotient group $L/L'$ is cyclic, then $L'$ is a cyclic sublattice
of $L$. -/
theorem IsCyclicSublattice.mk {L' L : AddSubgroup A} (hle : L' ≤ L)
    (hcyc : IsAddCyclic (L ⧸ L'.addSubgroupOf L)) :
    IsCyclicSublattice L' L :=
  ⟨hle, hcyc⟩

end AddSubgroup
