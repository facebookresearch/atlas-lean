/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subgroups permuting with minimal non-nilpotent subgroups (Kourovka Notebook Problem 17.56)

Kourovka Notebook, Problem 17.56 (V. N. Knyagina, V. S. Monakhov): suppose that a subgroup `H` of a
finite group `G` is such that `HM = MH` for every minimal non-nilpotent subgroup `M` of `G`. Must
`H/H_G` be nilpotent, where `H_G` is the largest normal subgroup of `G` contained in `H`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.MinimalNonNilpotentPermutableCoreKourovka17Problem56Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.56 (V. N. Knyagina, V. S. Monakhov).
UnsolvedMath record UM-00701358 (`KOU-17.56`), dataset ulamai/UnsolvedMath v1.8.0.

A minimal non-nilpotent subgroup is a non-nilpotent subgroup all of whose proper subgroups are
nilpotent. `HM` is the pointwise set product, `H_G` is `H.normalCore`, and `H/H_G` is the quotient
of `H` by `H_G` viewed as a normal subgroup of `H`.
-/

open scoped Pointwise

/-- **Minimal non-nilpotent subgroup.** A subgroup $M$ of a group $G$ is minimal non-nilpotent if
$M$ is not nilpotent but every proper subgroup of $M$ is nilpotent. -/
def IsMinimalNonNilpotent {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  ¬ Group.IsNilpotent M ∧ ∀ K : Subgroup G, K < M → Group.IsNilpotent K

/-- **Subgroups permuting with all minimal non-nilpotent subgroups (Kourovka 17.56).** The
statement that if $H$ is a subgroup of a finite group $G$ with $HM = MH$ (as sets of products) for
every minimal non-nilpotent subgroup $M$ of $G$, then the quotient $H/H_G$ is nilpotent, where the
normal core $H_G$ is the largest normal subgroup of $G$ contained in $H$.

The question is due to V. N. Knyagina and V. S. Monakhov. -/
def permutesMinimalNonNilpotentCoreQuotientNilpotent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G),
    (∀ M : Subgroup G, IsMinimalNonNilpotent M → (H : Set G) * M = M * H) →
      Group.IsNilpotent (H ⧸ H.normalCore.subgroupOf H)

/--
**Permutability with minimal non-nilpotent subgroups does not force a nilpotent core quotient.**
There exist a finite group $G$ and a subgroup $H$ of $G$ with $HM = MH$ (as sets of products) for
every minimal non-nilpotent subgroup $M$ of $G$ such that the quotient $H/H_G$ is not nilpotent,
where the normal core $H_G$ is the largest normal subgroup of $G$ contained in $H$.

This answers Kourovka Problem 17.56 in the negative (Ballester-Bolinches, Esteban-Romero,
Kamornikov and Pérez-Calabuig, 2022).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.56 (V. N. Knyagina, V. S. Monakhov);
resolution: A. Ballester-Bolinches, R. Esteban-Romero, S. F. Kamornikov and V. Pérez-Calabuig, J.
Algebra 608 (2022), 382-387, the Kourovka Notebook (21st issue) marks 17.56 solved (No, not always).
-/
public theorem_wanted permutesMinimalNonNilpotentCoreQuotientNilpotent_refuted :
    ¬ permutesMinimalNonNilpotentCoreQuotientNilpotent

end MathlibExt.GroupTheory.MinimalNonNilpotentPermutableCoreKourovka17Problem56Wanted
