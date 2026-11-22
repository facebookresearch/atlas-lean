/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Periodic groups with a self-centralizing abelian normal subgroup (Kourovka Notebook Problem 20.96)

Kourovka Notebook, Problem 20.96 (A. I. Sozutov), marked solved in the 21st issue: is a periodic
group a Frobenius group if it has a proper non-trivial normal abelian subgroup that contains the
centralizer of each of its non-identity elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Torsion
public import WantedExt.GroupTheory.FrobeniusGroupShared

@[expose] public section

namespace MathlibExt.GroupTheory.PeriodicSelfCentralizingAbelianFrobeniusKourovka20Problem96Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.96 (A. I. Sozutov). UnsolvedMath record
UM-00701754 (`KOU-20.96`), dataset ulamai/UnsolvedMath v1.8.0.

Frobenius groups are those of Kourovka Problem 6.53 (`IsFrobeniusGroup F H` of
`FrobeniusGroupShared` for some kernel `F` and complement `H`), the definition that Sozutov's
neighbouring Problem 20.95 cites: `G = F ⋊ H` with `H ∩ H^g = 1` for every `g ∉ H` and
`F \ {1} = G \ ⋃_g H^g`. Kernel and complement are required to be non-trivial (with `H = 1` or
`F = 1` every group would qualify). Periodic is `IsMulTorsion G`.
-/

open MathlibExt.GroupTheory.FrobeniusGroupShared (IsFrobeniusGroup)

/-- **Kourovka Problem 20.96 (periodic Frobenius groups).** The statement, posed by A. I. Sozutov,
that for every group $G$ in which every element has finite order and every normal abelian subgroup
$A$ of $G$ that is neither trivial nor all of $G$ and such that for every $a \in A$ with $a \ne 1$
the centralizer $C_G(a)$ of $a$ in $G$ is contained in $A$, there are subgroups $F$ and $H$ of $G$
such that $G$ is a Frobenius group with kernel $F$ and complement $H$. -/
def periodicSelfCentralizingAbelianNormalFrobenius : Prop :=
  ∀ (G : Type) [Group G], IsMulTorsion G → ∀ A : Subgroup G, A.Normal → A ≠ ⊥ → A ≠ ⊤ →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ a ∈ A, a ≠ 1 → Subgroup.centralizer {a} ≤ A) →
    ∃ F H : Subgroup G, IsFrobeniusGroup F H

/-- Deprecated: this entry's earlier local Frobenius-group predicate (Kourovka Problem 6.53:
`G = F ⋊ H` with `H ∩ H^g = 1` for every `g ∉ H` and `F \ {1} = G \ ⋃_g H^g`, kernel and
complement non-trivial), kept with its original body. The statement above now uses
`∃ F H, FrobeniusGroupShared.IsFrobeniusGroup F H`, which is equivalent to it on every group. -/
@[deprecated "Use `∃ F H, FrobeniusGroupShared.IsFrobeniusGroup F H` instead."
  (since := "2026-10-23")]
def IsFrobeniusGroup (G : Type) [Group G] : Prop :=
  ∃ F H : Subgroup G, F.Normal ∧ F ≠ ⊥ ∧ H ≠ ⊥ ∧ F ⊓ H = ⊥ ∧ F ⊔ H = ⊤ ∧
    (∀ g : G, g ∉ H → ∀ x ∈ H, g⁻¹ * x * g ∈ H → x = 1) ∧
    ∀ x : G, x ≠ 1 → (x ∈ F ↔ ∀ g : G, g⁻¹ * x * g ∉ H)

/--
**Lytkina–Mazurov theorem on periodic Frobenius groups.** Let $G$ be a group in which every element
has finite order, and let $A$ be a normal abelian subgroup of $G$ that is neither trivial nor all of
$G$ and such that for every $a \in A$ with $a \ne 1$ the centralizer $C_G(a)$ of $a$ in $G$ is
contained in $A$. Then there are subgroups $F$ and $H$ of $G$ such that $G$ is a Frobenius group
with kernel $F$ and complement $H$. This answers Kourovka Problem 20.96 (A. I. Sozutov) in the
affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.96 (A. I. Sozutov);
resolution: D. V. Lytkina and V. D. Mazurov, Periodic Frobenius groups, Siberian Math. J. 64 (2023),
no. 6, 1351-1355 (Sibirsk. Mat. Zh. 64 (2023), no. 6, 1224-1228), abstract: conditions for a
strongly isolated normal subgroup of a periodic group to have a complement; Kourovka Notebook (21st
issue), Problem 20.96: Yes, it is, https://www.mathnet.ru/eng/smj7826.
-/
public theorem_wanted periodicSelfCentralizingAbelianNormalFrobenius_holds :
    periodicSelfCentralizingAbelianNormalFrobenius

end MathlibExt.GroupTheory.PeriodicSelfCentralizingAbelianFrobeniusKourovka20Problem96Wanted
