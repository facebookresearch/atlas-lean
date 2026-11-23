/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimal and maximal conditions versus weak chain conditions (Kourovka Notebook Problem 10.14)

Kourovka Notebook, Archive of Solved Problems, Problem 10.14 (D. I. Zaitsev): (a) does every group
satisfying the minimum condition on subgroups satisfy the weak maximum condition on subgroups? (b)
does every group satisfying the maximum condition on subgroups satisfy the weak minimum condition on
subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.WeakChainConditionsKourovka10Problem14Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.14 (D. I.
Zaitsev). UnsolvedMath record UM-00700631 (`KOU-10.14`), dataset ulamai/UnsolvedMath v1.8.0.

The weak maximum (minimum) condition forbids infinite ascending (descending) chains of subgroups in
which each member has infinite index in the next larger one; an infinite index is `relIndex = 0`.
The minimum and maximum conditions are `WellFoundedLT` and `WellFoundedGT` on `Subgroup G`.
-/

/-- **Weak maximal condition on subgroups.** A group $G$ satisfies the weak maximal condition on
subgroups when there is no infinite ascending chain $H_0 \le H_1 \le \cdots$ of subgroups of $G$
in which every index $|H_{i+1} : H_i|$ is infinite. -/
def WeakMaximalCondition (G : Type*) [Group G] : Prop :=
  ¬ ∃ H : ℕ → Subgroup G, ∀ i, H i ≤ H (i + 1) ∧ (H i).relIndex (H (i + 1)) = 0

/-- The weak minimal condition on subgroups: there is no infinite descending chain
`H₀ ≥ H₁ ≥ ⋯` of subgroups with every index `|Hᵢ : Hᵢ₊₁|` infinite. -/
def WeakMinimalCondition (G : Type*) [Group G] : Prop :=
  ¬ ∃ H : ℕ → Subgroup G, ∀ i, H (i + 1) ≤ H i ∧ (H (i + 1)).relIndex (H i) = 0

/-- Kourovka 10.14(a) (D. I. Zaitsev): every group with the minimal condition on subgroups
satisfies the weak maximal condition on subgroups. -/
def minimalImpliesWeakMaximal : Prop :=
  ∀ (G : Type) [Group G], WellFoundedLT (Subgroup G) → WeakMaximalCondition G

/-- Kourovka 10.14(b): every group with the maximal condition on subgroups satisfies the weak
minimal condition on subgroups. -/
def maximalImpliesWeakMinimal : Prop :=
  ∀ (G : Type) [Group G], WellFoundedGT (Subgroup G) → WeakMinimalCondition G

/--
**A group with the minimal condition can fail the weak maximal condition.** There is a group $G$
satisfying the minimal condition on subgroups (there is no infinite strictly descending chain of
subgroups of $G$) that has an infinite ascending chain $H_0 \le H_1 \le \cdots$ of subgroups in
which every index $|H_{i+1} : H_i|$ is infinite. This answers Kourovka Problem 10.14(a) negatively.

The Kourovka Archive answers 10.14(a) "No, not always", citing Obraztsov (1990).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 10.14 (D. I. Zaitsev); resolution: V. N. Obraztsov, Math. USSR-Sb. 66, no. 2
(1990), 541-553 (a); V. N. Obraztsov, Siberian Math. J. 32, no. 1 (1991), 79-84 (b), Kourovka
Archive, Problem 10.14 (both parts "No, not always").
-/
public theorem_wanted minimalImpliesWeakMaximal_refuted : ¬ minimalImpliesWeakMaximal

/--
**A group with the maximal condition can fail the weak minimal condition.** There is a group $G$
satisfying the maximal condition on subgroups (there is no infinite strictly ascending chain of
subgroups of $G$) that has an infinite descending chain $H_0 \ge H_1 \ge \cdots$ of subgroups in
which every index $|H_i : H_{i+1}|$ is infinite. This answers Kourovka Problem 10.14(b) negatively.

The Kourovka Archive answers 10.14(b) "No, not always", citing Obraztsov (1991).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 10.14 (D. I. Zaitsev); resolution: V. N. Obraztsov, Math. USSR-Sb. 66, no.
2 (1990), 541-553 (a); V. N. Obraztsov, Siberian Math. J. 32, no. 1 (1991), 79-84 (b), Kourovka
Archive, Problem 10.14 (both parts "No, not always").
-/
public theorem_wanted maximalImpliesWeakMinimal_refuted : ¬ maximalImpliesWeakMinimal

end MathlibExt.GroupTheory.WeakChainConditionsKourovka10Problem14Wanted
