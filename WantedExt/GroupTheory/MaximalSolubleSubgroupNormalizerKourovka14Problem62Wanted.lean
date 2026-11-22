/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximal soluble subgroups and the Frattini argument (Kourovka Notebook Problem 14.62)

Kourovka Notebook, Archive of Solved Problems, Problem 14.62 (V. S. Monakhov): if `H` is a
non-soluble normal subgroup of a finite group `G`, is there always a maximal soluble subgroup `S` of
`H` with `G = H N_G(S)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalSolubleSubgroupNormalizerKourovka14Problem62Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.62 (V. S.
Monakhov). UnsolvedMath record UM-00701047 (`KOU-14.62`), dataset ulamai/UnsolvedMath v1.8.0.

A maximal soluble subgroup of `H` is a soluble subgroup `S ≤ H` not properly contained in a soluble
subgroup of `H`. Since `H` is normal, `H N_G(S)` is the subgroup `H ⊔ N_G(S)`.
-/

/-- Kourovka 14.62 (V. S. Monakhov): if `H` is a non-soluble normal subgroup of a finite group `G`,
then some maximal soluble subgroup `S` of `H` satisfies `G = H N_G(S)`. -/
def maximalSolubleSubgroupNormalizerSupplement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), H.Normal → ¬ Group.IsSolvable H →
    ∃ S : Subgroup G, S ≤ H ∧ Group.IsSolvable S ∧
      (∀ T : Subgroup G, S ≤ T → T ≤ H → Group.IsSolvable T → T = S) ∧
      H ⊔ Subgroup.normalizer (S : Set G) = ⊤

/--
Resolved true: the Kourovka Archive answers 14.62 "Yes, it always exists" modulo the classification
of finite simple groups, citing Zenkov, Monakhov and Revin. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 14.62 (V. S. Monakhov); resolution: V. I. Zenkov, V. S.
Monakhov and D. O. Revin, Algebra and Logic 43 (2004), no. 2, 102-108 (using the classification of
finite simple groups), Kourovka Archive, Problem 14.62 (answer: Yes, it always exists mod CFSG).
-/
public theorem_wanted maximalSolubleSubgroupNormalizerSupplement_holds :
    maximalSolubleSubgroupNormalizerSupplement

end MathlibExt.GroupTheory.MaximalSolubleSubgroupNormalizerKourovka14Problem62Wanted
