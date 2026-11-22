/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uncountable groups with the minimum condition (Kourovka Notebook Problem 9.79)

Kourovka Notebook, Archive of Solved Problems, Problem 9.79 (V. P. Shunkov (A. G. Kurosh)): is every
group with the minimum condition countable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Countable.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.MinimumConditionCountableKourovka9Problem79Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.79 (V. P.
Shunkov). UnsolvedMath record UM-00700612 (`KOU-9.79`), dataset ulamai/UnsolvedMath v1.8.0.

The minimum condition is on subgroups. The minimum condition on subgroups is `WellFoundedLT
(Subgroup G)`: every non-empty set of subgroups has a minimal member.
-/

/-- Kourovka 9.79 (V. P. Shunkov, after A. G. Kurosh): every group satisfying the minimum condition
on subgroups (every non-empty set of subgroups has a minimal member) is countable. -/
def minConditionCountable : Prop :=
  ∀ (G : Type) [Group G], WellFoundedLT (Subgroup G) → Countable G

/--
Resolved false: Obraztsov constructs a non-denumerable group satisfying the descending chain
condition on subgroups; the Kourovka Archive answers 9.79 "No". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.79 (V. P. Shunkov); resolution: V.
N. Obraztsov, An imbedding theorem for groups and its corollaries, Math. USSR-Sb. 66 (1990),
541-553, abstract: a nondenumerable group with the descending chain condition for subgroups is
constructed; Kourovka Archive of Solved Problems, Problem 9.79: No,
https://doi.org/10.1070/SM1990v066n02ABEH001184.
-/
public theorem_wanted minConditionCountable_refuted : ¬ minConditionCountable

end MathlibExt.GroupTheory.MinimumConditionCountableKourovka9Problem79Wanted
