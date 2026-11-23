/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple groups with min and a quasicyclic subgroup (Kourovka Notebook Problem 9.81)

Kourovka Notebook, Archive of Solved Problems, Problem 9.81 (V. P. Shunkov): does there exist a
simple group with the minimum condition possessing a non-trivial quasi-cyclic subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Simple
public import WantedExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleMinConditionQuasicyclicKourovka9Problem81Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.81 (V. P.
Shunkov). UnsolvedMath record UM-00700614 (`KOU-9.81`), dataset ulamai/UnsolvedMath v1.8.0.

The minimum condition is on subgroups. The minimum condition on subgroups is `WellFoundedLT
(Subgroup G)`: every non-empty set of subgroups has a minimal member. A quasicyclic subgroup is the
image of an injective homomorphism from a quasicyclic group (`IsQuasicyclic` of the 11.116 entry: an
infinite abelian group all of whose proper subgroups are finite, i.e. a Prüfer group `ℤ(p^∞)`); such
a subgroup is non-trivial.
-/

open MathlibExt.GroupTheory.ChernikovSubgroupLatticeDimensionKourovka11Problem116Wanted

/-- Kourovka 9.81 (V. P. Shunkov): there is a simple group with the minimum condition on subgroups
that has a non-trivial quasicyclic subgroup: a quasicyclic group `Q` (`IsQuasicyclic`, from the
11.116 entry) embeds in `G`. -/
def existsSimpleMinQuasicyclic : Prop :=
  ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ WellFoundedLT (Subgroup G) ∧
    ∃ (Q : Type) (_ : Group Q), IsQuasicyclic Q ∧ ∃ f : Q →* G, Function.Injective f

/--
Resolved true: the Kourovka Archive answers 9.81 "Yes, there does", citing Obraztsov's imbedding
theorem for groups and its corollaries on groups with the descending chain condition for subgroups:
some simple group with the minimum condition on subgroups has a non-trivial quasicyclic subgroup.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.81 (V. P.
Shunkov); resolution: V. N. Obraztsov, An imbedding theorem for groups and its corollaries, Math.
USSR-Sb. 66 (1990), 541-553, abstract: an economical imbedding theorem for countable sets of
countable groups without involutions into groups with few subgroups, used to solve problems on
groups with the descending chain condition for subgroups; Kourovka Archive of Solved Problems,
Problem 9.81: Yes, there does, https://doi.org/10.1070/SM1990v066n02ABEH001184.
-/
public theorem_wanted existsSimpleMinQuasicyclic_holds : existsSimpleMinQuasicyclic

end MathlibExt.GroupTheory.SimpleMinConditionQuasicyclicKourovka9Problem81Wanted
