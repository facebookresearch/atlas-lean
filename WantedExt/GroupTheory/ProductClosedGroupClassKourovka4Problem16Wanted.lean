/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Classes of finite groups closed under products of two subgroups (Kourovka Notebook Problem 4.16)

Kourovka Notebook, Archive of Solved Problems, Problem 4.16 (R. Baer): suppose that `𝔎` is a class
of groups meeting the following requirements: 1) subgroups and epimorphic images of `𝔎`-groups are
`𝔎`-groups; 2) if the group `G = UV` is the product of `𝔎`-subgroups `U` and `V` (neither of which
need be normal), then `G ∈ 𝔎`. If `π` is a set of primes, then the class of all finite `π`-groups
meets these requirements. Are these the only classes `𝔎` with these properties?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.ProductClosedGroupClassKourovka4Problem16Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.16 (R. Baer).
UnsolvedMath record UM-00700226 (`KOU-4.16`), dataset ulamai/UnsolvedMath v1.8.0.

A class of groups is a predicate on groups in `Type`; closure under epimorphic images makes it
closed under isomorphism. The class is read as a non-empty class of finite groups, the setting of
Baer's examples: the empty class and the class of all groups also satisfy 1) and 2) and are not
classes of finite `π`-groups, so without these restrictions the question would be trivial. Baer's
classes are classes of finite groups (R. Baer, Classes of finite groups and their properties,
Illinois J. Math. 1 (1957), 115-187), and Syskin's answer concerns classes of finite groups: zbMATH
indexes his paper (Zbl 0423.20014) under finite solvable groups, factorizable groups, class of
finite groups and Kourovka Problem 4.16, and its Lemma 2 (a finite group of order prime to `3` that
is a product of two soluble subgroups is soluble) is quoted in arXiv:2006.00466, proof of Corollary
2.2. A finite `π`-group is a finite group whose order has all prime divisors in `π`.
-/

/-- Kourovka 4.16 (R. Baer): every non-empty class `K` of finite groups that contains the subgroups
and epimorphic images of its members and contains every group `G = UV` that is a product of two
`K`-subgroups `U`, `V` (neither need be normal) is the class of all finite `π`-groups for some set
of primes `π`. -/
def productClosedClassesArePiClasses : Prop :=
  ∀ K : ∀ (G : Type) [Group G], Prop,
    (∃ (G : Type) (_ : Group G), K G) →
    (∀ (G : Type) [Group G], K G → Finite G) →
    (∀ (G : Type) [Group G], K G → ∀ U : Subgroup G, K U) →
    (∀ (G H : Type) [Group G] [Group H] (f : G →* H), Function.Surjective f → K G → K H) →
    (∀ (G : Type) [Group G] (U V : Subgroup G), K U → K V →
      (∀ g : G, ∃ u ∈ U, ∃ v ∈ V, g = u * v) → K G) →
    ∃ π : Set ℕ, ∀ (G : Type) [Group G],
      K G ↔ Finite G ∧ ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p ∈ π

/--
Resolved false: Syskin answers Baer's question in the negative; the Kourovka Archive answers 4.16
"No": not every class with properties 1) and 2) is the class of all finite `π`-groups for some set
of primes `π`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
4.16 (R. Baer); resolution: S. A. Syskin, A question of R. Baer, Siberian Math. J. 20 (1979),
475-476, zbMATH Zbl 0423.20014 (keywords: finite solvable groups, factorizable groups, class of
finite groups, problem 4.16 in Kourovka notebook); Kourovka Archive of Solved Problems, Problem
4.16: No, https://doi.org/10.1007/BF00969961.
-/
public theorem_wanted productClosedClassesArePiClasses_refuted : ¬ productClosedClassesArePiClasses

end MathlibExt.GroupTheory.ProductClosedGroupClassKourovka4Problem16Wanted
