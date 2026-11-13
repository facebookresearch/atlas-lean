/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated divisible groups (Kourovka Notebook Problem 1.1)

Kourovka Notebook, Archive of Solved Problems, Problem 1.1 (Yu. A. Bogan): do there exist
non-trivial finitely generated divisible groups? Equivalently, do there exist non-trivial finitely
generated divisible simple groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyGeneratedDivisibleGroupKourovka1Problem1Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.1 (Yu. A.
Bogan). UnsolvedMath record UM-00700001 (`KOU-1.1`), dataset ulamai/UnsolvedMath v1.8.0.

Divisible means that every element has an `n`-th root for every `n ≥ 1` (the equation `xⁿ = g` is
solvable). The target is the simple form, which the problem states as equivalent: it implies the
first form, and conversely a nontrivial finitely generated group has a maximal normal subgroup
(Zorn), whose quotient is simple, finitely generated and again divisible.
-/

/-- `G` is divisible: every element has an `n`-th root for every `n ≥ 1`. -/
def IsDivisibleGroup (G : Type) [Group G] : Prop :=
  ∀ g : G, ∀ n : ℕ, 0 < n → ∃ h : G, h ^ n = g

/-- Kourovka 1.1 (Yu. A. Bogan), in the equivalent form stated in the problem: there is a finitely
generated simple group (in particular a nontrivial one) in which every element has an `n`-th root
for every `n ≥ 1`. -/
def existsFGDivisibleSimpleGroup : Prop :=
  ∃ (G : Type) (_ : Group G), Group.FG G ∧ IsSimpleGroup G ∧ IsDivisibleGroup G

/--
Resolved true: the Kourovka Archive answers 1.1 "Yes, such groups do exist", citing Guba's
nontrivial finitely generated divisible (complete) group; a simple quotient of it by a maximal
normal subgroup is a finitely generated divisible simple group. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.1 (Yu. A. Bogan); resolution: V. S.
Guba, A finitely generated complete group, Math. USSR-Izv. 29 (1987), 233-277, main theorem (a
nontrivial finitely generated group in which every element has roots of all degrees); Kourovka
Archive, Problem 1.1.
-/
public theorem_wanted existsFGDivisibleSimpleGroup_holds : existsFGDivisibleSimpleGroup

end MathlibExt.GroupTheory.FinitelyGeneratedDivisibleGroupKourovka1Problem1Wanted
