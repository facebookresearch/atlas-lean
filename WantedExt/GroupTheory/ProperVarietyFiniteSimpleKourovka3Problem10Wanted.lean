/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite simple groups in a proper variety (Kourovka Notebook Problem 3.10)

Kourovka Notebook, Archive of Solved Problems, Problem 3.10 (Yu. M. Gorchakov): need the number of
finite non-abelian simple groups contained in a proper variety of groups be finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.ProperVarietyFiniteSimpleKourovka3Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.10 (Yu. M.
Gorchakov). UnsolvedMath record UM-00700164 (`KOU-3.10`), dataset ulamai/UnsolvedMath v1.8.0.

A proper variety satisfies some non-trivial law `w = 1`, `w ∈ FreeGroup (Fin n)`, and is contained
in the variety of that law, which is itself proper; so the statement is made for the variety of a
single non-trivial law. "Finitely many" (up to isomorphism) is a bound on the orders.
-/

/-- Kourovka 3.10 (Yu. M. Gorchakov): a proper variety of groups contains only finitely many
finite nonabelian simple groups. A proper variety satisfies some non-trivial law `w = 1`; stated
for the variety of that law, as a bound on the orders of the finite nonabelian simple groups
satisfying `w = 1` identically. -/
def properVarietyFinitelyManyFiniteSimple : Prop :=
  ∀ (n : ℕ) (w : FreeGroup (Fin n)), w ≠ 1 → ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G],
    IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → (∀ φ : FreeGroup (Fin n) →* G, φ w = 1) →
      Nat.card G ≤ N

/--
Resolved true: the Kourovka Archive answers 3.10 "Yes, mod CFSG", citing Jones (J. Austral. Math.
Soc. 17 (1974)): a proper variety contains only finitely many finite non-abelian simple groups.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.10 (Yu. M.
Gorchakov); resolution: G. A. Jones, J. Austral. Math. Soc. 17 (1974), 162-173, Kourovka Archive,
Problem 3.10: Yes, mod CFSG, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted properVarietyFinitelyManyFiniteSimple_holds :
    properVarietyFinitelyManyFiniteSimple

end MathlibExt.GroupTheory.ProperVarietyFiniteSimpleKourovka3Problem10Wanted
