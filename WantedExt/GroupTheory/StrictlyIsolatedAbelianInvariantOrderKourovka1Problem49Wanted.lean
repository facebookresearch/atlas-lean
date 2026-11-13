/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Invariant orders on abelian strictly isolated normal subgroups (Kourovka Notebook Problem 1.49)

Kourovka Notebook, Archive of Solved Problems, Problem 1.49 (A. I. Kokorin): is it possible to order
an abelian strictly isolated normal subgroup of an `S`-group (see Archive 1.47) in such a way that
the order is preserved under the action of the inner automorphisms of the whole group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice

@[expose] public section

namespace MathlibExt.GroupTheory.StrictlyIsolatedAbelianInvariantOrderKourovka1Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.49 (A. I.
Kokorin). UnsolvedMath record UM-00700044 (`KOU-1.49`), dataset ulamai/UnsolvedMath v1.8.0.

Strictly isolated subgroups and `S`-groups are as defined in Archive 1.47. An order of the abelian
subgroup `A` compatible with its multiplication is given by its positive cone `P ⊆ A` (closed under
multiplication, `P ∩ P⁻¹ = 1`, `A = P ∪ P⁻¹`); it is preserved by the inner automorphisms of `G`
when `g P g⁻¹ ⊆ P` for every `g ∈ G`.
-/

/-- The subgroup `H` is strictly isolated: whenever `x · g₁⁻¹xg₁ ⋯ gₙ⁻¹xgₙ ∈ H`, both `x` and every
`gᵢ⁻¹xgᵢ` lie in `H`. -/
def IsStrictlyIsolated {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ (x : G) (gs : List G), x * (gs.map fun g => g⁻¹ * x * g).prod ∈ H →
    x ∈ H ∧ ∀ g ∈ gs, g⁻¹ * x * g ∈ H

/-- `G` is an `S`-group: the identity subgroup is strictly isolated. -/
def IsSGroup (G : Type) [Group G] : Prop :=
  IsStrictlyIsolated (⊥ : Subgroup G)

/-- The abelian subgroup `A` has a linear order compatible with its multiplication and preserved by
conjugation by every element of `G`, given by its positive cone `P` (`a ≤ b` iff `b * a⁻¹ ∈ P`). -/
def HasConjugationInvariantOrder {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∃ P : Set G, P ⊆ A ∧ (∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) ∧ (∀ a ∈ P, a⁻¹ ∈ P → a = 1) ∧
    (∀ a ∈ A, a ∈ P ∨ a⁻¹ ∈ P) ∧ ∀ g : G, ∀ a ∈ P, g * a * g⁻¹ ∈ P

/-- Kourovka 1.49 (A. I. Kokorin): every abelian strictly isolated normal subgroup of an `S`-group
can be ordered so that the order is preserved by all inner automorphisms of the whole group. -/
def strictlyIsolatedAbelianNormalHasInvariantOrder : Prop :=
  ∀ (G : Type) [Group G] (A : Subgroup G), IsSGroup G → A.Normal →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → IsStrictlyIsolated A → HasConjugationInvariantOrder A

/--
Resolved false: the Kourovka Archive answers 1.49 "Not always", citing Bludov (1972). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.49 (A. I. Kokorin);
resolution: V. V. Bludov, Algebra and Logic 11 (1972), 341-349, Kourovka Archive, Problem 1.49 (Not
always).
-/
public theorem_wanted strictlyIsolatedAbelianNormalHasInvariantOrder_refuted :
    ¬ strictlyIsolatedAbelianNormalHasInvariantOrder

end MathlibExt.GroupTheory.StrictlyIsolatedAbelianInvariantOrderKourovka1Problem49Wanted
