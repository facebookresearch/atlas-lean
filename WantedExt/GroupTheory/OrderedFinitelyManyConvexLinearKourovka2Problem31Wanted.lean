/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ordered groups with finitely many convex subgroups (Kourovka Notebook Problem 2.31)

Kourovka Notebook, Archive of Solved Problems, Problem 2.31 (V. M. Kopytov): can every group
admitting an ordering with only finitely many convex subgroups be represented by matrices over a
field?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.OrderedFinitelyManyConvexLinearKourovka2Problem31Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.31 (V. M.
Kopytov). UnsolvedMath record UM-00700106 (`KOU-2.31`), dataset ulamai/UnsolvedMath v1.8.0.

An ordering of a group is a strict total order invariant under left and right multiplication; a
convex subgroup contains every element lying between two of its elements. "Represented by matrices
over a field" is an injective homomorphism into `GLₙ(K)` for a field `K : Type`.
-/

/-- Kourovka 2.31 (V. M. Kopytov): every group admitting an ordering (a strict total order invariant
under left and right multiplication) with only finitely many convex subgroups has a faithful
finite-dimensional linear representation over a field. -/
def orderableFinitelyManyConvexIsLinear : Prop :=
  ∀ (G : Type) [Group G],
    (∃ r : G → G → Prop, IsStrictTotalOrder G r ∧
      (∀ a b c : G, r b c → r (a * b) (a * c) ∧ r (b * a) (c * a)) ∧
      {H : Subgroup G | ∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ g : G, r h₁ g → r g h₂ → g ∈ H}.Finite) →
    ∃ (K : Type) (_ : Field K) (n : ℕ) (f : G →* GL (Fin n) K), Function.Injective f

/--
Resolved false: the Kourovka Archive answers 2.31 "No, not every" with Churkin's group `⟨aₙ, bₙ (n ∈
ℤ), c, d | [aₙ, bₙ] = c, aₙ^d = aₙ₊₁, bₙ^d = bₙ₊₁, [aₙ, aₘ] = [bₙ, bₘ] = [aₙ, c] = [bₙ, c] = 1⟩`,
which is soluble and orderable with finitely many convex subgroups but not residually finite, hence
not linear over a field. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 2.31 (V. M. Kopytov); resolution: V. A. Churkin (1969), Kourovka Archive, Problem 2.31: No,
not every; the group ⟨aₙ, bₙ (n ∈ ℤ), c, d | [aₙ, bₙ] = c, aₙ^d = aₙ₊₁, bₙ^d = bₙ₊₁, [aₙ, aₘ] = [bₙ,
bₘ] = [aₙ, c] = [bₙ, c] = 1⟩ is soluble and orderable with finitely many convex subgroups but not
residually finite, hence not linear, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted orderableFinitelyManyConvexIsLinear_refuted :
    ¬ orderableFinitelyManyConvexIsLinear

end MathlibExt.GroupTheory.OrderedFinitelyManyConvexLinearKourovka2Problem31Wanted
