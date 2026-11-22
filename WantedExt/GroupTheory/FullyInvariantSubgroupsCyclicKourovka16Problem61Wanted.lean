/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite groups with fully invariant subgroups of every order (Kourovka Notebook Problem 16.61)

Kourovka Notebook, Archive of Solved Problems, Problem 16.61 (D. MacHale): a subgroup `H` of a group
`G` is fully invariant if `θ(H) ≤ H` for every endomorphism `θ` of `G`. Let `G` be a finite group
such that `G` has a fully invariant subgroup of order `d` for every `d` dividing `|G|`. Must `G` be
cyclic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.FullyInvariantSubgroupsCyclicKourovka16Problem61Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.61 (D.
MacHale). UnsolvedMath record UM-00701253 (`KOU-16.61`), dataset ulamai/UnsolvedMath v1.8.0.

Endomorphisms are all homomorphisms `G →* G`, and orders are `Nat.card`.
-/

/-- Kourovka 16.61 (D. MacHale): a finite group with a fully invariant subgroup (one mapped into
itself by every endomorphism) of order `d` for every divisor `d` of `|G|` is cyclic. -/
def fullyInvariantSubgroupsOfEachOrderCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ d : ℕ, d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d ∧ ∀ φ : G →* G, H.map φ ≤ H) →
    IsCyclic G

/--
Resolved false: the Kourovka Archive answers 16.61 "No" (Abdollahi): take `G = C_p × C_{p²}`, where
`C_p` and `C_{p²}` are cyclic `p`-groups of orders `p` and `p²`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.61 (D. MacHale); resolution: A.
Abdollahi, letter of 4 March 2009, as recorded in the Kourovka Archive, Kourovka Archive, Problem
16.61 (No: G = C_p × C_{p²}).
-/
public theorem_wanted fullyInvariantSubgroupsOfEachOrderCyclic_refuted :
    ¬ fullyInvariantSubgroupsOfEachOrderCyclic

end MathlibExt.GroupTheory.FullyInvariantSubgroupsCyclicKourovka16Problem61Wanted
