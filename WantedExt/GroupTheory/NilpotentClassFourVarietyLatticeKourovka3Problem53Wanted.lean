/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Distributivity of the lattice of subvarieties of 𝔑₄ (Kourovka Notebook Problem 3.53)

Kourovka Notebook, Archive of Solved Problems, Problem 3.53 (D. M. Smirnov): let `L(𝔑₄)` denote the
lattice of subvarieties of the variety `𝔑₄` of nilpotent groups of class at most `4`. Is `L(𝔑₄)`
distributive?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.53 (D. M.
Smirnov). UnsolvedMath record UM-00700202 (`KOU-3.53`), dataset ulamai/UnsolvedMath v1.8.0.

A subvariety of `𝔑₄` is determined by its laws, a fully invariant subgroup of the free group `F_ω =
FreeGroup ℕ` of countable rank containing `γ₅(F_ω)` (Mathlib's `(⊤ : Subgroup _).lowerCentralSeries
4`), and this correspondence is an order-reversing bijection (H. Neumann, Varieties of Groups,
Chapter 1). Fully invariant subgroups are closed under the subgroup lattice operations `⊓`
(intersection) and `⊔` (product of normal subgroups), so they form a sublattice, dually isomorphic
to `L(𝔑₄)`. Distributivity is self-dual, so the target states it on the fully invariant subgroups:
`U ⊓ (V ⊔ W) = (U ⊓ V) ⊔ (U ⊓ W)`.
-/

/-- `H` is a fully invariant subgroup of `G`: every endomorphism of `G` maps `H` into `H`. -/
def IsFullyInvariant {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ φ : G →* G, H.map φ ≤ H

/-- `H` is the subgroup of laws of a subvariety of `𝔑₄`: a fully invariant subgroup of the free
group `F_ω = FreeGroup ℕ` of countable rank containing `γ₅(F_ω)`, the fifth term of the lower
central series (Mathlib's `lowerCentralSeries` is indexed from `γ₁ = ⊤`). -/
def IsNilpotentClassFourLawSubgroup (H : Subgroup (FreeGroup ℕ)) : Prop :=
  IsFullyInvariant H ∧ (⊤ : Subgroup (FreeGroup ℕ)).lowerCentralSeries 4 ≤ H

/-- Kourovka 3.53 (D. M. Smirnov): the lattice `L(𝔑₄)` of subvarieties of the variety of nilpotent
groups of class at most `4` is distributive. Stated on the dually isomorphic lattice of fully
invariant subgroups of `F_ω` containing `γ₅(F_ω)` (a sublattice of the subgroup lattice), where
distributivity reads `U ⊓ (V ⊔ W) = (U ⊓ V) ⊔ (U ⊓ W)`. -/
def nilpotentClassFourVarietyLatticeDistributive : Prop :=
  ∀ U V W : Subgroup (FreeGroup ℕ), IsNilpotentClassFourLawSubgroup U →
    IsNilpotentClassFourLawSubgroup V → IsNilpotentClassFourLawSubgroup W →
    U ⊓ (V ⊔ W) = (U ⊓ V) ⊔ (U ⊓ W)

/--
Resolved false: Belov shows that the lattice of subvarieties of the variety of nilpotent groups of
class at most `4` is not distributive; the Kourovka Archive answers 3.53 "No". Stated on the dually
isomorphic lattice of fully invariant subgroups of `F_ω` containing `γ₅(F_ω)`. Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.53 (D. M. Smirnov); resolution: Yu.
A. Belov, The lattice of nilpotent varieties of class four groups, Algebra and Logic 9 (1970),
371-374, Kourovka Archive of Solved Problems, Problem 3.53: No, https://doi.org/10.1007/BF02219039.
-/
public theorem_wanted nilpotentClassFourVarietyLatticeDistributive_refuted :
    ¬ nilpotentClassFourVarietyLatticeDistributive

end MathlibExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted
