/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quasi-nilpotent and Γ-quasi-nilpotent finite groups (Kourovka Notebook Problem 2.3)

Kourovka Notebook, Archive of Solved Problems, Problem 2.3 (Ya. G. Berkovich, M. I. Kravchuk): a
finite group is quasi-nilpotent (`Γ`-quasi-nilpotent) if any two of its (maximal) subgroups `A` and
`B` satisfy `A ≤ B`, or `B ≤ A`, or `N_A(A ∩ B) ≠ A ∩ B ≠ N_B(A ∩ B)`. Do the classes of
quasi-nilpotent and `Γ`-quasi-nilpotent groups coincide?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.Atoms

@[expose] public section

namespace MathlibExt.GroupTheory.QuasiNilpotentMaximalSubgroupsKourovka2Problem3Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.3 (Ya. G.
Berkovich, M. I. Kravchuk). UnsolvedMath record UM-00700082 (`KOU-2.3`), dataset ulamai/UnsolvedMath
v1.8.0.

This is the Berkovich-Kravchuk notion, not the quasinilpotent groups of the generalized Fitting
subgroup. `N_A(X) = N_G(X) ∩ A` and maximal subgroups are coatoms. "The classes coincide" is stated
as an equivalence for every finite group in `Type`. The refutation is one explicit group of order
96, whose verification is an argument about its subgroups, not a decision procedure on a small
object.
-/

/-- Subgroups `A`, `B` of `G` satisfy the Berkovich–Kravchuk condition: `A ≤ B`, or `B ≤ A`, or
`N_A(A ∩ B) ≠ A ∩ B ≠ N_B(A ∩ B)`, where `N_A(X) = N_G(X) ∩ A`. -/
def BerkovichKravchukCondition {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  A ≤ B ∨ B ≤ A ∨ (Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) ⊓ A ≠ A ⊓ B ∧
    Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) ⊓ B ≠ A ⊓ B)

/-- Kourovka 2.3 (Ya. G. Berkovich, M. I. Kravchuk): the classes of quasi-nilpotent finite groups
(any two subgroups satisfy the condition) and `Γ`-quasi-nilpotent finite groups (any two maximal
subgroups satisfy it) coincide. -/
def quasiNilpotentIffGammaQuasiNilpotent : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ A B : Subgroup G, BerkovichKravchukCondition A B) ↔
      ∀ A B : Subgroup G, IsCoatom A → IsCoatom B → BerkovichKravchukCondition A B

/--
Resolved false: the Kourovka Archive answers 2.3 "No" with Mazurov's group `⟨x, y, z, t | x⁴ = y⁴ =
z² = t³ = 1, [x, y] = z, [x, z] = [y, z] = 1, x^t = y, y^t = x⁻¹y⁻¹⟩`: any two maximal subgroups
meet in `Φ(G)` (as `G / Φ(G) ≅ A₄`), so `G` is `Γ`-quasi-nilpotent, while `A₁ = ⟨zx², zy², t⟩` and
`B₁ = ⟨z, t⟩` violate the condition. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 2.3 (Ya. G. Berkovich, M. I. Kravchuk); resolution: V. D. Mazurov (1973),
Kourovka Archive, Problem 2.3: No; G = ⟨x, y, z, t | x⁴ = y⁴ = z² = t³ = 1, [x, y] = z, [x, z] = [y,
z] = 1, x^t = y, y^t = x⁻¹y⁻¹⟩ with G / Φ(G) ≅ A₄ is Γ-quasi-nilpotent but not quasi-nilpotent,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted quasiNilpotentIffGammaQuasiNilpotent_refuted :
    ¬ quasiNilpotentIffGammaQuasiNilpotent

end MathlibExt.GroupTheory.QuasiNilpotentMaximalSubgroupsKourovka2Problem3Wanted
