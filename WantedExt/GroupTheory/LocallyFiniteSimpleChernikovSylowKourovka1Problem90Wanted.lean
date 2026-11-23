/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally finite simple groups with Chernikov Sylow `2`-subgroups (Kourovka Notebook Problem 1.90)

Kourovka Notebook, Archive of Solved Problems, Problem 1.90 (V. P. Shunkov): a subgroup `H` of `G`
is `2`-infinitely isolated if, whenever the centralizer `C_G(h)` of some `h ≠ 1` in `H` contains an
involution and meets `H` in an infinite subgroup, `C_G(h) ≤ H`. Let `G` be an infinite simple
locally finite group whose Sylow `2`-subgroups are Chernikov groups, with a proper `2`-infinitely
isolated subgroup `H` containing some Sylow `2`-subgroup. Is `G ≅ PSL₂(k)` for a field `k` of odd
characteristic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import WantedExt.GroupTheory.GroupClassesShared

@[expose] public section

namespace MathlibExt.GroupTheory.LocallyFiniteSimpleChernikovSylowKourovka1Problem90Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.90 (V. P.
Shunkov). UnsolvedMath record UM-00700079 (`KOU-1.90`), dataset ulamai/UnsolvedMath v1.8.0.

Sylow `2`-subgroups of an infinite group are its maximal `2`-subgroups; locally finite means that
every finitely generated subgroup is finite. A Chernikov group is `IsChernikov` of
`GroupClassesShared`: a group with an abelian subgroup of finite index satisfying the minimal
condition. `PSL₂(k)` is `SL₂(k) / Z(SL₂(k))`; fields are taken in `Type`, and odd characteristic is
a prime characteristic `p ≠ 2`. The hypothesis does not hold vacuously with `H = 1`: every infinite
simple locally finite group contains involutions (by the existence of Kegel covers and the
Feit-Thompson theorem).
-/

open MathlibExt.GroupTheory.GroupClassesShared (IsChernikov IsLocallyFinite)

/-- `S` is a Sylow `2`-subgroup of `G`: a maximal `2`-subgroup. -/
def IsSylowTwo {G : Type*} [Group G] (S : Subgroup G) : Prop :=
  IsPGroup 2 S ∧ ∀ T : Subgroup G, IsPGroup 2 T → S ≤ T → T = S

/-- `H` is `2`-infinitely isolated in `G` (V. P. Shunkov): whenever the centralizer `C_G(h)` of an
element `h ≠ 1` of `H` contains an involution and meets `H` in an infinite subgroup,
`C_G(h) ≤ H`. -/
def IsTwoInfinitelyIsolated {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∀ h ∈ H, h ≠ 1 → (∃ t ∈ Subgroup.centralizer {h}, orderOf t = 2) →
    ((Subgroup.centralizer {h} ⊓ H : Subgroup G) : Set G).Infinite → Subgroup.centralizer {h} ≤ H

/-- Kourovka 1.90 (V. P. Shunkov): an infinite simple locally finite group whose Sylow `2`-subgroups
are Chernikov groups and which has a proper `2`-infinitely isolated subgroup containing a Sylow
`2`-subgroup is isomorphic to `PSL₂(k) = SL₂(k) / Z(SL₂(k))` for a field `k` of odd
characteristic. -/
def isolatedSubgroupForcesPSLTwo : Prop :=
  ∀ (G : Type) [Group G], Infinite G → IsSimpleGroup G → IsLocallyFinite G →
    (∀ S : Subgroup G, IsSylowTwo S → IsChernikov S) →
    (∃ H : Subgroup G, H ≠ ⊤ ∧ IsTwoInfinitelyIsolated H ∧ ∃ S : Subgroup G, IsSylowTwo S ∧ S ≤ H) →
    ∃ (k : Type) (_ : Field k) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ CharP k p ∧
      Nonempty (G ≃* (Matrix.SpecialLinearGroup (Fin 2) k ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)))

/--
Resolved true: the Kourovka Archive answers "Yes, it does", citing Shunkov (1972): such a group is
isomorphic to `PSL₂(k)` for a field `k` of odd characteristic. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.90 (V. P. Shunkov); resolution: V.
P. Shunkov, Algebra and Logic 11 (1972), 260-272, Kourovka Archive, Problem 1.90 ("Yes, it does").
-/
public theorem_wanted isolatedSubgroupForcesPSLTwo_holds : isolatedSubgroupForcesPSLTwo

end MathlibExt.GroupTheory.LocallyFiniteSimpleChernikovSylowKourovka1Problem90Wanted
