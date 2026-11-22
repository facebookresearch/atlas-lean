/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Soluble invariant subgroups under coprime automorphism groups (Kourovka Notebook Problem 4.22)

Kourovka Notebook, Archive of Solved Problems, Problem 4.22 (G. Glauberman): (J. G. Thompson) let
`G` be a finite group, `A` a group of automorphisms of `G` such that `|A|` and `|G|` are coprime.
Does there exist an `A`-invariant soluble subgroup `H` of `G` such that `C_A(H) = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.CoprimeActionSolubleInvariantSubgroupKourovka4Problem22Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.22 (G.
Glauberman). UnsolvedMath record UM-00700232 (`KOU-4.22`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is a subgroup of `MulAut G`; `A`-invariant means `α(H) ⊆ H` for `α ∈ A`, and `C_A(H) = 1` means
that only the identity of `A` fixes `H` elementwise.
-/

/-- Kourovka 4.22 (J. G. Thompson; G. Glauberman): if `A` is a group of automorphisms of a finite
group `G` with `|A|` and `|G|` coprime, then `G` has an `A`-invariant soluble subgroup `H` with
`C_A(H) = 1`: only the identity of `A` fixes `H` elementwise. -/
def coprimeActionSolubleInvariantSubgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup (MulAut G)),
    Nat.Coprime (Nat.card A) (Nat.card G) →
    ∃ H : Subgroup G, Group.IsSolvable H ∧ (∀ α ∈ A, ∀ h ∈ H, α h ∈ H) ∧
      ∀ α ∈ A, (∀ h ∈ H, α h = h) → α = 1

/--
Resolved true: Syskin proves that a finite group `G` with a group of automorphisms `A` of coprime
order has an `A`-invariant soluble subgroup `H` with `C_A(H) = 1`; the Kourovka Archive answers 4.22
"Yes, it does". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
4.22 (G. Glauberman); resolution: S. A. Syskin, Automorphisms of finite groups, Siberian Math. J. 32
(1991), no. 6, 1034-1037, Theorem 1 (A. Kondrat'ev's zbMATH review, Zbl 0752.20009); Kourovka
Archive of Solved Problems, Problem 4.22: Yes, it does, https://doi.org/10.1007/BF00971211.
-/
public theorem_wanted coprimeActionSolubleInvariantSubgroup_holds :
    coprimeActionSolubleInvariantSubgroup

end MathlibExt.GroupTheory.CoprimeActionSolubleInvariantSubgroupKourovka4Problem22Wanted
