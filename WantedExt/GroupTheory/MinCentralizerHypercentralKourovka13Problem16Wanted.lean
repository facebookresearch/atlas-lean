/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimal condition on centralizers and hypercentrality (Kourovka Notebook Problem 13.16)

Kourovka Notebook, Archive of Solved Problems, Problem 13.16 (F. O. Wagner): is every locally
nilpotent group with the minimal condition on centralizers hypercentral?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.MinCentralizerHypercentralKourovka13Problem16Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.16 (F. O.
Wagner). UnsolvedMath record UM-00700934 (`KOU-13.16`), dataset ulamai/UnsolvedMath v1.8.0.

Locally nilpotent means that finitely generated subgroups are nilpotent. The minimal condition on
centralizers is the descending chain condition on the subgroups `C_G(X)`, `X ⊆ G`. Hypercentral is
stated through its standard equivalent form: every proper quotient `G ⧸ N` has nontrivial centre
(equivalently, the transfinite upper central series reaches `G`).
-/

/-- `G` is locally nilpotent: every finitely generated subgroup is nilpotent. -/
def IsLocallyNilpotent (G : Type*) [Group G] : Prop :=
  ∀ S : Set G, S.Finite → Group.IsNilpotent (Subgroup.closure S)

/-- `G` satisfies the minimal condition on centralizers: there is no infinite strictly descending
chain of centralizers `C_G(X)`. -/
def HasMinCentralizers (G : Type*) [Group G] : Prop :=
  WellFounded fun H K : {H : Subgroup G // ∃ X : Set G, H = Subgroup.centralizer X} => H.1 < K.1

/-- `G` is hypercentral: every nontrivial quotient `G ⧸ N` has nontrivial centre, i.e. some
`g ∉ N` commutes with all of `G` modulo `N` (equivalently, the transfinite upper central series
reaches `G`). -/
def IsHypercentral (G : Type*) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → N ≠ ⊤ → ∃ g : G, g ∉ N ∧ ∀ h : G, g * h * g⁻¹ * h⁻¹ ∈ N

/-- Kourovka 13.16 (F. O. Wagner): every locally nilpotent group with the minimal condition on
centralizers is hypercentral. -/
def locallyNilpotentMinCentralizersHypercentral : Prop :=
  ∀ (G : Type) [Group G], IsLocallyNilpotent G → HasMinCentralizers G → IsHypercentral G

/--
Resolved true: the Kourovka Archive answers 13.16 "Yes, it is" (V. V. Bludov, 1998). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.16 (F. O. Wagner);
resolution: V. V. Bludov, Algebra and Logic 37 (1998), no. 3, 151-156, Kourovka Archive, Problem
13.16: Yes, it is.
-/
public theorem_wanted locallyNilpotentMinCentralizersHypercentral_holds :
    locallyNilpotentMinCentralizersHypercentral

end MathlibExt.GroupTheory.MinCentralizerHypercentralKourovka13Problem16Wanted
