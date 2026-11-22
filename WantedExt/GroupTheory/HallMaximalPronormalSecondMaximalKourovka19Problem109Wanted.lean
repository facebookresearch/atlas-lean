/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hall maximal subgroups and pronormal second maximal subgroups (Kourovka Notebook Problem 19.109)

Kourovka Notebook, Archive of Solved Problems, Problem 19.109 (V. I. Zenkov): a subgroup `H` of a
finite group `G` is pronormal if for any `g ∈ G` the subgroups `H` and `H^g` are conjugate by an
element of `⟨H, H^g⟩`; a maximal subgroup of a maximal subgroup is second maximal. Is it true that
in a non-abelian finite simple group `G` all maximal subgroups are Hall subgroups if and only if
every second maximal subgroup of `G` is pronormal in `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.HallMaximalPronormalSecondMaximalKourovka19Problem109Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.109 (V. I.
Zenkov). UnsolvedMath record UM-00701657 (`KOU-19.109`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal subgroups are coatoms; Hall means `|M|` coprime to `|G : M|`; a second maximal subgroup is
`K < M` with `M` maximal and no subgroup strictly between.
-/

/-- `H` is a Hall subgroup: `|H|` is coprime to `|G : H|`. -/
def IsHallSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  (Nat.card H).Coprime H.index

/-- `H` is pronormal in `G`: for every `g ∈ G`, the subgroups `H` and `H^g` are conjugate by an
element of `⟨H, H^g⟩`. -/
def IsPronormal {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ g : G, ∃ x ∈ H ⊔ H.map (MulAut.conj g).toMonoidHom,
    H.map (MulAut.conj x).toMonoidHom = H.map (MulAut.conj g).toMonoidHom

/-- `K` is a second maximal subgroup: a maximal subgroup of a maximal subgroup of `G`. -/
def IsSecondMaximal {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∃ M : Subgroup G, IsCoatom M ∧ K < M ∧ ∀ L : Subgroup G, K < L → ¬ L < M

/-- Kourovka 19.109 (V. I. Zenkov): in a non-abelian finite simple group `G`, all maximal subgroups
are Hall subgroups if and only if every second maximal subgroup of `G` is pronormal in `G`. -/
def maximalHallIffSecondMaximalPronormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ((∀ M : Subgroup G, IsCoatom M → IsHallSubgroup M) ↔
      ∀ K : Subgroup G, IsSecondMaximal K → IsPronormal K)

/--
Resolved false: the Kourovka Archive answers 19.109 "No, not always": `SL₂(2¹¹)`, in which every
second maximal subgroup is pronormal (V. N. Tyutyanov, 2018), is a counterexample. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.109 (V. I. Zenkov);
resolution: V. N. Tyutyanov, letter of 23 November 2018, as recorded in the Kourovka Archive,
Kourovka Archive, Problem 19.109: No, not always; in SL_2(2^11) every second maximal subgroup is
pronormal, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted maximalHallIffSecondMaximalPronormal_refuted :
    ¬ maximalHallIffSecondMaximalPronormal

end MathlibExt.GroupTheory.HallMaximalPronormalSecondMaximalKourovka19Problem109Wanted
