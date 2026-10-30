/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Formations of finite p-groups cut out by varieties (Kourovka Notebook Problem 11.21)

Kourovka Notebook, Archive of Solved Problems, Problem 11.21 (A. F. Vasil'yev): let `𝔑_p` be the
formation of all finite `p`-groups. Is every subformation `𝔉` of `𝔑_p` of the form `𝔑_p ∩ 𝔐` for a
variety `𝔐`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.21 (A. F.
Vasil'yev). UnsolvedMath record UM-00700714 (`KOU-11.21`), dataset ulamai/UnsolvedMath v1.8.0.

A class of groups is a predicate on groups in `Type`. A formation is a nonempty, isomorphism-closed
class of finite groups closed under quotients and subdirect products (`G / M, G / N ∈ 𝔉` implies `G
/ (M ∩ N) ∈ 𝔉`); nonemptiness excludes the empty class, which no variety cuts out (every variety
contains the trivial `p`-group). A variety is the class of groups satisfying a set `W` of laws,
words in the free group on countably many letters. `𝔉 = 𝔑_p ∩ 𝔐` means that a finite `p`-group lies
in `𝔉` iff it satisfies `W`. The prime `p` is universally quantified, so the refutation asserts a
counterexample for some prime.
-/

/-- A class of groups: a predicate on groups in `Type`. -/
abbrev GroupClass : Type 1 := ∀ (G : Type) [Group G], Prop

/-- `F` is a formation of finite groups: a nonempty, isomorphism-closed class of finite groups
closed under homomorphic images and under subdirect products (if `G / M` and `G / N` lie in `F`,
then so does `G / (M ⊓ N)`). -/
structure IsFormation (F : GroupClass) : Prop where
  finite : ∀ (G : Type) [Group G], F G → Finite G
  nonempty : ∃ (G : Type) (_ : Group G), F G
  of_mulEquiv : ∀ (G H : Type) [Group G] [Group H], (G ≃* H) → F G → F H
  quotient : ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], F G → F (G ⧸ N)
  subdirect : ∀ (G : Type) [Group G] [Finite G] (M N : Subgroup G) [M.Normal] [N.Normal],
    F (G ⧸ M) → F (G ⧸ N) → F (G ⧸ (M ⊓ N))

/-- `G` satisfies every law in `W`: each `w ∈ W`, a word in the free group on countably many
letters, maps to `1` under every homomorphism to `G`. The groups satisfying `W` form the variety
defined by `W`, and every variety arises this way. -/
def SatisfiesLaws (W : Set (FreeGroup ℕ)) (G : Type) [Group G] : Prop :=
  ∀ w ∈ W, ∀ f : FreeGroup ℕ →* G, f w = 1

/-- Kourovka 11.21 (A. F. Vasil'yev): for every prime `p`, every subformation `F` of the formation
`𝔑_p` of all finite `p`-groups has the form `𝔑_p ∩ 𝔐` for a variety `𝔐`: some set of laws `W`
holds in a finite `p`-group exactly when the group lies in `F`. -/
def subformationOfPGroupsIsVarietal : Prop :=
  ∀ p : ℕ, p.Prime → ∀ F : GroupClass, IsFormation F →
    (∀ (G : Type) [Group G], F G → IsPGroup p G) →
    ∃ W : Set (FreeGroup ℕ), ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
      (F G ↔ SatisfiesLaws W G)

/--
Resolved false: the Kourovka Archive answers 11.21 "No, it is not true" (A. N. Krasil'nikov):
formations of finite `p`-groups correspond bijectively to varieties of pro-`p` groups, there are
continuously many varieties of nilpotent pro-`p` groups of class at most 6 (Zubkov), hence
continuously many formations of finite `p`-groups of class at most 6, while a formation `𝔑_p ∩ 𝔐` of
such groups equals `𝔑_p ∩ (𝔐 ∩ 𝔑_6)` and there are only countably many varieties of nilpotent groups
of class at most 6 (all finitely based). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 11.21 (A. F. Vasil'yev); resolution: A. N. Krasil'nikov, letter of 17 July
1998, using A. N. Zubkov, Siberian Math. J. 29, no. 3 (1988), 491-494, Kourovka Archive, Problem
11.21: "No, it is not true"; formations of finite `p`-groups correspond to varieties of pro-`p`
groups, there are continuously many varieties of nilpotent pro-`p` groups of class at most 6
(Zubkov) but only countably many varieties of nilpotent groups of class at most 6,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted subformationOfPGroupsIsVarietal_refuted : ¬ subformationOfPGroupsIsVarietal

end MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted
