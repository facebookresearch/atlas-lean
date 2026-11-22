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

/-- **Classes of groups.** A class of groups is a predicate on groups: it assigns to every group
$G$ (in the lowest universe of types) a proposition, read as "$G$ belongs to the class". No
closure under isomorphism is required. -/
abbrev GroupClass : Type 1 := ∀ (G : Type) [Group G], Prop

/-- **Formations of finite groups.** A class $\mathfrak F$ of groups is a formation when every group
in $\mathfrak F$ is finite, $\mathfrak F$ contains at least one group, $\mathfrak F$ is closed under
isomorphism, $\mathfrak F$ is closed under quotients (if $G \in \mathfrak F$ and $N$ is a normal
subgroup of $G$, then $G/N \in \mathfrak F$), and $\mathfrak F$ is closed under subdirect products:
if $G$ is a finite group with normal subgroups $M$ and $N$ such that $G/M \in \mathfrak F$ and
$G/N \in \mathfrak F$, then $G/(M \cap N) \in \mathfrak F$. -/
structure IsFormation (F : GroupClass) : Prop where
  finite : ∀ (G : Type) [Group G], F G → Finite G
  nonempty : ∃ (G : Type) (_ : Group G), F G
  of_mulEquiv : ∀ (G H : Type) [Group G] [Group H], (G ≃* H) → F G → F H
  quotient : ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], F G → F (G ⧸ N)
  subdirect : ∀ (G : Type) [Group G] [Finite G] (M N : Subgroup G) [M.Normal] [N.Normal],
    F (G ⧸ M) → F (G ⧸ N) → F (G ⧸ (M ⊓ N))

/-- **Groups satisfying a set of laws.** Let $W$ be a set of words in the free group on countably
many generators $x_0, x_1, x_2, \dots$. A group $G$ satisfies the laws in $W$ when every
homomorphism from this free group to $G$ sends every $w \in W$ to $1$. The groups satisfying $W$
form the variety defined by $W$, and every variety arises this way. -/
def SatisfiesLaws (W : Set (FreeGroup ℕ)) (G : Type) [Group G] : Prop :=
  ∀ w ∈ W, ∀ f : FreeGroup ℕ →* G, f w = 1

/-- **Kourovka Problem 11.21 (Vasil'yev's question on formations of $p$-groups).** The proposition
that for every prime $p$ and every formation $\mathfrak F$ all of whose members are $p$-groups (a
subformation of the formation $\mathfrak N_p$ of all finite $p$-groups), there is a set $W$ of laws,
words in the free group on countably many generators, such that a finite $p$-group lies in
$\mathfrak F$ if and only if it satisfies every law in $W$. In other words, every such
$\mathfrak F$ equals $\mathfrak N_p \cap \mathfrak M$ for the variety $\mathfrak M$ defined by
$W$. -/
def subformationOfPGroupsIsVarietal : Prop :=
  ∀ p : ℕ, p.Prime → ∀ F : GroupClass, IsFormation F →
    (∀ (G : Type) [Group G], F G → IsPGroup p G) →
    ∃ W : Set (FreeGroup ℕ), ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
      (F G ↔ SatisfiesLaws W G)

/--
**Kourovka Problem 11.21 has a negative answer.** There are a prime $p$ and a formation
$\mathfrak F$ all of whose members are $p$-groups such that for every set $W$ of laws, words in the
free group on countably many generators, some finite $p$-group lies in $\mathfrak F$ and fails a
law in $W$, or satisfies every law in $W$ and does not lie in $\mathfrak F$. Thus $\mathfrak F$ is
not of the form $\mathfrak N_p \cap \mathfrak M$ for any variety $\mathfrak M$, where
$\mathfrak N_p$ is the formation of all finite $p$-groups.

The Kourovka Archive answers 11.21 "No, it is not true" (A. N. Krasil'nikov): formations of finite
$p$-groups correspond bijectively to varieties of pro-$p$ groups, there are continuously many
varieties of nilpotent pro-$p$ groups of class at most $6$ (Zubkov), hence continuously many
formations of finite $p$-groups of class at most $6$, while such a formation of the form
$\mathfrak N_p \cap \mathfrak M$ equals $\mathfrak N_p \cap (\mathfrak M \cap \mathfrak N_6)$, where
$\mathfrak N_6$ is the variety of nilpotent groups of class at most $6$, and there are only
countably many varieties of nilpotent groups of class at most $6$ (all finitely based).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
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
