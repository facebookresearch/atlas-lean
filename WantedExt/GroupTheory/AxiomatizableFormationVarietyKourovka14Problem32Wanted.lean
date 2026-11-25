/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Axiomatizable formations of groups that are not varieties (Kourovka Notebook Problem 14.32)

Kourovka Notebook, Archive of Solved Problems, Problem 14.32 (A. M. Gaglione, D. Spellman): define a
formation of (not necessarily finite) groups as a nonempty class closed under homomorphic images and
subdirect products with finitely many factors. Must every first-order axiomatizable formation of
groups be a variety?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.GroupTheory.AxiomatizableFormationVarietyKourovka14Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.32 (A. M.
Gaglione, D. Spellman). UnsolvedMath record UM-00701017 (`KOU-14.32`), dataset ulamai/UnsolvedMath
v1.8.0.

Classes of groups are predicates on groups in `Type`. Subdirect products of finitely many factors
are expressed by `G / N₁, G / N₂ ∈ 𝔉 → G / (N₁ ∩ N₂) ∈ 𝔉`, which together with homomorphic images
gives all of them. Axiomatizable means "the groups in the class are the models of a first-order
theory in the language of groups" (`MathlibExt`'s `groupLanguage`); a variety is the class of groups
satisfying a set of laws.
-/

open FirstOrder FirstOrder.Language

/-- A class of groups, as a predicate on groups in `Type`. -/
abbrev GroupClass : Type 1 := ∀ (G : Type) [Group G], Prop

/-- **Formations of groups in the sense of Gaglione and Spellman.** A class $\mathfrak{F}$ of
groups is a formation when it contains at least one group, it is closed under surjective
homomorphic images (if $G \in \mathfrak{F}$ and $\varphi \colon G \to H$ is a surjective
homomorphism, then $H \in \mathfrak{F}$), and for every group $G$ and all normal subgroups $N_1$,
$N_2$ of $G$, if $G/N_1$ and $G/N_2$ lie in $\mathfrak{F}$, then so does $G/(N_1 \cap N_2)$.

Together with closure under homomorphic images, the last condition amounts to closure under
subdirect products of finitely many factors; the groups need not be finite. -/
def IsFormation (𝔉 : GroupClass) : Prop :=
  (∃ (G : Type) (_ : Group G), 𝔉 G) ∧
    (∀ (G H : Type) [Group G] [Group H] (φ : G →* H), Function.Surjective φ → 𝔉 G → 𝔉 H) ∧
    ∀ (G : Type) [Group G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
      𝔉 (G ⧸ N₁) → 𝔉 (G ⧸ N₂) → 𝔉 (G ⧸ (N₁ ⊓ N₂))

/-- **First-order axiomatizable classes of groups.** A class $\mathfrak{F}$ of groups is
first-order axiomatizable when there is a theory $T$ in the first-order language of groups such
that a group $G$ lies in $\mathfrak{F}$ if and only if $G$, with its canonical structure, is a
model of $T$. -/
def IsAxiomatizable (𝔉 : GroupClass) : Prop :=
  ∃ T : groupLanguage.Theory, ∀ (G : Type) [Group G],
    𝔉 G ↔ @Theory.Model groupLanguage G (groupLanguageStructure G) T

/-- **Varieties of groups.** A class $\mathfrak{F}$ of groups is a variety when there is a set
$W$ of elements of the free group on generators $x_0, x_1, x_2, \dots$ such that a group $G$ lies
in $\mathfrak{F}$ if and only if every $w \in W$ evaluates to $1$ in $G$ under every assignment of
elements of $G$ to the generators. -/
def IsVariety (𝔉 : GroupClass) : Prop :=
  ∃ W : Set (FreeGroup ℕ), ∀ (G : Type) [Group G],
    𝔉 G ↔ ∀ w ∈ W, ∀ x : ℕ → G, FreeGroup.lift x w = 1

/-- **The Gaglione–Spellman question on axiomatizable formations (Kourovka 14.32).** The
proposition that every first-order axiomatizable formation of groups is a variety: every class
$\mathfrak{F}$ of groups that is a formation and is first-order axiomatizable is a variety. -/
def axiomatizableFormationIsVariety : Prop :=
  ∀ 𝔉 : GroupClass, IsFormation 𝔉 → IsAxiomatizable 𝔉 → IsVariety 𝔉

/--
**Not every axiomatizable formation of groups is a variety.** The Gaglione–Spellman question
(Kourovka 14.32) has a negative answer: it is not the case that every first-order axiomatizable
formation of groups is a variety, that is, some class of groups is a formation and is first-order
axiomatizable but is not a variety.

Kearnes proved more: every variety of groups that contains a finite non-solvable group contains a
first-order axiomatizable subformation that is not a variety.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
14.32 (A. M. Gaglione, D. Spellman); resolution: K. A. Kearnes, J. Group Theory 13 (2010), no. 2,
233-241, Kourovka Archive, Problem 14.32: every variety of groups containing a finite non-solvable
member contains an axiomatic subformation that is not a variety (answer: No).
-/
public theorem_wanted axiomatizableFormationIsVariety_refuted : ¬ axiomatizableFormationIsVariety

end MathlibExt.GroupTheory.AxiomatizableFormationVarietyKourovka14Problem32Wanted
