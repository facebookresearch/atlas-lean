/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Indecomposability of the formation of finite `p`-groups (Kourovka Notebook Problem 10.72)

Kourovka Notebook, Archive of Solved Problems, Problem 10.72 (L. A. Shemetkov): prove that the
formation of all finite `p`-groups does not decompose into a product of two non-trivial
subformations.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.72 (L. A.
Shemetkov). UnsolvedMath record UM-00700687 (`KOU-10.72`), dataset ulamai/UnsolvedMath v1.8.0.

A formation is an isomorphism-closed class of finite groups (in `Type`) that contains the trivial
group and is closed under quotients and subdirect products; the product is Gaschütz's `𝔉 ∘ 𝔊` (`G ∈
𝔉 ∘ 𝔊` iff the `𝔊`-residual of `G` lies in `𝔉`). Non-trivial subformations are read as subformations
of `𝔑_p` different from the formation of trivial groups and from `𝔑_p` itself: `𝔑_p ∘ 𝔊 = 𝔉 ∘ 𝔑_p =
𝔑_p` for all subformations `𝔉, 𝔊` of `𝔑_p`, so admitting the factor `𝔑_p` would make the statement
false.
-/

/-- **Class of finite groups (Kourovka 10.72).** A class of finite groups is given by a
membership predicate: a proposition $X(G)$ for every finite group $G$. It is not required to be
closed under isomorphisms. -/
abbrev GroupClass : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Prop

/-- **Formation of finite groups (Kourovka 10.72).** A class $X$ of finite groups is a formation
when it is closed under isomorphisms, contains the trivial group, contains the quotient $G/N$ of
each of its members $G$ by every normal subgroup $N$, and contains $G/(N_1 \cap N_2)$ whenever
$N_1$ and $N_2$ are normal subgroups of a finite group $G$ with $G/N_1$ and $G/N_2$ in $X$. The
last condition is closure under subdirect products. -/
def IsFormation (X : GroupClass) : Prop :=
  (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H], (G ≃* H) → X G → X H) ∧ X Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X G → X (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X (G ⧸ N₁) → X (G ⧸ N₂) → X (G ⧸ (N₁ ⊓ N₂))

/-- **Residual of a finite group with respect to a class (Kourovka 10.72).** For a class $X$ of
finite groups and a finite group $G$, the $X$-residual of $G$ is the intersection of all normal
subgroups $N$ of $G$ with $G/N \in X$. When $X$ is a formation, it is the smallest such $N$. -/
def residual (X : GroupClass) (G : Type) [Group G] [Finite G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : ∃ _ : N.Normal, X (G ⧸ N)), N

/-- **Indecomposability of the formation of finite $p$-groups (Kourovka 10.72).** The statement
that for every prime $p$, the class $\mathfrak{N}_p$ of all finite $p$-groups is not the Gaschütz
product $\mathfrak{F} \circ \mathfrak{G}$ of two formations $\mathfrak{F}$ and $\mathfrak{G}$ that
consist of $p$-groups, each contain a nontrivial group and each omit some finite $p$-group. Here a
finite group $G$ lies in $\mathfrak{F} \circ \mathfrak{G}$ when its $\mathfrak{G}$-residual lies
in $\mathfrak{F}$.

Omitting some finite $p$-group is part of the reading of "non-trivial": for all formations
$\mathfrak{F}, \mathfrak{G}$ consisting of $p$-groups,
$\mathfrak{N}_p \circ \mathfrak{G} = \mathfrak{F} \circ \mathfrak{N}_p = \mathfrak{N}_p$. -/
def pGroupFormationIndecomposable : Prop :=
  ∀ p : ℕ, p.Prime → ∀ F H : GroupClass, IsFormation F → IsFormation H →
    (∀ (G : Type) [Group G] [Finite G], F G → IsPGroup p G) →
    (∀ (G : Type) [Group G] [Finite G], H G → IsPGroup p G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ F G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), Nontrivial G ∧ H G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ ¬ F G) →
    (∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ ¬ H G) →
    ¬ ∀ (G : Type) [Group G] [Finite G], IsPGroup p G ↔ F (residual H G)

/--
**The formation of finite $p$-groups is indecomposable.** For every prime $p$, the class
$\mathfrak{N}_p$ of all finite $p$-groups is not the Gaschütz product $\mathfrak{F} \circ
\mathfrak{G}$ of two formations $\mathfrak{F}$ and $\mathfrak{G}$ that consist of $p$-groups, each
contain a nontrivial group and each omit some finite $p$-group. Here a finite group $G$ lies in
$\mathfrak{F} \circ \mathfrak{G}$ when its $\mathfrak{G}$-residual lies in $\mathfrak{F}$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
10.72 (L. A. Shemetkov); resolution: A. N. Skiba and L. A. Shemetkov, Dokl. Akad. Nauk BSSR 33
(1989), 581-582 (Russian), Kourovka Archive, Problem 10.72 ("This has been proved").
-/
public theorem_wanted pGroupFormationIndecomposable_holds : pGroupFormationIndecomposable

end MathlibExt.GroupTheory.PGroupFormationIndecomposableKourovka10Problem72Wanted
