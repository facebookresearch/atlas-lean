/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hereditary formations with Shmidt minimal non-members (Kourovka Notebook Problem 11.91)

Kourovka Notebook, Archive of Solved Problems, Problem 11.91 (V. N. Semenchuk): prove that a
hereditary formation `𝔉` of finite soluble groups is local if every finite soluble non-simple
minimal non-`𝔉`-group is a Shmidt group (a non-nilpotent finite group all of whose proper subgroups
are nilpotent).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.HereditaryFormationShmidtLocalKourovka11Problem91Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.91 (V. N.
Semenchuk). UnsolvedMath record UM-00700783 (`KOU-11.91`), dataset ulamai/UnsolvedMath v1.8.0.

A class of groups is a predicate on groups in `Type`. A hereditary formation of finite soluble
groups is an isomorphism-closed class of finite soluble groups closed under subgroups, quotients and
subdirect products. "Local" is stated as saturated (`G / Φ(G) ∈ 𝔉` implies `G ∈ 𝔉`, `Φ` the Frattini
subgroup): by the Gaschütz-Lubeseder theorem a nonempty formation of finite soluble groups is local
iff it is saturated, so for nonempty `𝔉` the statement is the source's. The structure also admits
the empty class, which is saturated but not local; it fails the hypothesis, since the trivial group
is then a non-simple minimal non-member that is nilpotent, so both readings hold for it vacuously. A
minimal non-`𝔉`-group is a group outside `𝔉` all of whose proper subgroups lie in `𝔉`.
-/

/-- **Classes of groups.** A class of groups is a property of groups: for each group $G$ it gives
a proposition, read as "$G$ belongs to the class". No closure under isomorphism is required. -/
abbrev GroupClass : Type 1 := ∀ (G : Type) [Group G], Prop

/-- **Hereditary formations of finite soluble groups.** A class $\mathfrak F$ of groups is a
hereditary formation of finite soluble groups if every group in $\mathfrak F$ is finite and
soluble; $\mathfrak F$ is closed under isomorphisms, under taking subgroups and under taking
quotients by normal subgroups; and for every finite group $G$ with normal subgroups $M$ and $N$
such that $G/M$ and $G/N$ lie in $\mathfrak F$, also $G/(M \cap N)$ lies in $\mathfrak F$. -/
structure IsHereditarySolubleFormation (F : GroupClass) : Prop where
  finite_solvable : ∀ (G : Type) [Group G], F G → Finite G ∧ Group.IsSolvable G
  of_mulEquiv : ∀ (G H : Type) [Group G] [Group H], (G ≃* H) → F G → F H
  subgroup : ∀ (G : Type) [Group G] (H : Subgroup G), F G → F H
  quotient : ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], F G → F (G ⧸ N)
  subdirect : ∀ (G : Type) [Group G] [Finite G] (M N : Subgroup G) [M.Normal] [N.Normal],
    F (G ⧸ M) → F (G ⧸ N) → F (G ⧸ (M ⊓ N))

/-- **Saturated classes of groups.** A class $\mathfrak F$ of groups is saturated if every finite
soluble group $G$ such that $G/\Phi(G)$ lies in $\mathfrak F$, where $\Phi(G)$ is the Frattini
subgroup of $G$, itself lies in $\mathfrak F$.

By the Gaschütz–Lubeseder theorem, a nonempty formation of finite soluble groups is saturated if
and only if it is local. -/
def IsSaturated (F : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → F (G ⧸ frattini G) → F G

/-- **Minimal non-members of a class of groups.** Let $\mathfrak F$ be a class of groups. A group
$G$ is a minimal non-$\mathfrak F$-group if $G$ does not lie in $\mathfrak F$ but every proper
subgroup of $G$ lies in $\mathfrak F$. -/
def IsMinimalNon (F : GroupClass) (G : Type) [Group G] : Prop :=
  ¬ F G ∧ ∀ H : Subgroup G, H ≠ ⊤ → F H

/-- **Shmidt groups.** A group $G$ is a Shmidt group if it is finite and not nilpotent, but every
proper subgroup of $G$ is nilpotent. -/
def IsShmidtGroup (G : Type) [Group G] : Prop :=
  Finite G ∧ ¬ Group.IsNilpotent G ∧ ∀ H : Subgroup G, H ≠ ⊤ → Group.IsNilpotent H

/-- **Kourovka Problem 11.91 (statement).** The statement that every hereditary formation
$\mathfrak F$ of finite soluble groups such that every finite soluble non-simple minimal
non-$\mathfrak F$-group (a group outside $\mathfrak F$ all of whose proper subgroups lie in
$\mathfrak F$) is a Shmidt group is saturated, that is, every finite soluble group $G$ whose
quotient $G/\Phi(G)$ by its Frattini subgroup $\Phi(G)$ lies in $\mathfrak F$ itself lies in
$\mathfrak F$.

Under this hypothesis $\mathfrak F$ contains the trivial group, so by the Gaschütz–Lubeseder
theorem saturated is the same as local, the property the problem (V. N. Semenchuk) asks for. -/
def hereditaryFormationLocalOfShmidt : Prop :=
  ∀ F : GroupClass, IsHereditarySolubleFormation F →
    (∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ¬ IsSimpleGroup G → IsMinimalNon F G →
      IsShmidtGroup G) →
    IsSaturated F

/--
**Skiba's theorem (Kourovka Problem 11.91).** Let $\mathfrak F$ be a hereditary formation of
finite soluble groups: every group in $\mathfrak F$ is finite and soluble, $\mathfrak F$ is closed
under isomorphisms, subgroups and quotients, and whenever $M$ and $N$ are normal subgroups of a
finite group $G$ with $G/M$ and $G/N$ in $\mathfrak F$, also $G/(M \cap N)$ lies in $\mathfrak F$.
Suppose that every finite soluble group that is not simple and is a minimal non-$\mathfrak F$-group
(it does not lie in $\mathfrak F$, but all of its proper subgroups do) is a Shmidt group, that is,
a finite non-nilpotent group all of whose proper subgroups are nilpotent. Then $\mathfrak F$ is
saturated: every finite soluble group $G$ such that $G/\Phi(G)$ lies in $\mathfrak F$, where
$\Phi(G)$ is the Frattini subgroup of $G$, itself lies in $\mathfrak F$.

The hypothesis forces the trivial group into $\mathfrak F$, and by the Gaschütz–Lubeseder theorem a
nonempty saturated formation of finite soluble groups is local, so $\mathfrak F$ is local.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 11.91 (V. N. Semenchuk); resolution: A. N. Skiba, Dokl. Akad.
Nauk Belorus. SSR 34, no. 11 (1990), 982-985 (Russian), Kourovka Archive, Problem 11.91: "This is
proved", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted hereditaryFormationLocalOfShmidt_holds : hereditaryFormationLocalOfShmidt

end MathlibExt.GroupTheory.HereditaryFormationShmidtLocalKourovka11Problem91Wanted
