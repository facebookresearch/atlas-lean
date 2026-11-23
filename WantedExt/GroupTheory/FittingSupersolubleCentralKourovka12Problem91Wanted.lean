/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fitting classes of supersoluble groups (Kourovka Notebook Problem 12.91)

Kourovka Notebook, Archive of Solved Problems, Problem 12.91 (H. Heineken): every metabelian group
belonging to a Fitting class of finite supersoluble groups is nilpotent. Does every group belonging
to a Fitting class of supersoluble groups have only central minimal normal subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FittingSupersolubleCentralKourovka12Problem91Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.91 (H.
Heineken). UnsolvedMath record UM-00700908 (`KOU-12.91`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. A Fitting class is closed under normal subgroups and under products of two
normal members. Supersoluble means a series of normal subgroups with cyclic factors; a minimal
normal subgroup is a nontrivial normal subgroup containing no smaller nontrivial normal subgroup.
-/

/-- **Isomorphism-closed classes of groups (Kourovka 12.91).** A class of groups is a property of
groups (in the lowest type universe) that is closed under isomorphism: whenever a group $H$ has the
property and $H$ is isomorphic to a group $K$, then $K$ has the property. Only the finite members of
a class are used in Kourovka Problem 12.91. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Fitting classes (Kourovka 12.91).** A class $\mathfrak{X}$ of groups is a Fitting class (of
finite groups) if, for every finite group $G$: whenever $G \in \mathfrak{X}$, every normal subgroup
of $G$ belongs to $\mathfrak{X}$; and whenever $N_1$ and $N_2$ are normal subgroups of $G$ that
belong to $\mathfrak{X}$, the subgroup $N_1 N_2$ they generate belongs to $\mathfrak{X}$. -/
def IsFitting (X : GroupClass) : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → X.mem G → X.mem N) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G), N₁.Normal → N₂.Normal →
    X.mem N₁ → X.mem N₂ → X.mem ↥(N₁ ⊔ N₂)

/-- **Supersoluble groups (Kourovka 12.91).** A group $G$ is supersoluble if it has a chain of
subgroups $1 = G_0 \le G_1 \le \cdots \le G_k = G$, each normal in $G$, such that for every $i < k$
there is an element $x \in G_{i+1}$ with $G_{i+1} = \langle x \rangle G_i$; that is, every factor
$G_{i+1}/G_i$ is cyclic. -/
def IsSupersoluble (G : Type*) [Group G] : Prop :=
  ∃ (k : ℕ) (s : ℕ → Subgroup G), s 0 = ⊥ ∧ s k = ⊤ ∧ ∀ i < k, s i ≤ s (i + 1) ∧
    (s i).Normal ∧ ∃ x ∈ s (i + 1), s (i + 1) = Subgroup.closure {x} ⊔ s i

/-- **Minimal normal subgroups (Kourovka 12.91).** A subgroup $N$ of a group $G$ is minimal normal
if $N$ is a nontrivial normal subgroup of $G$ and every nontrivial normal subgroup $M$ of $G$ with
$M \le N$ equals $N$. -/
def IsMinimalNormal {G : Type*} [Group G] (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → M = N

/-- **Heineken's question on Fitting classes of supersoluble groups.** The proposition that for
every class $\mathfrak{X}$ of groups that is a Fitting class and all of whose finite members are
supersoluble, every minimal normal subgroup of every finite group $G \in \mathfrak{X}$ is contained
in the center of $G$.

This is Kourovka Problem 12.91 (H. Heineken). -/
def fittingSupersolubleMinimalNormalCentral : Prop :=
  ∀ X : GroupClass, IsFitting X →
    (∀ (G : Type) [Group G] [Finite G], X.mem G → IsSupersoluble G) →
    ∀ (G : Type) [Group G] [Finite G], X.mem G →
      ∀ N : Subgroup G, IsMinimalNormal N → N ≤ Subgroup.center G

/-- **A Fitting class of supersoluble groups with a non-central minimal normal subgroup.** There
exist a class $\mathfrak{X}$ of groups that is a Fitting class and all of whose finite members are
supersoluble, a finite group $G \in \mathfrak{X}$, and a minimal normal subgroup $N$ of $G$ that is
not contained in the center of $G$.

This answers Kourovka Problem 12.91 in the negative.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.91 (H. Heineken);
resolution: H. Heineken, Rend. Sem. Mat. Univ. Padova 98 (1997), 241-251, Kourovka Archive, Problem
12.91: No, it does not.
-/
public theorem_wanted fittingSupersolubleMinimalNormalCentral_refuted :
    ¬ fittingSupersolubleMinimalNormalCentral

end MathlibExt.GroupTheory.FittingSupersolubleCentralKourovka12Problem91Wanted
