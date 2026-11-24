/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared notions for formations of finite groups

Inclusion of classes, local (saturated) formations and residuals, on top of `FiniteGroupClass` and
`IsFormation` from the WantedExt entry for Kourovka Notebook Problem 13.51. Shared by the WantedExt
entries for Kourovka Notebook Problems 9.58, 9.59, 9.60 and 9.73 so that they speak about the same
notions. The residual and saturation predicates of the 12.97 and 11.91 entries are stated for other
carriers (the `GroupClass` structure of 12.97, and isomorphism-closed classes of finite soluble
groups in 11.91), so they do not apply to `FiniteGroupClass`.
-/

module

public import WantedExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteGroupFormationShared

open MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted

/-- **Inclusion of classes of finite groups.** For classes $\mathfrak{F}$ and $\mathfrak{G}$ of
finite groups, $\mathfrak{F} \subseteq \mathfrak{G}$ means that every finite group in
$\mathfrak{F}$ belongs to $\mathfrak{G}$. -/
def ClassLE (𝔉 𝔊 : FiniteGroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝔉 G → 𝔊 G

/-- **Local formation of finite groups.** A class $\mathfrak{F}$ of finite groups is a local
formation when it is a formation, contains the trivial group, and is saturated: a finite group $G$
belongs to $\mathfrak{F}$ whenever $G/\Phi(G)$ does, where $\Phi(G)$ is the Frattini subgroup of
$G$.

By the Gaschütz-Lubeseder-Schmid theorem a nonempty formation of finite groups is local (defined
by a formation function) iff it is saturated. -/
def IsLocalFormation (𝔉 : FiniteGroupClass) : Prop :=
  IsFormation 𝔉 ∧ 𝔉 Unit ∧ ∀ (G : Type) [Group G] [Finite G], 𝔉 (G ⧸ frattini G) → 𝔉 G

/-- **Residual of a finite group with respect to a class.** For a class $\mathfrak{F}$ of finite
groups and a finite group $G$, the $\mathfrak{F}$-residual $G^{\mathfrak{F}}$ is the intersection
of all normal subgroups $N$ of $G$ with $G/N \in \mathfrak{F}$.

For a formation containing the trivial group it is the smallest such $N$. -/
def residual (𝔉 : FiniteGroupClass) (G : Type) [Group G] [Finite G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N.Normal) (_ : 𝔉 (G ⧸ N)), N

end MathlibExt.GroupTheory.FiniteGroupFormationShared
