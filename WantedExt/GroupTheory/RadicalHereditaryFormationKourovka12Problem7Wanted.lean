/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Radical hereditary formations need not be composition formations (Kourovka Notebook Problem 12.7)

Kourovka Notebook, Archive of Solved Problems, Problem 12.7 (A. F. Vasil'ev): is every radical
hereditary formation of finite groups a composition formation?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.7 (A. F.
Vasil'ev). UnsolvedMath record UM-00700827 (`KOU-12.7`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in
the `OpenConjectures` entries `Kourovka11Problem117` and `Kourovka12Problem35`); only their finite
members are constrained. A formation contains the trivial group and is closed under quotients and
subdirect products; a radical class is a Fitting class (closed under normal subgroups and under
products of two normal members); hereditary means closed under all subgroups. A composition
formation (Shemetkov) is taken in its standard equivalent form, a solubly saturated (Baer-local)
formation: `G ⧸ Φ(R(G)) ∈ 𝔉` implies `G ∈ 𝔉`, with `R(G)` the soluble radical. The three names are
synonyms in E. N. Myslovets and A. F. Vasil'ev (arXiv:1603.04018, Section 2), whose definition
allows any soluble normal subgroup `N` in place of `R(G)`; this is equivalent for formations, since
`Φ(N) ≤ Φ(R(G))`.
-/

/-- **Isomorphism-closed class of groups.** A class of groups $X$ is a property of groups that is
invariant under isomorphism: if a group $H$ belongs to $X$ and $K$ is a group isomorphic to $H$,
then $K$ belongs to $X$.

Infinite groups may belong to a class; apart from isomorphism invariance, the conditions imposed
on classes below concern only finite groups. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Quotient lying in a class.** For a class of groups $X$, a group $G$ and a subgroup $N$ of $G$,
this holds when $N$ is normal in $G$ and the quotient group $G/N$ belongs to $X$. -/
def QuotMem (X : GroupClass) {G : Type} [Group G] (N : Subgroup G) : Prop :=
  ∃ _ : N.Normal, X.mem (G ⧸ N)

/-- **Formation of finite groups.** A class of groups $X$ is a formation if it contains the trivial
group, for every finite group $G$ in $X$ and every normal subgroup $N$ of $G$ the quotient $G/N$
belongs to $X$, and for every finite group $G$ with normal subgroups $N_1, N_2$ such that
$G/N_1$ and $G/N_2$ belong to $X$, the quotient $G/(N_1 \cap N_2)$ belongs to $X$. -/
def IsFormation (X : GroupClass) : Prop :=
  X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- **Radical (Fitting) class.** A class of groups $X$ is radical if, for every finite group $G$,
every normal subgroup of $G$ belongs to $X$ whenever $G$ does, and whenever $N_1, N_2$ are normal
subgroups of $G$ that belong to $X$, their product $N_1 N_2$ belongs to $X$. -/
def IsRadical (X : GroupClass) : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal → X.mem G → X.mem N) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G), N₁.Normal → N₂.Normal →
    X.mem N₁ → X.mem N₂ → X.mem ↥(N₁ ⊔ N₂)

/-- **Hereditary class of groups.** A class of groups $X$ is hereditary if every subgroup of a
finite group in $X$ belongs to $X$. -/
def IsHereditary (X : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), X.mem G → X.mem H

/-- **Soluble radical.** A subgroup $R$ of a group $G$ is the soluble radical of $G$ if $R$ is a
soluble normal subgroup of $G$ that contains every soluble normal subgroup of $G$. -/
def IsSolubleRadical {G : Type} [Group G] (R : Subgroup G) : Prop :=
  R.Normal ∧ Group.IsSolvable R ∧ ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N ≤ R

/-- **Solubly saturated class.** A class of groups $X$ is solubly saturated (a composition class)
if, for every finite group $G$ with soluble radical $R$, whenever the Frattini subgroup $\Phi(R)$
of $R$ is normal in $G$ and $G/\Phi(R)$ belongs to $X$, the group $G$ belongs to $X$.

A formation with this property is a composition (solubly saturated, Baer-local) formation. -/
def IsComposition (X : GroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R : Subgroup G), IsSolubleRadical R →
    QuotMem X ((frattini R).map R.subtype) → X.mem G

/-- **Kourovka Problem 12.7 (Vasil'ev).** The statement that every radical hereditary formation of
finite groups is a composition formation: every class of groups that is a formation, a radical
class and a hereditary class is solubly saturated. -/
def radicalHereditaryFormationIsComposition : Prop :=
  ∀ X : GroupClass, IsFormation X → IsRadical X → IsHereditary X → IsComposition X

/--
**Radical hereditary formations need not be composition formations.** It is not true that every
radical hereditary formation of finite groups is a composition formation: some class of groups
that is a formation, a radical class and a hereditary class is not solubly saturated.

Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.7 (A. F. Vasil'ev); resolution: S.
F. Kamornikov, Math. Notes 55 (1994), no. 6, 586-588, Kourovka Archive, Problem 12.7: No, it is not.
-/
public theorem_wanted radicalHereditaryFormationIsComposition_refuted :
    ¬ radicalHereditaryFormationIsComposition

end MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted
