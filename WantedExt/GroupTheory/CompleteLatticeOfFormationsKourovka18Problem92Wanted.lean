/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-algebraic and non-modular complete lattices of formations (Kourovka Notebook Problem 18.92)

Kourovka Notebook, Problem 18.92 (A. N. Skiba), marked solved in the 21st issue: a non-empty set `θ`
of formations is a complete lattice of formations if the intersection of any set of formations in
`θ` belongs to `θ` and `θ` has a largest element. An element `a` of a complete lattice is compact if
`a ≤ ⋁X` implies `a ≤ ⋁X₁` for a finite `X₁ ⊆ X`, and the lattice is algebraic if every element is a
join of compact elements. (a) Is there a non-algebraic complete lattice of formations of finite
groups? (b) Is there a non-modular complete lattice of formations of finite groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.92 (A. N. Skiba). UnsolvedMath record
UM-00701521 (`KOU-18.92`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in the
WantedExt module for Kourovka 12.97); a formation consists of finite groups, contains the trivial
group, and is closed under quotients and finite subdirect products (`G ⧸ N₁, G ⧸ N₂ ∈ X → G ⧸ (N₁ ⊓
N₂) ∈ X`). Intersections of nonempty subsets of `θ` lie in `θ` (the empty intersection is replaced
by the largest element). Order is inclusion; joins are least upper bounds inside `θ` and meets are
intersections, as in the problem's definition. The resolution is an AI-generated solution confirmed
by A. N. Skiba.
-/

/-- **Isomorphism-closed classes of groups (Kourovka 18.92).** A class of groups $\mathfrak{X}$ is
given by a membership predicate on groups whose underlying type lies in the lowest universe, such
that whenever a group $H$ belongs to $\mathfrak{X}$ and $K$ is a group isomorphic to $H$, the group
$K$ also belongs to $\mathfrak{X}$. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- **Formations of finite groups (Kourovka 18.92).** A class $\mathfrak{X}$ of groups is a
formation if every group in $\mathfrak{X}$ is finite, $\mathfrak{X}$ contains the trivial group,
for every finite group $G$ in $\mathfrak{X}$ and every normal subgroup $N$ of $G$ the quotient
$G/N$ lies in $\mathfrak{X}$, and for every finite group $G$ with normal subgroups $N_1$ and $N_2$
such that $G/N_1$ and $G/N_2$ lie in $\mathfrak{X}$, the quotient $G/(N_1 \cap N_2)$ lies in
$\mathfrak{X}$. -/
def IsFormation (X : GroupClass) : Prop :=
  (∀ (H : Type) [Group H], X.mem H → Finite H) ∧ X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- **Inclusion of group classes.** For classes of groups $\mathfrak{X}$ and $\mathfrak{Y}$, the
class $\mathfrak{X}$ is included in $\mathfrak{Y}$, written $\mathfrak{X} \subseteq \mathfrak{Y}$,
if every group that belongs to $\mathfrak{X}$ also belongs to $\mathfrak{Y}$. -/
def Incl (X Y : GroupClass) : Prop :=
  ∀ (H : Type) [Group H], X.mem H → Y.mem H

/-- **Complete lattices of formations.** A set $\Theta$ of classes of groups is a complete lattice
of formations if it is nonempty, every member of $\Theta$ is a formation, for every nonempty subset
$S \subseteq \Theta$ the intersection of the classes in $S$ (the class of groups belonging to every
member of $S$) belongs to $\Theta$, and $\Theta$ has a member that contains every member of
$\Theta$. -/
def IsCompleteLatticeOfFormations (Θ : Set GroupClass) : Prop :=
  Θ.Nonempty ∧ (∀ X ∈ Θ, IsFormation X) ∧
  (∀ S ⊆ Θ, S.Nonempty → ∃ Y ∈ Θ, ∀ (H : Type) [Group H], Y.mem H ↔ ∀ X ∈ S, X.mem H) ∧
  ∃ T ∈ Θ, ∀ X ∈ Θ, Incl X T

/-- **Joins in a set of group classes.** Let $\Theta$ and $S$ be sets of classes of groups. A class
$\mathfrak{J}$ is the join of $S$ in $\Theta$ if $\mathfrak{J} \in \Theta$, every member of $S$ is
contained in $\mathfrak{J}$, and $\mathfrak{J}$ is contained in every member of $\Theta$ that
contains every member of $S$. -/
def IsJoinIn (Θ S : Set GroupClass) (J : GroupClass) : Prop :=
  J ∈ Θ ∧ (∀ X ∈ S, Incl X J) ∧ ∀ U ∈ Θ, (∀ X ∈ S, Incl X U) → Incl J U

/-- **Compact elements of a set of group classes.** Let $\Theta$ be a set of classes of groups and
$\mathfrak{A}$ a class of groups. Then $\mathfrak{A}$ is compact in $\Theta$ if, for every subset
$S \subseteq \Theta$ and every join $\mathfrak{J}$ of $S$ in $\Theta$ with
$\mathfrak{A} \subseteq \mathfrak{J}$, there are a finite subset $S_1 \subseteq S$ and a join
$\mathfrak{J}_1$ of $S_1$ in $\Theta$ with $\mathfrak{A} \subseteq \mathfrak{J}_1$. -/
def IsCompactIn (Θ : Set GroupClass) (A : GroupClass) : Prop :=
  ∀ S ⊆ Θ, ∀ J, IsJoinIn Θ S J → Incl A J →
    ∃ S₁ ⊆ S, S₁.Finite ∧ ∃ J₁, IsJoinIn Θ S₁ J₁ ∧ Incl A J₁

/-- **Algebraic sets of group classes.** A set $\Theta$ of classes of groups is algebraic if every
member $\mathfrak{A}$ of $\Theta$ is the join in $\Theta$ of some subset $S \subseteq \Theta$ all of
whose members are compact in $\Theta$. -/
def IsAlgebraicIn (Θ : Set GroupClass) : Prop :=
  ∀ A ∈ Θ, ∃ S ⊆ Θ, (∀ C ∈ S, IsCompactIn Θ C) ∧ IsJoinIn Θ S A

/-- **Modular sets of group classes.** A set $\Theta$ of classes of groups is modular if for all
$\mathfrak{A}, \mathfrak{B}, \mathfrak{C} \in \Theta$ with $\mathfrak{A} \subseteq \mathfrak{C}$
the following holds: whenever $\mathfrak{J}_1$ is the join in $\Theta$ of the set
$\{\mathfrak{A}, \mathfrak{B} \cap \mathfrak{C}\}$ and $\mathfrak{D}$ is the join in $\Theta$ of
the set $\{\mathfrak{A}, \mathfrak{B}\}$, the classes $\mathfrak{J}_1$ and
$\mathfrak{D} \cap \mathfrak{C}$ contain the same groups. This is the modular law
$\mathfrak{A} \vee (\mathfrak{B} \wedge \mathfrak{C}) = (\mathfrak{A} \vee \mathfrak{B}) \wedge
\mathfrak{C}$, with joins taken in $\Theta$ and meets the intersections. -/
def IsModularIn (Θ : Set GroupClass) : Prop :=
  ∀ A ∈ Θ, ∀ B ∈ Θ, ∀ C ∈ Θ, Incl A C → ∀ BC J₁ AB J₂ : GroupClass,
    (∀ (H : Type) [Group H], BC.mem H ↔ B.mem H ∧ C.mem H) → IsJoinIn Θ {A, BC} J₁ →
    IsJoinIn Θ {A, B} AB → (∀ (H : Type) [Group H], J₂.mem H ↔ AB.mem H ∧ C.mem H) →
    Incl J₁ J₂ ∧ Incl J₂ J₁

/-- **Kourovka Problem 18.92(a) (A. N. Skiba).** The proposition that some set $\Theta$ of classes
of groups is a complete lattice of formations of finite groups and is not algebraic. -/
def nonAlgebraicCompleteLatticeOfFormations : Prop :=
  ∃ Θ : Set GroupClass, IsCompleteLatticeOfFormations Θ ∧ ¬ IsAlgebraicIn Θ

/-- **The non-modular formation lattice problem (Kourovka 18.92(b), A. N. Skiba).** The proposition
that there is a complete lattice of formations of finite groups that is not modular, joins being
least upper bounds in the lattice and meets being intersections. -/
def nonModularCompleteLatticeOfFormations : Prop :=
  ∃ Θ : Set GroupClass, IsCompleteLatticeOfFormations Θ ∧ ¬ IsModularIn Θ

/-- **Non-algebraic complete lattices of formations exist.** There is a set $\Theta$ of classes of
groups that is a complete lattice of formations of finite groups and is not algebraic; that is,
Kourovka Problem 18.92(a) has a positive answer.

The Kourovka Notebook (21st issue) answers 18.92(a) "Yes", by an AI-generated solution confirmed by
A. N. Skiba (Kinyon–Urban, 2026): for a set $S$ of primes let $\mathfrak{F}_S$ be the class of
finite groups whose order has all its prime divisors in $S$; the classes $\mathfrak{F}_S$ with $S$
finite, together with the class of all finite groups, form a complete lattice of formations whose
only compact element is the bottom.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 18.92 (A. N. Skiba); resolution: M. Kinyon and J.
Urban, Results on problems from the Kourovka Notebook, preprint, version 4, 19 September 2026,
Section 3.29 (Problem 18.92): with F_S the finite groups whose order has all prime divisors in S,
{F_S : S finite} ∪ {F_P} is not algebraic and the formations with prime sets ∅, {2}, {2, 3}, {5}, P
form a pentagon N_5; an AI solution confirmed by A. N. Skiba, accepted in the Kourovka Notebook
(21st issue),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted nonAlgebraicCompleteLatticeOfFormations_holds :
    nonAlgebraicCompleteLatticeOfFormations

/--
**A non-modular complete lattice of formations exists (Kourovka 18.92(b)).** There is a complete
lattice of formations of finite groups that is not modular: a nonempty set $\Theta$ of formations
of finite groups, ordered by inclusion, that contains the intersection of each of its nonempty
subsets and has a largest element, in which the modular law $A \vee (B \wedge C) = (A \vee B)
\wedge C$ for $A \le C$ fails, joins being least upper bounds in $\Theta$ and meets intersections.

The Kourovka Notebook (21st issue) answers 18.92(b) "Yes" (Kinyon-Urban, 2026, confirmed by A. N.
Skiba): writing $\mathfrak{F}_S$ for the finite groups whose order has all prime divisors in $S$,
the formations $\mathfrak{F}_S$ with $S = \emptyset, \{2\}, \{2, 3\}, \{5\}$ and $S$ the set of all
primes are closed under intersections and form the pentagon $N_5$.

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 18.92 (A. N. Skiba); resolution: M. Kinyon and J. Urban, Results on problems from
the Kourovka Notebook, preprint, version 4, 19 September 2026, Section 3.29 (Problem 18.92): with
F_S the finite groups whose order has all prime divisors in S, {F_S : S finite} ∪ {F_P} is not
algebraic and the formations with prime sets ∅, {2}, {2, 3}, {5}, P form a pentagon N_5; an AI
solution confirmed by A. N. Skiba, accepted in the Kourovka Notebook (21st issue),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted nonModularCompleteLatticeOfFormations_holds :
    nonModularCompleteLatticeOfFormations

end MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted
