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

/-- A class of groups closed under isomorphism, given by a membership predicate on groups in
`Type`. -/
structure GroupClass where
  /-- Membership predicate. -/
  mem : ∀ (H : Type) [Group H], Prop
  /-- Closure under isomorphism. -/
  iso : ∀ (H K : Type) [Group H] [Group K], (H ≃* K) → mem H → mem K

/-- A formation of finite groups: its members are finite, it contains the trivial group, it is
closed under quotients, and `G ⧸ N₁, G ⧸ N₂ ∈ X` implies `G ⧸ (N₁ ⊓ N₂) ∈ X`. -/
def IsFormation (X : GroupClass) : Prop :=
  (∀ (H : Type) [Group H], X.mem H → Finite H) ∧ X.mem Unit ∧
  (∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal], X.mem G → X.mem (G ⧸ N)) ∧
  ∀ (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    X.mem (G ⧸ N₁) → X.mem (G ⧸ N₂) → X.mem (G ⧸ (N₁ ⊓ N₂))

/-- Inclusion of classes. -/
def Incl (X Y : GroupClass) : Prop :=
  ∀ (H : Type) [Group H], X.mem H → Y.mem H

/-- `Θ` is a complete lattice of formations: a nonempty set of formations, containing the
intersection of each of its nonempty subsets and having a largest element. -/
def IsCompleteLatticeOfFormations (Θ : Set GroupClass) : Prop :=
  Θ.Nonempty ∧ (∀ X ∈ Θ, IsFormation X) ∧
  (∀ S ⊆ Θ, S.Nonempty → ∃ Y ∈ Θ, ∀ (H : Type) [Group H], Y.mem H ↔ ∀ X ∈ S, X.mem H) ∧
  ∃ T ∈ Θ, ∀ X ∈ Θ, Incl X T

/-- `J` is the join of `S` in `Θ`: the least member of `Θ` containing every member of `S`. -/
def IsJoinIn (Θ S : Set GroupClass) (J : GroupClass) : Prop :=
  J ∈ Θ ∧ (∀ X ∈ S, Incl X J) ∧ ∀ U ∈ Θ, (∀ X ∈ S, Incl X U) → Incl J U

/-- `A` is compact in `Θ`: whenever `A` lies below the join of `S ⊆ Θ`, it lies below the join of
some finite `S₁ ⊆ S`. -/
def IsCompactIn (Θ : Set GroupClass) (A : GroupClass) : Prop :=
  ∀ S ⊆ Θ, ∀ J, IsJoinIn Θ S J → Incl A J →
    ∃ S₁ ⊆ S, S₁.Finite ∧ ∃ J₁, IsJoinIn Θ S₁ J₁ ∧ Incl A J₁

/-- `Θ` is algebraic: every member is the join of a set of compact members. -/
def IsAlgebraicIn (Θ : Set GroupClass) : Prop :=
  ∀ A ∈ Θ, ∃ S ⊆ Θ, (∀ C ∈ S, IsCompactIn Θ C) ∧ IsJoinIn Θ S A

/-- `Θ` is modular: `A ∨ (B ∧ C) = (A ∨ B) ∧ C` whenever `A ≤ C`, with joins taken in `Θ` and meets
the intersections (the meets in `Θ`). -/
def IsModularIn (Θ : Set GroupClass) : Prop :=
  ∀ A ∈ Θ, ∀ B ∈ Θ, ∀ C ∈ Θ, Incl A C → ∀ BC J₁ AB J₂ : GroupClass,
    (∀ (H : Type) [Group H], BC.mem H ↔ B.mem H ∧ C.mem H) → IsJoinIn Θ {A, BC} J₁ →
    IsJoinIn Θ {A, B} AB → (∀ (H : Type) [Group H], J₂.mem H ↔ AB.mem H ∧ C.mem H) →
    Incl J₁ J₂ ∧ Incl J₂ J₁

/-- Kourovka 18.92(a) (A. N. Skiba): there is a non-algebraic complete lattice of formations of
finite groups. -/
def nonAlgebraicCompleteLatticeOfFormations : Prop :=
  ∃ Θ : Set GroupClass, IsCompleteLatticeOfFormations Θ ∧ ¬ IsAlgebraicIn Θ

/-- Kourovka 18.92(b) (A. N. Skiba): there is a non-modular complete lattice of formations of finite
groups. -/
def nonModularCompleteLatticeOfFormations : Prop :=
  ∃ Θ : Set GroupClass, IsCompleteLatticeOfFormations Θ ∧ ¬ IsModularIn Θ

/--
Resolved true: the Kourovka Notebook (21st issue) answers 18.92(a) "Yes", by an AI-generated
solution confirmed by A. N. Skiba (Kinyon-Urban, 2026): for `𝔉_S` the finite groups with all prime
divisors of the order in `S`, the family of `𝔉_S` with `S` finite together with the class of all
finite groups is a complete lattice of formations whose only compact element is the bottom. Source:
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
Resolved true: the Kourovka Notebook (21st issue) answers 18.92(b) "Yes" (Kinyon-Urban, 2026,
confirmed by A. N. Skiba): the formations `𝔉_S` with prime sets `∅, {2}, {2, 3}, {5}` and all primes
are closed under intersections and form the pentagon `N₅`. Source: E. I. Khukhro and V. D. Mazurov
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
