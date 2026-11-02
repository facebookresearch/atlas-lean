/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Width of the lattice of closed subgroup functors (Kourovka Notebook Problem 16.82)

Kourovka Notebook, Archive of Solved Problems, Problem 16.82 (A. N. Skiba): let `𝔛` be a non-empty
class of finite groups closed under homomorphic images, subgroups and direct products, and let
`F(𝔛)` be the lattice of closed subgroup functors on `𝔛`. Is there a non-nilpotent class `𝔛` such
that the width of `F(𝔛)` is at most `|π(𝔛)|`, where `π(𝔛)` is the set of prime divisors of the
orders of the groups in `𝔛`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.82 (A. N.
Skiba). UnsolvedMath record UM-00701273 (`KOU-16.82`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are predicates on finite groups in `Type`. A subgroup functor assigns a set
of subgroups to every finite group, only the values on `𝔛` mattering, with the problem's conditions:
`G ∈ τ(G)`, closure under images and preimages along epimorphisms between groups of `𝔛`, and, for
closed functors, `τ(H) ⊆ τ(G)` for `H ∈ τ(G)`. The order of `F(𝔛)` compares values on `𝔛`, so
functors agreeing on `𝔛` are comparable and never lie in a common antichain. Width at most `|π(𝔛)|`
means that every antichain has at most `|π(𝔛)|` elements (as cardinals). Non-nilpotent means
containing a non-nilpotent group.
-/

/-- **Classes of finite groups (Kourovka 16.82 setting).** A class $\mathfrak{X}$ of finite groups
is a predicate on finite groups $G$ (with carrier in the lowest type universe, together with their
group structure); the groups satisfying it are the members of the class, written
$G \in \mathfrak{X}$. -/
abbrev FiniteGroupClass : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Prop

/-- **Closed classes of finite groups.** A class $\mathfrak{X}$ of finite groups is closed when it
contains at least one group and is closed under homomorphic images, subgroups and direct products:
if $G \in \mathfrak{X}$ and $f : G \to H$ is a surjective homomorphism onto a finite group $H$,
then $H \in \mathfrak{X}$; every subgroup of a group in $\mathfrak{X}$ lies in $\mathfrak{X}$; and
if $G, H \in \mathfrak{X}$, then $G \times H \in \mathfrak{X}$. -/
def IsClosedClass (X : FiniteGroupClass) : Prop :=
  (∃ (G : Type) (_ : Group G) (_ : Finite G), X G) ∧
    (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H] (f : G →* H),
      Function.Surjective f → X G → X H) ∧
    (∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), X G → X H) ∧
    ∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H], X G → X H → X (G × H)

/-- **Subgroup assignments.** A subgroup assignment $\tau$ assigns to every finite group $G$ (with
carrier in the lowest type universe) a set $\tau(G)$ of subgroups of $G$. -/
abbrev SubgroupAssignment : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Set (Subgroup G)

/-- **Closed subgroup functors.** Let $\mathfrak{X}$ be a class of finite groups. A subgroup
assignment $\tau$ is a closed subgroup functor on $\mathfrak{X}$ (A. N. Skiba) when the following
three conditions hold. For every $G \in \mathfrak{X}$, $G \in \tau(G)$. For every surjective
homomorphism $\varphi : A \to B$ with $A, B \in \mathfrak{X}$, $\varphi(H) \in \tau(B)$ for every
$H \in \tau(A)$ and $\varphi^{-1}(T) \in \tau(A)$ for every $T \in \tau(B)$. For every
$G \in \mathfrak{X}$, every $H \in \tau(G)$ and every $K \in \tau(H)$, the subgroup $K$, viewed as
a subgroup of $G$, lies in $\tau(G)$; that is, $\tau(H) \subseteq \tau(G)$. -/
def IsClosedSubgroupFunctor (X : FiniteGroupClass) (τ : SubgroupAssignment) : Prop :=
  (∀ (G : Type) [Group G] [Finite G], X G → ⊤ ∈ τ G) ∧
    (∀ (A B : Type) [Group A] [Finite A] [Group B] [Finite B] (φ : A →* B),
      Function.Surjective φ → X A → X B →
        (∀ H ∈ τ A, H.map φ ∈ τ B) ∧ ∀ T ∈ τ B, T.comap φ ∈ τ A) ∧
    ∀ (G : Type) [Group G] [Finite G], X G → ∀ H ∈ τ G, ∀ K ∈ τ H, K.map H.subtype ∈ τ G

/-- **Order on subgroup functors.** Let $\mathfrak{X}$ be a class of finite groups. For subgroup
assignments $\tau_1$ and $\tau_2$, $\tau_1 \le \tau_2$ on $\mathfrak{X}$ when
$\tau_1(G) \subseteq \tau_2(G)$ for every $G \in \mathfrak{X}$. This is the order of the lattice
$F(\mathfrak{X})$ of closed subgroup functors on $\mathfrak{X}$. -/
def FunctorLE (X : FiniteGroupClass) (τ₁ τ₂ : SubgroupAssignment) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], X G → τ₁ G ⊆ τ₂ G

/-- **Prime divisors of a class of finite groups.** For a class $\mathfrak{X}$ of finite groups,
$\pi(\mathfrak{X})$ is the set of primes $p$ that divide the order of some group in
$\mathfrak{X}$. -/
def primesOf (X : FiniteGroupClass) : Set ℕ :=
  {p | p.Prime ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ p ∣ Nat.card G}

/-- **Kourovka Problem 16.82 (Skiba).** For a class $\mathfrak{X}$ of finite groups, let
$\pi(\mathfrak{X})$ be the set of primes dividing the order of some group in $\mathfrak{X}$, and
for subgroup assignments $\tau_1, \tau_2$ write $\tau_1 \le \tau_2$ on $\mathfrak{X}$ when
$\tau_1(G) \subseteq \tau_2(G)$ for every $G \in \mathfrak{X}$. There is a class $\mathfrak{X}$ of
finite groups that contains at least one group, is closed under homomorphic images, subgroups and
direct products, and contains a non-nilpotent group, such that the lattice $F(\mathfrak{X})$ of
closed subgroup functors on $\mathfrak{X}$ has width at most $|\pi(\mathfrak{X})|$: every set of
closed subgroup functors on $\mathfrak{X}$ in which no two distinct members $\tau_1, \tau_2$
satisfy $\tau_1 \le \tau_2$ on $\mathfrak{X}$ has cardinality at most $|\pi(\mathfrak{X})|$. -/
def existsNonnilpotentClassOfSmallWidth : Prop :=
  ∃ X : FiniteGroupClass, IsClosedClass X ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ ¬ Group.IsNilpotent G) ∧
    ∀ A : Set SubgroupAssignment, (∀ τ ∈ A, IsClosedSubgroupFunctor X τ) →
      (∀ τ₁ ∈ A, ∀ τ₂ ∈ A, τ₁ ≠ τ₂ → ¬ FunctorLE X τ₁ τ₂) →
      Cardinal.mk A ≤ Cardinal.lift.{1} (Cardinal.mk (primesOf X))

/-- **Kourovka Problem 16.82 has a negative answer.** For a class $\mathfrak{X}$ of finite groups,
let $\pi(\mathfrak{X})$ be the set of primes dividing the order of some group in $\mathfrak{X}$,
and for subgroup assignments $\tau_1, \tau_2$ write $\tau_1 \le \tau_2$ on $\mathfrak{X}$ when
$\tau_1(G) \subseteq \tau_2(G)$ for every $G \in \mathfrak{X}$. There is no class $\mathfrak{X}$ of
finite groups that contains at least one group, is closed under homomorphic images, subgroups and
direct products, contains a non-nilpotent group, and has the following property: every set of
closed subgroup functors on $\mathfrak{X}$ in which no two distinct members $\tau_1, \tau_2$
satisfy $\tau_1 \le \tau_2$ on $\mathfrak{X}$ has cardinality at most $|\pi(\mathfrak{X})|$. In
other words, for every such class the lattice $F(\mathfrak{X})$ of closed subgroup functors on
$\mathfrak{X}$ has width greater than $|\pi(\mathfrak{X})|$.

The Kourovka Archive answers 16.82 "No such classes exist", citing Kamornikov (2010).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.82
(A. N. Skiba); resolution: S. F. Kamornikov, Siberian Math. J. 51 (2010), no. 5, 824-829, Kourovka
Archive, Problem 16.82 (No such classes exist).
-/
public theorem_wanted existsNonnilpotentClassOfSmallWidth_refuted :
    ¬ existsNonnilpotentClassOfSmallWidth

end MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82Wanted
