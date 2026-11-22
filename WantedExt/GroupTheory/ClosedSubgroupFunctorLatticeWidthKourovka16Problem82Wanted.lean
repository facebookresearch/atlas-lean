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

/-- A class of finite groups in `Type`, as a predicate. -/
abbrev FiniteGroupClass : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Prop

/-- `X` is a nonempty class of finite groups closed under homomorphic images, subgroups and direct
products. -/
def IsClosedClass (X : FiniteGroupClass) : Prop :=
  (∃ (G : Type) (_ : Group G) (_ : Finite G), X G) ∧
    (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H] (f : G →* H),
      Function.Surjective f → X G → X H) ∧
    (∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), X G → X H) ∧
    ∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H], X G → X H → X (G × H)

/-- An assignment of a set `τ(G)` of subgroups to every finite group `G`. -/
abbrev SubgroupAssignment : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Set (Subgroup G)

/-- `τ` is a closed subgroup functor on `X` (A. N. Skiba): `G ∈ τ(G)` for `G ∈ X`; for every
epimorphism `φ : A → B` with `A, B ∈ X`, images of members of `τ(A)` lie in `τ(B)` and preimages of
members of `τ(B)` lie in `τ(A)`; and `τ(H) ⊆ τ(G)` for every `H ∈ τ(G)` (here `H ∈ X`, as `X` is
closed under subgroups). -/
def IsClosedSubgroupFunctor (X : FiniteGroupClass) (τ : SubgroupAssignment) : Prop :=
  (∀ (G : Type) [Group G] [Finite G], X G → ⊤ ∈ τ G) ∧
    (∀ (A B : Type) [Group A] [Finite A] [Group B] [Finite B] (φ : A →* B),
      Function.Surjective φ → X A → X B →
        (∀ H ∈ τ A, H.map φ ∈ τ B) ∧ ∀ T ∈ τ B, T.comap φ ∈ τ A) ∧
    ∀ (G : Type) [Group G] [Finite G], X G → ∀ H ∈ τ G, ∀ K ∈ τ H, K.map H.subtype ∈ τ G

/-- The order of the lattice `F(X)`: `τ₁ ≤ τ₂` iff `τ₁(G) ⊆ τ₂(G)` for every `G ∈ X`. -/
def FunctorLE (X : FiniteGroupClass) (τ₁ τ₂ : SubgroupAssignment) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], X G → τ₁ G ⊆ τ₂ G

/-- `π(X)`: the primes dividing the order of some group in `X`. -/
def primesOf (X : FiniteGroupClass) : Set ℕ :=
  {p | p.Prime ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ p ∣ Nat.card G}

/-- Kourovka 16.82 (A. N. Skiba): there is a class `X` of finite groups, closed under homomorphic
images, subgroups and direct products and containing a non-nilpotent group, such that the lattice
`F(X)` of closed subgroup functors on `X` has width at most `|π(X)|`: every antichain of `F(X)` has
at most `|π(X)|` elements. -/
def existsNonnilpotentClassOfSmallWidth : Prop :=
  ∃ X : FiniteGroupClass, IsClosedClass X ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ ¬ Group.IsNilpotent G) ∧
    ∀ A : Set SubgroupAssignment, (∀ τ ∈ A, IsClosedSubgroupFunctor X τ) →
      (∀ τ₁ ∈ A, ∀ τ₂ ∈ A, τ₁ ≠ τ₂ → ¬ FunctorLE X τ₁ τ₂) →
      Cardinal.mk A ≤ Cardinal.lift.{1} (Cardinal.mk (primesOf X))

/--
Resolved false: the Kourovka Archive answers 16.82 "No such classes exist", citing Kamornikov
(2010): for every non-nilpotent class `𝔛` of finite groups closed under homomorphic images,
subgroups and direct products, the lattice of closed subgroup functors on `𝔛` has width greater than
`|π(𝔛)|`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.82
(A. N. Skiba); resolution: S. F. Kamornikov, Siberian Math. J. 51 (2010), no. 5, 824-829, Kourovka
Archive, Problem 16.82 (No such classes exist).
-/
public theorem_wanted existsNonnilpotentClassOfSmallWidth_refuted :
    ¬ existsNonnilpotentClassOfSmallWidth

end MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82Wanted
