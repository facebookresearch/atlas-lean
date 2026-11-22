/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The cardinal p_p equals t (Tsaban, Problem 11.4)

B. Tsaban, Selection principles and special sets of reals, Problem 11.4: for a cardinal `κ > 1`,
`𝔭_κ` is the minimal cardinality of a centered subset of `[ℕ]^∞` which cannot be partitioned into
less than `κ` sets each having a pseudo-intersection; then `𝔭 = 𝔭_{ℵ₁} ≤ 𝔭_{ℵ₂} ≤ ... ≤ 𝔭_𝔱 = 𝔱`. Is
`𝔭_𝔭 = 𝔱`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace MathlibExt.Logic.PseudointersectionHierarchyAMR133Problem0046Wanted

/-!
Source: B. Tsaban, Selection principles and special sets of reals, in Open Problems in Topology II
(E. Pearl, ed.), Elsevier 2007, 91-108; revised version arXiv:math/0609601, Problem 11.4.
UnsolvedMath record UM-00800620 (`AMR-133-0046`), dataset ulamai/UnsolvedMath v1.8.0.

A centered family is a family of infinite subsets of `ℕ` all of whose finite subfamilies have
infinite intersection; a pseudo-intersection of `𝓕` is an infinite `B` with `B \ A` finite for all
`A ∈ 𝓕`. `𝔭` is the least size of a centered family without a pseudo-intersection, `𝔱` the least
size of a family of infinite sets linearly quasi-ordered by `⊆*` without a pseudo-intersection, and
a partition of `𝓕` into fewer than `κ` sets is a map from `𝓕` to an index type of size `< κ` (empty
pieces have pseudo-intersections). Cardinals live in `Cardinal.{0}`. `𝔭` is the same cardinal as
`pseudoIntersectionNumber` in the OpenConjectures entry `AMR133Problem19` (WantedExt cannot import
OpenConjectures).
-/

/-- `B` is a pseudo-intersection of `𝓕`: `B` is infinite and `B \ A` is finite for every `A ∈ 𝓕`. -/
def IsPseudoIntersection (B : Set ℕ) (𝓕 : Set (Set ℕ)) : Prop :=
  B.Infinite ∧ ∀ A ∈ 𝓕, (B \ A).Finite

/-- `𝓕` is a centered family of infinite sets: every finite subfamily (including singletons) has
infinite intersection. -/
def IsCentered (𝓕 : Set (Set ℕ)) : Prop :=
  ∀ 𝓖 : Finset (Set ℕ), (𝓖 : Set (Set ℕ)) ⊆ 𝓕 → (⋂ A ∈ 𝓖, A).Infinite

/-- The pseudo-intersection number `𝔭`: the least size of a centered family of infinite subsets of
`ℕ` without a pseudo-intersection. -/
noncomputable def pseudoIntersectionNumber : Cardinal :=
  sInf {κ | ∃ 𝓕 : Set (Set ℕ), IsCentered 𝓕 ∧ (¬ ∃ B, IsPseudoIntersection B 𝓕) ∧
    Cardinal.mk 𝓕 = κ}

/-- The tower number `𝔱`: the least size of a family of infinite subsets of `ℕ` that is linearly
quasi-ordered by almost inclusion `⊆*` and has no pseudo-intersection. -/
noncomputable def towerNumber : Cardinal :=
  sInf {κ | ∃ 𝓣 : Set (Set ℕ), (∀ A ∈ 𝓣, A.Infinite) ∧
    (∀ A ∈ 𝓣, ∀ B ∈ 𝓣, (A \ B).Finite ∨ (B \ A).Finite) ∧ (¬ ∃ C, IsPseudoIntersection C 𝓣) ∧
      Cardinal.mk 𝓣 = κ}

/-- `𝔭_κ`: the least size of a centered family of infinite subsets of `ℕ` that cannot be
partitioned into fewer than `κ` pieces each having a pseudo-intersection (every map `c` from the
family to an index type of size `< κ` has a fibre without a pseudo-intersection). -/
noncomputable def pKappa (κ : Cardinal) : Cardinal :=
  sInf {μ | ∃ 𝓕 : Set (Set ℕ), IsCentered 𝓕 ∧ Cardinal.mk 𝓕 = μ ∧
    ∀ (I : Type) (c : 𝓕 → I), Cardinal.mk I < κ →
      ∃ i, ¬ ∃ B, IsPseudoIntersection B {A | ∃ h : A ∈ 𝓕, c ⟨A, h⟩ = i}}

/-- Tsaban, Problem 11.4: `𝔭_𝔭 = 𝔱`. -/
def pKappaAtPEqualsT : Prop :=
  pKappa pseudoIntersectionNumber = towerNumber

/--
Resolved true: Malliaris and Shelah proved `𝔭 = 𝔱` in ZFC (Theorem 14.1), and the problem list
states `𝔭_𝔱 = 𝔱`, so `𝔭_𝔭 = 𝔭_𝔱 = 𝔱`. Source: B. Tsaban, Selection principles and special sets of
reals, in Open Problems in Topology II (E. Pearl, ed.), Elsevier 2007, 91-108; revised version
arXiv:math/0609601, Problem 11.4; resolution: M. Malliaris and S. Shelah, Cofinality spectrum
theorems in model theory, set theory, and general topology, J. Amer. Math. Soc. 29 (2016), 237-297,
arXiv:1208.5424, Theorem 14.1: 𝔭 = 𝔱 (in ZFC); the problem list (Section 11) states 'It is easy to
see that 𝔭 = 𝔭_2 = 𝔭_3 = ... = 𝔭_{ℵ₀}, and 𝔭_𝔱 = 𝔱', so 𝔭 = 𝔱 gives 𝔭_𝔭 = 𝔭_𝔱 = 𝔱,
https://arxiv.org/abs/1208.5424.
-/
public theorem_wanted pKappaAtPEqualsT_holds : pKappaAtPEqualsT

end MathlibExt.Logic.PseudointersectionHierarchyAMR133Problem0046Wanted
