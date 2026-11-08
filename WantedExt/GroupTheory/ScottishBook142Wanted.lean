/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Defs
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook142Wanted

universe u

/-- `G` is the full automorphism group of the binary relation `X` on `Z`:
there is an injective homomorphism from `G` into the permutation group of
`Z` whose image is exactly the set of permutations preserving `X`. -/
def IsAutomorphismGroupOf (G : Type u) [Group G] (Z : Type u) (X : Set (Z × Z)) :
    Prop :=
  ∃ φ : G → Equiv.Perm Z, Function.Injective φ ∧
    (∀ g h : G, φ (g * h) = φ g * φ h) ∧
    (∀ g : G, ∀ x y : Z, (x, y) ∈ X ↔ (φ g x, φ g y) ∈ X) ∧
    ∀ f : Equiv.Perm Z, (∀ x y : Z, (x, y) ∈ X ↔ (f x, f y) ∈ X) → ∃ g : G, φ g = f

/--
Every abstract group is the group of all injective transformations of some
set preserving some binary relation: for every group `G` there are a set
`Z` and a subset `X` of `Z × Z` such that `G` is isomorphic to the
automorphism group of the binary relation `X` on `Z`.
Source: S. Ulam, Problem 142 of the Scottish Book, headed "Problem (Ulam) -
Theorem (Garrett Birkhoff)"; the representation is Birkhoff's theorem.
-/
theorem_wanted everyGroupIsAutomorphismGroupOfBinaryRelation :
    ∀ (G : Type u) [Group G], ∃ (Z : Type u) (X : Set (Z × Z)),
      IsAutomorphismGroupOf G Z X

end MathlibExt.GroupTheory.ScottishBook142Wanted
