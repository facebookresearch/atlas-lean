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

/-- **Full automorphism group of a binary relation.** Let $G$ be a group, $Z$ a set and
$X \subseteq Z \times Z$ a binary relation on $Z$. Then $G$ is the full automorphism group of
$X$ when there is an injective group homomorphism $\varphi$ from $G$ to the group of
permutations of $Z$ whose image is exactly the set of permutations $f$ of $Z$ with
$(x, y) \in X \iff (f(x), f(y)) \in X$ for all $x, y \in Z$. -/
def IsAutomorphismGroupOf (G : Type u) [Group G] (Z : Type u) (X : Set (Z × Z)) :
    Prop :=
  ∃ φ : G → Equiv.Perm Z, Function.Injective φ ∧
    (∀ g h : G, φ (g * h) = φ g * φ h) ∧
    (∀ g : G, ∀ x y : Z, (x, y) ∈ X ↔ (φ g x, φ g y) ∈ X) ∧
    ∀ f : Equiv.Perm Z, (∀ x y : Z, (x, y) ∈ X ↔ (f x, f y) ∈ X) → ∃ g : G, φ g = f

/--
**Birkhoff's theorem: every group is the automorphism group of a binary relation.** For every
group $G$ there are a set $Z$ and a binary relation $X \subseteq Z \times Z$ such that $G$ is
the full automorphism group of $X$: there is an injective group homomorphism $\varphi$ from $G$
to the group of permutations of $Z$ whose image is exactly the set of permutations $f$ of $Z$
with $(x, y) \in X \iff (f(x), f(y)) \in X$ for all $x, y \in Z$.

The set $Z$ lies in the same universe as $G$.

Source: S. Ulam, Problem 142 of the Scottish Book, headed "Problem (Ulam) -
Theorem (Garrett Birkhoff)"; the representation is Birkhoff's theorem.
-/
theorem_wanted everyGroupIsAutomorphismGroupOfBinaryRelation :
    ∀ (G : Type u) [Group G], ∃ (Z : Type u) (X : Set (Z × Z)),
      IsAutomorphismGroupOf G Z X

end MathlibExt.GroupTheory.ScottishBook142Wanted
