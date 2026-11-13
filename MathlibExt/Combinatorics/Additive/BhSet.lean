/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.List.Permutation

/-!
# `B_h`-sets

This file defines `B_h`-sets following Nathanson,
"`B_h`-sets of real and complex numbers" (<https://arxiv.org/abs/2502.21272v3>,
lines 197–203 and 230–235): a nonempty subset `A` of an additive commutative
semigroup, with `h` positive, such that any two sums of exactly `h`
(not necessarily distinct) elements of `A` that agree must use the same
summands up to permutation.

No zero or identity is assumed: the ambient type is only an
`AddCommSemigroup`, and sums of representations are computed with
`AdditiveCombinatorics.sumNE`, which folds `+` over the tail starting from
the head, so the theory applies to genuine semigroups.

## Main definitions

* `AdditiveCombinatorics.sumNE`: sum of a nonempty list.
* `AdditiveCombinatorics.sumNE_proof_irrel`: the nonemptiness proof does not
  affect the sum.
* `AdditiveCombinatorics.IsBhSet`: the `B_h`-set predicate.
-/

@[expose] public section

namespace AdditiveCombinatorics

/-- **Sum of a nonempty list.** For a nonempty list $(a_1, \dots, a_k)$ of elements of a type with
an addition, its sum is obtained by adding the entries from left to right starting from the head:
it is $a_1$ when $k = 1$, and $(\cdots((a_1 + a_2) + a_3) + \cdots) + a_k$ in general. No zero
element is needed, and the proof that the list is nonempty does not affect the value. -/
public def sumNE {G : Type*} [Add G] : (l : List G) → l ≠ [] → G
  | [], h => absurd rfl h
  | a :: t, _ => t.foldl (· + ·) a

/-- **The sum of a nonempty list does not depend on the nonemptiness proof.** For every list $l$
of elements of a type with an addition and any two proofs $e_1$ and $e_2$ that $l$ is nonempty,
the sum of $l$ computed with $e_1$ equals the sum of $l$ computed with $e_2$. -/
public theorem sumNE_proof_irrel {G : Type*} [Add G] (l : List G) (e₁ e₂ : l ≠ []) :
    sumNE l e₁ = sumNE l e₂ := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

/-- **$B_h$-set.** Let $G$ be an additive commutative semigroup, $A \subseteq G$ and $h$ a natural
number. $A$ is a $B_h$-set if $A$ is nonempty, $h \ge 1$, and whenever two sequences
$(a_1, \dots, a_h)$ and $(b_1, \dots, b_h)$ of elements of $A$ satisfy
$a_1 + \dots + a_h = b_1 + \dots + b_h$, the sequence $(b_1, \dots, b_h)$ is a rearrangement of
$(a_1, \dots, a_h)$.

Repeated summands are allowed: the entries of each sequence need not be distinct. No zero element
is assumed. -/
public def IsBhSet {G : Type*} [AddCommSemigroup G] (A : Set G) (h : ℕ) : Prop :=
  A.Nonempty ∧ 0 < h ∧
    ∀ (l₁ l₂ : List G),
      (∀ x ∈ l₁, x ∈ A) →
      (∀ x ∈ l₂, x ∈ A) →
      l₁.length = h →
      l₂.length = h →
      ∀ (e₁ : l₁ ≠ []) (e₂ : l₂ ≠ []),
        sumNE l₁ e₁ = sumNE l₂ e₂ → l₁.Perm l₂

end AdditiveCombinatorics
