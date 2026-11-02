/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 1, Logic 42, Logic 52, Logic 53, Logic 2

/-!
# `MathlibExt.SetTheory.Cardinal.Cofinality.Stationary`

## References

* Jech (for `ContainsAllBounded`, `IsKappaCompleteIdeal`, `IsNormalIdeal`, `IsRegressive`)
-/

open Cardinal

namespace MetaMathlibExt

-- Logic 42: Contains all bounded sets

/-- A set X⊆κ is *bounded in κ* if there is some
β<κ with α<β for every α∈ X; equivalently,
X⊆β for some β<κ.

A family I⊆𝒫(κ) *contains all bounded sets*
if every bounded X⊆κ belongs to I:

  ∀ X ⊆ κ  [
    (∃ β < κ ∀ α ∈ X, α < β)
     ⟶  X ∈ I
   ].
-/
def ContainsAllBounded.{u} (κ : Cardinal.{u}) (I : Set (Set (Set.Iio κ.ord))) : Prop :=
  ∀ X : Set (Set.Iio κ.ord),
    (∃ β : Set.Iio κ.ord, ∀ α ∈ X, (α : Ordinal) < (β : Ordinal)) → X ∈ I

-- Logic 52: $\kappa$-complete ideal

/-- A *κ-complete ideal on κ* is a collection I ⊆ 𝒫(κ) such that:

1. ∅ ∈ I.
1. If A ∈ I and B ⊆ A, then B ∈ I.
1. κ ∉ I.
1. If λ < κ and ⟨ A_α : α < λ ⟩ is a sequence of members of I, then [ ⋃_{α < λ} A_α ∈ I. ]
-/
structure IsKappaCompleteIdeal.{u} (κ : Cardinal.{u})
    (I : Set (Set (Set.Iio κ.ord))) : Prop where
  downward : ∀ X ∈ I, ∀ Y ⊆ X, Y ∈ I
  empty_mem : (∅ : Set (Set.Iio κ.ord)) ∈ I
  univ_not_mem : (Set.univ : Set (Set.Iio κ.ord)) ∉ I
  kappa_complete : ∀ F : Set (Set (Set.Iio κ.ord)),
    #F < Cardinal.lift.{u+1} κ → (∀ X ∈ F, X ∈ I) → ⋃₀ F ∈ I

-- Logic 53: Normal ideal on $\kappa$

/-- Let κ be a cardinal, identified with
κ = Iio(κ.ord) = {α : Ordinal ∣ α < κ.ord},
and let I⊆𝒫(κ).

I is *normal* if it is closed under diagonal unions: for every
κ-sequence ⟨ A_ξ : ξ<κ⟩ with A_ξ∈ I,

  ∇_{ξ<κ} A_ξ := {α<κ ∣ ∃ ξ<α, α∈ A_ξ} ∈ I.

Formally,

  ∀ A : κ → 𝒫(κ),  (∀ ξ, A_ξ∈ I) →
  {α∈κ ∣ ∃ ξ∈κ, ξ<α ∧ α∈ A_ξ}∈ I.
-/
def IsNormalIdeal.{u} (κ : Cardinal.{u}) (I : Set (Set (Set.Iio κ.ord))) : Prop :=
  ∀ (A : Set.Iio κ.ord → Set (Set.Iio κ.ord)),
    (∀ ξ, A ξ ∈ I) →
    {α : Set.Iio κ.ord | ∃ ξ : Set.Iio κ.ord, (ξ : Ordinal) < α ∧ α ∈ A ξ} ∈ I

-- Logic 2: Regressive function

/-- **Regressive functions.** Let $\kappa$ be a cardinal, identified with its initial ordinal, let
$S$ be a set of ordinals less than $\kappa$, and let $f$ be a function from $S$ to the ordinals
less than $\kappa$. Then $f$ is regressive if $f(\alpha) < \alpha$ for every nonzero
$\alpha \in S$.
-/
def IsRegressive (κ : Cardinal)
    (S : Set (Set.Iio κ.ord)) (f : ↥S → Set.Iio κ.ord) : Prop :=
  ∀ x : ↥S, (x : Ordinal) ≠ 0 → (f x : Ordinal) < (x : Ordinal)

end MetaMathlibExt

end
