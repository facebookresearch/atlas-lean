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

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import MathlibExt.SetTheory.Cardinal.Cofinality.Stationary

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 4, Logic 5

open Cardinal Ordinal

namespace MetaMathlibExt

-- Logic 4: Diamond ($\Diamond$)

/-- ◇_κ holds iff there is a sequence ⟨ S_α : α < κ⟩ with S_α ⊆ α for all α < κ, such that for every
X ⊆ κ, {α < κ : X ∩ α = S_α} is stationary in κ.
-/
def Diamond.{u} (κ : Cardinal.{u}) : Prop :=
  ∃ S : Set.Iio κ.ord → Set Ordinal.{u},
    (∀ α : Set.Iio κ.ord, S α ⊆ Set.Iio (α : Ordinal.{u})) ∧
    (∀ X : Set (Set.Iio κ.ord),
      IsStationary {α : Set.Iio κ.ord |
        (Subtype.val '' X) ∩ Set.Iio (α : Ordinal.{u}) = S α})

-- Logic 5: Weak Diamond ($\Diamond^-$)

/-- ◇⁻_κ holds iff there is a sequence ⟨ 𝒜_α : α < κ⟩ with each 𝒜_α ⊆ 𝒫(α) and |𝒜_α| ≤ |α|, such
that for every X ⊆ κ the set {α < κ : X ∩ α ∈ 𝒜_α} is stationary in κ.
-/
def DiamondMinus.{u} (κ : Cardinal.{u}) : Prop :=
  ∃ A : Set.Iio κ.ord → Set (Set Ordinal.{u}),
    (∀ α : Set.Iio κ.ord,
      (∀ s ∈ A α, s ⊆ Set.Iio (α : Ordinal.{u})) ∧
      #(A α) ≤ #(Set.Iio (α : Ordinal.{u}))) ∧
    (∀ X : Set (Set.Iio κ.ord),
      IsStationary {α : Set.Iio κ.ord |
        (Subtype.val '' X) ∩ Set.Iio (α : Ordinal.{u}) ∈ A α})

end MetaMathlibExt

end
