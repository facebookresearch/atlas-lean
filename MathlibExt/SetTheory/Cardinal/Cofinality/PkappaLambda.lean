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
public import Mathlib.SetTheory.Ordinal.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 55, Logic 56
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal

-- Logic 55: Subsets of $lambda$ of size less than $\kappa$
def powersetCardLT.{u} (κ lam : Cardinal.{u}) : Set (Set (Set.Iio lam.ord)) :=
  {x | #x < Cardinal.lift.{u+1} κ}

theorem powersetCardLT_downward.{u} {κ lam : Cardinal.{u}}
    {x y : Set (Set.Iio lam.ord)}
    (hx : x ∈ powersetCardLT κ lam) (hyx : y ⊆ x) : y ∈ powersetCardLT κ lam :=
  lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hyx) hx

-- Logic 56: Club in P_κ(λ)
structure IsClubPowersetCardLT.{u} (κ lam : Cardinal.{u})
    (C : Set (Set (Set.Iio lam.ord))) : Prop where
  subset : C ⊆ powersetCardLT κ lam
  cofinal : ∀ x ∈ powersetCardLT κ lam, ∃ y ∈ C, x ⊆ y
  closed : ∀ D : Set (Set (Set.Iio lam.ord)), D ⊆ C → D.Nonempty →
    #D < Cardinal.lift.{u+1} κ → DirectedOn (· ⊆ ·) D → (⋃₀ D) ∈ C

theorem empty_mem_powersetCardLT.{u} {κ lam : Cardinal.{u}} (hκ : 0 < κ) :
    (∅ : Set (Set.Iio lam.ord)) ∈ powersetCardLT κ lam := by
  show #(∅ : Set (Set.Iio lam.ord)) < Cardinal.lift.{u+1} κ
  simpa using hκ

theorem IsClubPowersetCardLT.nonempty.{u} {κ lam : Cardinal.{u}}
    {C : Set (Set (Set.Iio lam.ord))}
    (h : IsClubPowersetCardLT κ lam C) (hκ : 0 < κ) : C.Nonempty := by
  obtain ⟨y, hy, _⟩ := h.cofinal ∅ (empty_mem_powersetCardLT hκ)
  exact ⟨y, hy⟩

end
