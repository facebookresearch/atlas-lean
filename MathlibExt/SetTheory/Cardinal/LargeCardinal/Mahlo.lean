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
public import MathlibExt.SetTheory.Cardinal.LargeCardinal.Inaccessible
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 28, Logic 30
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal

-- Logic 28: Mahlo cardinal
def IsMahlo.{u} (κ : Cardinal.{u}) : Prop :=
  Cardinal.IsInaccessible κ ∧ IsStationary (inaccessibleBelow κ)

theorem not_isMahlo_of_least.{u} (κ : Cardinal.{u}) (_hκ : κ.IsInaccessible)
    (hmin : ∀ c : Cardinal.{u}, c.IsInaccessible → κ ≤ c) :
    ¬ IsMahlo κ := by
  rintro ⟨-, hstat⟩
  obtain ⟨α, ⟨hα1, -⟩, -⟩ := hstat (IsClub.univ)
  exact absurd (Cardinal.lt_ord.1 α.2) (not_lt.2 (hmin _ hα1))

-- Logic 30: Weakly Mahlo cardinal
def IsWeaklyMahlo.{u} (κ : Cardinal.{u}) : Prop :=
  IsWeaklyInaccessible κ ∧
  IsStationary {α : Set.Iio κ.ord | (α.val.card).IsRegular ∧ α.val.card.ord = α.val}

theorem regularBelow_excludes_succ.{u} (κ c : Cardinal.{u}) (hc : c.IsRegular)
    (h₀ : c.ord < κ.ord) (h₁ : c.ord + 1 < κ.ord) :
    (⟨c.ord, h₀⟩ : Set.Iio κ.ord) ∈
        {α : Set.Iio κ.ord | (α.val.card).IsRegular ∧ α.val.card.ord = α.val} ∧
      (⟨c.ord + 1, h₁⟩ : Set.Iio κ.ord) ∉
        {α : Set.Iio κ.ord | (α.val.card).IsRegular ∧ α.val.card.ord = α.val} := by
  have hcard : (c.ord + 1).card = c := by
    rw [Ordinal.card_add, Cardinal.card_ord, Ordinal.card_one,
      Cardinal.add_one_of_aleph0_le hc.aleph0_le]
  refine ⟨⟨by rw [Cardinal.card_ord]; exact hc, by rw [Cardinal.card_ord]⟩, ?_⟩
  rintro ⟨-, h2⟩
  rw [show ((⟨c.ord + 1, h₁⟩ : Set.Iio κ.ord) : Ordinal) = c.ord + 1 from rfl, hcard] at h2
  exact absurd h2 (by simp)

theorem not_isWeaklyMahlo_aleph_one.{u} : ¬ IsWeaklyMahlo (ℵ₁ : Cardinal.{u}) := by
  rintro ⟨⟨-, -, hlim⟩, -⟩
  rw [← succ_aleph0] at hlim
  exact Order.not_isSuccLimit_succ _ hlim

end
