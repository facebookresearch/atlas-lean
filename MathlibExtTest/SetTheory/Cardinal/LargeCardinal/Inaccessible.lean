/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner, Nam Trang
-/
module

public import MathlibExt.SetTheory.Cardinal.LargeCardinal.Inaccessible
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.Cardinal.LargeCardinal.Inaccessible

open MetaMathlibExt

-- Logic 29: Weakly inaccessible cardinal

/-- Sanity check: `ℵ₁` is uncountable and regular but not weakly inaccessible.
This isolates the limit-cardinal clause — `ℵ₁` satisfies the other two, so drop
`Order.IsSuccLimit` and this becomes unprovable. -/

theorem not_isWeaklyInaccessible_aleph_one.{u} :
    ℵ₀ < (ℵ₁ : Cardinal.{u}) ∧ (ℵ₁ : Cardinal.{u}).IsRegular ∧
      ¬ IsWeaklyInaccessible (ℵ₁ : Cardinal.{u}) := by
  refine ⟨aleph0_lt_aleph_one, isRegular_aleph_one, ?_⟩
  rintro ⟨-, -, hlim⟩
  rw [← succ_aleph0] at hlim
  exact Order.not_isSuccLimit_succ _ hlim

-- Logic 26: Set of inaccessible cardinality below κ

/-- Sanity check: `inaccessibleBelow κ` really is the set of *inaccessible cardinals*
below `κ`, not the larger set of ordinals whose *cardinality* happens to be
inaccessible. -/

theorem inaccessibleBelow_excludes_succ.{u} (κ c : Cardinal.{u}) (hc : c.IsInaccessible)
    (h₀ : c.ord < κ.ord) (h₁ : c.ord + 1 < κ.ord) :
    (⟨c.ord, h₀⟩ : Set.Iio κ.ord) ∈ inaccessibleBelow κ ∧
    (⟨c.ord + 1, h₁⟩ : Set.Iio κ.ord) ∉ inaccessibleBelow κ := by
  have hinf : ℵ₀ ≤ c := le_of_lt hc.1
  have hcard : (c.ord + 1).card = c := by
    rw [Ordinal.card_add, Cardinal.card_ord, Ordinal.card_one,
        Cardinal.add_one_of_aleph0_le hinf]
  refine ⟨⟨by rw [Cardinal.card_ord]; exact hc, by rw [Cardinal.card_ord]⟩, ?_⟩
  rintro ⟨-, h2⟩
  rw [show ((⟨c.ord + 1, h₁⟩ : Set.Iio κ.ord) : Ordinal) = c.ord + 1 from rfl,
      hcard] at h2
  -- h2 : c.ord = c.ord + 1
  exact absurd h2 (by simp)

-- Logic 27: Inaccessible fixed point

/-- Sanity check: the least inaccessible is not an inaccessible fixed point.
This targets the order-type conjunct.  If `κ` is inaccessible with no inaccessible
below it, then `inaccessibleBelow κ` is empty and its order type is `0`, whereas
`κ.ord ≠ 0`.  So the second conjunct is not implied by the first, and it is not
vacuously satisfiable: it genuinely demands `κ`-many inaccessibles below `κ`. -/

theorem not_isInaccessibleFixedPoint_of_least.{u} (κ : Cardinal.{u}) (hκ : κ.IsInaccessible)
    (hmin : ∀ c : Cardinal.{u}, c.IsInaccessible → κ ≤ c) :
    ¬ IsInaccessibleFixedPoint κ := by
  rintro ⟨-, h⟩
  have hempty : IsEmpty ↥(inaccessibleBelow κ) := by
    constructor
    rintro ⟨α, hα1, -⟩
    exact absurd (Cardinal.lt_ord.1 α.2) (not_lt.2 (hmin _ hα1))
  rw [Ordinal.type_eq_zero_iff_isEmpty.2 hempty] at h
  have hord : κ.ord = 0 := Ordinal.lift_inj.1 (h.trans Ordinal.lift_zero.symm)
  rw [Cardinal.ord_eq_zero] at hord
  exact absurd hord hκ.pos.ne'

end MathlibExtTest.SetTheory.Cardinal.LargeCardinal.Inaccessible

end
