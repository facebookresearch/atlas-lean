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

public import MathlibExt.SetTheory.Cardinal.LargeCardinal.Mahlo
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

@[expose] public section

open Cardinal Ordinal

namespace MathlibExtTest.SetTheory.Cardinal.LargeCardinal.Mahlo

open MetaMathlibExt

-- Logic 28: Mahlo cardinal

/-- Sanity check: the least inaccessible is not Mahlo.

This targets the stationarity conjunct.  With no inaccessible below `κ`, the set
`inaccessibleBelow κ` is empty, and the empty set meets no club — in particular
not `Set.univ`.  So the second conjunct is not implied by the first and is not
vacuously satisfiable: it genuinely demands inaccessibles below `κ`. -/

theorem not_isMahlo_of_least.{u} (κ : Cardinal.{u}) (_hκ : κ.IsInaccessible)
    (hmin : ∀ c : Cardinal.{u}, c.IsInaccessible → κ ≤ c) :
    ¬ IsMahlo κ := by
  rintro ⟨-, hstat⟩
  obtain ⟨α, ⟨hα1, -⟩, -⟩ := hstat (IsClub.univ)
  exact absurd (Cardinal.lt_ord.1 α.2) (not_lt.2 (hmin _ hα1))

/-- Companion: the least inaccessible is not an inaccessible fixed point either. -/

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

-- Logic 30: Weakly Mahlo cardinal

/-- Check A: the `α.val.card.ord = α.val` clause is load-bearing.  Both `c.ord` and
`c.ord + 1` have regular cardinality, but only `c.ord` is in the stationary set's
carrier — without the clause each regular `c < κ` would drag all of `[c, c⁺)` in. -/

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

/-- Check B: `ℵ₁` is not weakly Mahlo — it fails the
weak inaccessibility conjunct. -/

theorem not_isWeaklyMahlo_aleph_one.{u} : ¬ IsWeaklyMahlo (ℵ₁ : Cardinal.{u}) := by
  rintro ⟨⟨-, -, hlim⟩, -⟩
  rw [← succ_aleph0] at hlim
  exact Order.not_isSuccLimit_succ _ hlim

end MathlibExtTest.SetTheory.Cardinal.LargeCardinal.Mahlo

end
