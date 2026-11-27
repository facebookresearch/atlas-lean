/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeThreeRelIso
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.OrderOfElement
import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphTypeTwo
import MathlibExt.NumberTheory.Digits.NegTwoCubeDvd
import MathlibExt.NumberTheory.Digits.NineDvdExponent
import MathlibExt.NumberTheory.Digits.PositiveTwoCubeDvd
import MathlibExt.NumberTheory.Digits.ThreePowCubeBound

/-! # Tests for Type 3 normal forms -/

namespace MathlibExtTest.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeThreeRelIso

open MetaMathlibExt

-- The rules -2m + 3 and -2m + 6 have loops at 1 and 2. Their normal form must
-- therefore have two distinct loops, forcing its odd offset to be divisible by 3.
example : (∃ a : ℕ, Odd a ∧ 3 ∣ a ∧
    Nonempty (ecsdAdj ![-2, -2] ![3, 6] ≃r ecsdAdj ![-2, -2] ![0, (a : ℤ)])) ∨
    (∃ a : ℕ, Even a ∧ a % 3 = 1 ∧
      Nonempty (ecsdAdj ![-2, -2] ![3, 6] ≃r ecsdAdj ![-2, -2] ![1, (a : ℤ)])) ∨
    ∃ a : ℤ, Even a ∧ a % 3 = 2 ∧
      Nonempty (ecsdAdj ![-2, -2] ![3, 6] ≃r ecsdAdj ![-2, -2] ![1, a]) := by
  rcases ecsd_type_three_relIso 3 6 ⟨-2, rfl⟩ with ⟨a, haOdd, ⟨e⟩⟩ | h | h
  · have loop1 := e.map_rel_iff.mpr ((ecsdAdj_two (-2) (-2) 3 6 1 1).mpr (Or.inl rfl))
    have loop2 := e.map_rel_iff.mpr ((ecsdAdj_two (-2) (-2) 3 6 2 2).mpr (Or.inr rfl))
    rw [ecsdAdj_two] at loop1 loop2
    have hne : e 1 ≠ e 2 := e.injective.ne (by decide)
    have h3dvd : 3 ∣ a := by omega
    exact Or.inl ⟨a, haOdd, h3dvd, ⟨e⟩⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

-- The rules -2m + 4 and -2m + 13 have no loops, ruling out the Type 3.1 form
-- whose first rule always loops at zero. The Type 3.2 witness exceeds one.
example : (∃ a : ℕ, Odd a ∧
    Nonempty (ecsdAdj ![-2, -2] ![4, 13] ≃r ecsdAdj ![-2, -2] ![0, (a : ℤ)])) ∨
    (∃ a : ℕ, Even a ∧ a % 3 = 1 ∧ 1 < a ∧
      Nonempty (ecsdAdj ![-2, -2] ![4, 13] ≃r ecsdAdj ![-2, -2] ![1, (a : ℤ)])) ∨
    ∃ a : ℤ, Even a ∧ a % 3 = 2 ∧
      Nonempty (ecsdAdj ![-2, -2] ![4, 13] ≃r ecsdAdj ![-2, -2] ![1, a]) := by
  rcases ecsd_type_three_relIso 4 13 ⟨-5, rfl⟩ with ⟨a, haOdd, ⟨e⟩⟩ | ⟨a, haEven, haMod, ⟨e⟩⟩ | h
  · exfalso
    have hloop_tgt : ecsdAdj ![-2, -2] ![0, (a : ℤ)] 0 0 :=
      (ecsdAdj_two (-2) (-2) 0 (a : ℤ) 0 0).mpr (Or.inl rfl)
    have hloop_src := e.symm.map_rel_iff.mpr hloop_tgt
    have hno : ∀ m : ℤ, ¬ ecsdAdj ![-2, -2] ![4, 13] m m := by
      intro m hm
      rw [ecsdAdj_two] at hm
      rcases hm with hm | hm <;> omega
    exact hno _ hloop_src
  · have h1lt : 1 < a := by
      obtain ⟨r, hr⟩ := haEven
      omega
    exact Or.inr (Or.inl ⟨a, haEven, haMod, h1lt, ⟨e⟩⟩)
  · exact Or.inr (Or.inr h)

-- The rules -2m + 4 and -2m + 11 have no loops, ruling out the Type 3.1 form.
-- The Type 3.3 witness is nonzero.
example : (∃ a : ℕ, Odd a ∧
    Nonempty (ecsdAdj ![-2, -2] ![4, 11] ≃r ecsdAdj ![-2, -2] ![0, (a : ℤ)])) ∨
    (∃ a : ℕ, Even a ∧ a % 3 = 1 ∧
      Nonempty (ecsdAdj ![-2, -2] ![4, 11] ≃r ecsdAdj ![-2, -2] ![1, (a : ℤ)])) ∨
    ∃ a : ℤ, Even a ∧ a % 3 = 2 ∧ a ≠ 0 ∧
      Nonempty (ecsdAdj ![-2, -2] ![4, 11] ≃r ecsdAdj ![-2, -2] ![1, a]) := by
  rcases ecsd_type_three_relIso 4 11 ⟨-4, rfl⟩ with ⟨a, haOdd, ⟨e⟩⟩ | h | ⟨a, haEven, haMod, ⟨e⟩⟩
  · exfalso
    have hloop_tgt : ecsdAdj ![-2, -2] ![0, (a : ℤ)] 0 0 :=
      (ecsdAdj_two (-2) (-2) 0 (a : ℤ) 0 0).mpr (Or.inl rfl)
    have hloop_src := e.symm.map_rel_iff.mpr hloop_tgt
    have hno : ∀ m : ℤ, ¬ ecsdAdj ![-2, -2] ![4, 11] m m := by
      intro m hm
      rw [ecsdAdj_two] at hm
      rcases hm with hm | hm <;> omega
    exact hno _ hloop_src
  · exact Or.inr (Or.inl h)
  · have hne : a ≠ 0 := by omega
    exact Or.inr (Or.inr ⟨a, haEven, haMod, hne, ⟨e⟩⟩)

end MathlibExtTest.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeThreeRelIso
