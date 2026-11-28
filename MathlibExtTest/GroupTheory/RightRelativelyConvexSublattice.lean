/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import MathlibExt.GroupTheory.RightRelativelyConvexSublattice

open MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted
open MathlibExt.GroupTheory.RightRelativelyConvexSublatticeKourovka21Problem147Wanted

-- The trivial subgroup is convex in any witnessing order.
example {G : Type} [Group G] (h : IsRightOrderable G) :
    IsRightRelativelyConvex (⊥ : Subgroup G) := by
  obtain ⟨o, hi⟩ := h
  refine ⟨o, fun a b hab c => hi a b c hab, ?_⟩
  intro a ha b hb g hag hgb
  rw [Subgroup.mem_bot.mp ha] at hag
  rw [Subgroup.mem_bot.mp hb] at hgb
  exact Subgroup.mem_bot.mpr (o.le_antisymm g 1 hgb hag)

-- In either orientation of a right order on ℤ, 1 is between the even integers 0 and 2.
example : ¬ IsRightRelativelyConvex (AddSubgroup.zmultiples (2 : ℤ)).toSubgroup := by
  rintro ⟨o, hi, hc⟩
  let e := Multiplicative.ofAdd (1 : ℤ)
  let H := (AddSubgroup.zmultiples (2 : ℤ)).toSubgroup
  have he : e ∉ H := by
    change (1 : ℤ) ∉ AddSubgroup.zmultiples 2
    rw [Int.mem_zmultiples_iff]
    decide
  have hsq : e * e ∈ H := AddSubgroup.mem_zmultiples (2 : ℤ)
  rcases o.le_total 1 e with h | h
  · exact he (hc 1 H.one_mem (e * e) hsq e h (by simpa using hi 1 e h e))
  · exact he (hc (e * e) hsq 1 H.one_mem e (by simpa using hi e 1 h e) h)
