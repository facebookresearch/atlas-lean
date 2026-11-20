/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib



namespace StatMech.FrontierD



def FKRectHorizontalOddOrZero (u : Int × Int) : Prop :=
  u = 0 ∨ (u.2 = 0 ∧ Odd u.1)

theorem fkRectHorizontalOddOrZero_zero :
    FKRectHorizontalOddOrZero (0, 0) :=
  Or.inl rfl

theorem FKRectHorizontalOddOrZero.snd_eq_zero
    {u : Int × Int} (hu : FKRectHorizontalOddOrZero u) : u.2 = 0 := by
  rcases hu with rfl | hu
  · rfl
  · exact hu.1

theorem FKRectHorizontalOddOrZero.odd_fst_of_ne_zero
    {u : Int × Int} (hu : FKRectHorizontalOddOrZero u) (hne : u ≠ 0) :
    Odd u.1 := by
  rcases hu with hu | hu
  · exact absurd hu hne
  · exact hu.2




theorem fkRectHorizontalOddOrZero_add_eq_zero_of_both_ne_zero
    {u v : Int × Int}
    (hu : FKRectHorizontalOddOrZero u)
    (hv : FKRectHorizontalOddOrZero v)
    (hsum : FKRectHorizontalOddOrZero (u + v))
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    u + v = 0 := by
  by_contra huv0
  obtain ⟨a, ha⟩ := hu.odd_fst_of_ne_zero hu0
  obtain ⟨b, hb⟩ := hv.odd_fst_of_ne_zero hv0
  obtain ⟨c, hc⟩ := hsum.odd_fst_of_ne_zero huv0
  simp only [Prod.fst_add] at hc
  omega



theorem fkRectHorizontalOddOrZero_split_one_eq_zero
    {u v w : Int × Int}
    (hu : FKRectHorizontalOddOrZero u)
    (hv : FKRectHorizontalOddOrZero v)
    (hw : FKRectHorizontalOddOrZero w)
    (hu0 : u ≠ 0) (hsplit : u = v + w) :
    v = 0 ∨ w = 0 := by
  by_contra h
  push Not at h
  have hzero := fkRectHorizontalOddOrZero_add_eq_zero_of_both_ne_zero
    hv hw (hsplit ▸ hu) h.1 h.2
  exact hu0 (hsplit.trans hzero)

end StatMech.FrontierD
