/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusNet









namespace StatMech.FrontierD


def FKRectPrimitiveWinding (w : Int × Int) : Prop :=
  ∃ a b : Int, a * w.1 + b * w.2 = 1



theorem snd_dvd_of_primitive_of_not_windingIndependent
    {w u : Int × Int} (hprimitive : FKRectPrimitiveWinding w)
    (hdependent : ¬ FKRectWindingIndependent w u) :
    w.2 ∣ u.2 := by
  rcases hprimitive with ⟨a, b, hab⟩
  unfold FKRectWindingIndependent at hdependent
  push Not at hdependent
  refine ⟨a * u.1 + b * u.2, ?_⟩
  calc
    u.2 = (a * w.1 + b * w.2) * u.2 := by rw [hab]; ring
    _ = w.2 * (a * u.1 + b * u.2) := by
      linear_combination a * hdependent



theorem windingIndependent_of_primitive_of_snd_between
    {w u : Int × Int} (hprimitive : FKRectPrimitiveWinding w)
    (hw : 0 < w.2) (hu0 : 0 < u.2) (huk : u.2 < w.2) :
    FKRectWindingIndependent w u := by
  by_contra hdependent
  obtain ⟨q, hq⟩ :=
    snd_dvd_of_primitive_of_not_windingIndependent
      hprimitive hdependent
  have hqpos : 0 < q := by
    nlinarith
  have hqone : 1 ≤ q := hqpos
  nlinarith


theorem windingIndependent_of_primitive_of_snd_between_neg
    {w u : Int × Int} (hprimitive : FKRectPrimitiveWinding w)
    (hw : w.2 < 0) (hwu : w.2 < u.2) (hu0 : u.2 < 0) :
    FKRectWindingIndependent w u := by
  by_contra hdependent
  obtain ⟨q, hq⟩ :=
    snd_dvd_of_primitive_of_not_windingIndependent
      hprimitive hdependent
  have hqpos : 0 < q := by
    nlinarith
  have hqone : 1 ≤ q := hqpos
  nlinarith



theorem eq_of_primitive_of_primitive_of_not_windingIndependent_of_sameSign
    {u v : Int × Int} (hu : FKRectPrimitiveWinding u)
    (hv : FKRectPrimitiveWinding v)
    (hdep : ¬ FKRectWindingIndependent u v)
    (hsign : 0 < u.1 * v.1 ∨ 0 < u.2 * v.2) :
    u = v := by
  rcases hu with ⟨a, b, hab⟩
  rcases hv with ⟨c, d, hcd⟩
  unfold FKRectWindingIndependent at hdep
  push Not at hdep
  let q := a * v.1 + b * v.2
  have hvfst : v.1 = q * u.1 := by
    dsimp only [q]
    calc
      v.1 = (a * u.1 + b * u.2) * v.1 := by rw [hab]; ring
      _ = (a * v.1 + b * v.2) * u.1 := by
        linear_combination -b * hdep
  have hvsnd : v.2 = q * u.2 := by
    dsimp only [q]
    calc
      v.2 = (a * u.1 + b * u.2) * v.2 := by rw [hab]; ring
      _ = (a * v.1 + b * v.2) * u.2 := by
        linear_combination a * hdep
  have hqunit : q * (c * u.1 + d * u.2) = 1 := by
    calc
      q * (c * u.1 + d * u.2) = c * v.1 + d * v.2 := by
        rw [hvfst, hvsnd]
        ring
      _ = 1 := hcd
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hqunit with hq | hq
  · apply Prod.ext
    · rw [hvfst, hq]
      simp
    · rw [hvsnd, hq]
      simp
  · exfalso
    rcases hsign with hsign | hsign
    · rw [hvfst, hq] at hsign
      nlinarith [sq_nonneg u.1]
    · rw [hvsnd, hq] at hsign
      nlinarith [sq_nonneg u.2]



theorem eq_or_eq_neg_of_primitive_of_primitive_of_not_windingIndependent
    {u v : Int × Int} (hu : FKRectPrimitiveWinding u)
    (hv : FKRectPrimitiveWinding v)
    (hdep : ¬ FKRectWindingIndependent u v) :
    v = u ∨ v = -u := by
  rcases hu with ⟨a, b, hab⟩
  rcases hv with ⟨c, d, hcd⟩
  unfold FKRectWindingIndependent at hdep
  push Not at hdep
  let q := a * v.1 + b * v.2
  have hvfst : v.1 = q * u.1 := by
    dsimp only [q]
    calc
      v.1 = (a * u.1 + b * u.2) * v.1 := by rw [hab]; ring
      _ = (a * v.1 + b * v.2) * u.1 := by
        linear_combination -b * hdep
  have hvsnd : v.2 = q * u.2 := by
    dsimp only [q]
    calc
      v.2 = (a * u.1 + b * u.2) * v.2 := by rw [hab]; ring
      _ = (a * v.1 + b * v.2) * u.2 := by
        linear_combination a * hdep
  have hqunit : q * (c * u.1 + d * u.2) = 1 := by
    calc
      q * (c * u.1 + d * u.2) = c * v.1 + d * v.2 := by
        rw [hvfst, hvsnd]
        ring
      _ = 1 := hcd
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hqunit with hq | hq
  · left
    apply Prod.ext
    · rw [hvfst, hq]
      simp
    · rw [hvsnd, hq]
      simp
  · right
    apply Prod.ext
    · rw [hvfst, hq]
      simp
    · rw [hvsnd, hq]
      simp




theorem primitiveWinding_split_eq_zero_or_eq
    {u v w : Int × Int} (hu : FKRectPrimitiveWinding u)
    (hsum : u = v + w)
    (hv : v = 0 ∨ FKRectPrimitiveWinding v)
    (hw : w = 0 ∨ FKRectPrimitiveWinding w)
    (hdepv : ¬ FKRectWindingIndependent u v)
    (hdepw : ¬ FKRectWindingIndependent u w) :
    (v = 0 ∧ w = u) ∨ (v = u ∧ w = 0) := by
  have hune : u ≠ 0 := by
    rintro rfl
    rcases hu with ⟨a, b, h⟩
    norm_num [FKRectPrimitiveWinding] at h
  rcases hv with rfl | hv
  · left
    constructor
    · rfl
    · simpa using hsum.symm
  rcases hw with rfl | hw
  · right
    constructor
    · simpa using hsum.symm
    · rfl
  have hvsign :=
    eq_or_eq_neg_of_primitive_of_primitive_of_not_windingIndependent
      hu hv hdepv
  have hwsign :=
    eq_or_eq_neg_of_primitive_of_primitive_of_not_windingIndependent
      hu hw hdepw
  have hfst := congrArg Prod.fst hsum
  have hsnd := congrArg Prod.snd hsum
  simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
  rcases hvsign with hvsign | hvsign <;>
    rcases hwsign with hwsign | hwsign <;>
    rw [hvsign, hwsign] at hfst hsnd
  all_goals
    try simp only [Prod.fst_neg, Prod.snd_neg] at hfst hsnd
    exfalso
    apply hune
    apply Prod.ext
    · simpa only [Prod.fst_zero] using (show u.1 = 0 by omega)
    · simpa only [Prod.snd_zero] using (show u.2 = 0 by omega)



theorem not_primitiveWinding_add_self (u : Int × Int) :
    ¬ FKRectPrimitiveWinding (u + u) := by
  rintro ⟨a, b, h⟩
  simp only [Prod.fst_add, Prod.snd_add] at h
  have heven : 2 * (a * u.1 + b * u.2) = 1 := by
    linear_combination h
  omega



theorem not_primitiveWinding_add_of_primitive_dependent_sameSign
    {u v : Int × Int} (hu : FKRectPrimitiveWinding u)
    (hv : FKRectPrimitiveWinding v)
    (hdep : ¬ FKRectWindingIndependent u v)
    (hsign : 0 < u.1 * v.1 ∨ 0 < u.2 * v.2) :
    ¬ FKRectPrimitiveWinding (u + v) := by
  rw [eq_of_primitive_of_primitive_of_not_windingIndependent_of_sameSign
    hu hv hdep hsign]
  exact not_primitiveWinding_add_self v

end StatMech.FrontierD
