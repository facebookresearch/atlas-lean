/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusAxisMonotonicity

open Finset

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}








theorem isingTorusTwoPoint_le_axis_of_coordinate_eq
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (z : IsingDyadicTorus d k) (r : Nat)
    (hr : r < 2 ^ (k + 1))
    (hz : z i = (r : ZMod (2 ^ (k + 2)))) :
    isingTorusTwoPoint beta 0 z <=
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) := by
  by_cases hr0 : r = 0
  · subst r
    have hshift : isingTorusCoordinateShift (k := k) i 0 = 0 := by
      funext j
      simp [isingTorusCoordinateShift]
    rw [hshift]
    calc
      isingTorusTwoPoint beta 0 z <= 1 :=
        isingTorusTwoPoint_le_one beta 0 z
      _ = isingTorusTwoPoint beta 0 0 := by
        rw [isingTorusTwoPoint_eq_twoPointJ_unitEdge, twoPointJ_self]
  by_cases heven : r % 2 = 0
  · let q := r / 2
    have hrq : r = 2 * q := by
      dsimp only [q]
      omega
    have hq0 : 0 < q := by omega
    have hqhalf : q < 2 ^ (k + 1) := by omega
    let x0 : IsingDyadicTorus d k :=
      Function.update z i (q : ZMod (2 ^ (k + 2)))
    let y0 : IsingDyadicTorus d k := isingTorusCoordinateShift i q
    have hxmem : isingTorusInStrictLower i x0 := by
      unfold isingTorusInStrictLower
      dsimp only [x0]
      rw [Function.update_self, ZMod.val_natCast_of_lt]
      · exact ⟨hq0, hqhalf⟩
      · have hhalfpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        omega
    have hymem : isingTorusInStrictLower i y0 := by
      unfold isingTorusInStrictLower
      dsimp only [y0]
      rw [isingTorusCoordinateShift_apply_same, ZMod.val_natCast_of_lt]
      · exact ⟨hq0, hqhalf⟩
      · have hhalfpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        omega
    let x : IsingTorusStrictLower (k := k) i := ⟨x0, hxmem⟩
    let y : IsingTorusStrictLower (k := k) i := ⟨y0, hymem⟩
    have hcauchy := isingTorusTwoPoint_siteReflection_cauchy
      (k := k) i beta x y
    have hxy : isingTorusSiteReflect i y.1 - x.1 = -z := by
      funext j
      by_cases hji : j = i
      · subst j
        dsimp only [x, y, x0, y0]
        rw [Pi.sub_apply, isingTorusSiteReflect_apply_same,
          isingTorusCoordinateShift_apply_same, Function.update_self,
          Pi.neg_apply, hz]
        rw [hrq]
        push_cast
        ring
      · dsimp only [x, y, x0, y0]
        rw [Pi.sub_apply, isingTorusSiteReflect_apply_of_ne i j hji,
          isingTorusCoordinateShift_apply_of_ne i j hji,
          Function.update_of_ne hji, Pi.neg_apply]
        ring
    have hxx : isingTorusSiteReflect i x.1 - x.1 =
        -isingTorusCoordinateShift i r := by
      funext j
      by_cases hji : j = i
      · subst j
        dsimp only [x, x0]
        rw [Pi.sub_apply, isingTorusSiteReflect_apply_same,
          Function.update_self, Pi.neg_apply,
          isingTorusCoordinateShift_apply_same]
        rw [hrq]
        push_cast
        ring
      · dsimp only [x, x0]
        rw [Pi.sub_apply, isingTorusSiteReflect_apply_of_ne i j hji,
          Function.update_of_ne hji, Pi.neg_apply,
          isingTorusCoordinateShift_apply_of_ne i j hji]
        ring
    have hyy : isingTorusSiteReflect i y.1 - y.1 =
        -isingTorusCoordinateShift i r := by
      funext j
      by_cases hji : j = i
      · subst j
        dsimp only [y, y0]
        rw [Pi.sub_apply, isingTorusSiteReflect_apply_same,
          isingTorusCoordinateShift_apply_same, Pi.neg_apply]
        rw [hrq]
        rw [isingTorusCoordinateShift_apply_same]
        push_cast
        ring
      · dsimp only [y, y0]
        rw [Pi.sub_apply, isingTorusSiteReflect_apply_of_ne i j hji,
          isingTorusCoordinateShift_apply_of_ne i j hji, Pi.neg_apply]
        rw [isingTorusCoordinateShift_apply_of_ne i j hji]
        ring
    have hleft : isingTorusTwoPoint beta x.1
        (isingTorusSiteReflect i y.1) = isingTorusTwoPoint beta 0 z := by
      rw [isingTorusTwoPoint_eq_origin_displacement, hxy,
        isingTorusTwoPoint_origin_neg]
    have hrightX : isingTorusTwoPoint beta x.1
        (isingTorusSiteReflect i x.1) =
          isingTorusTwoPoint (k := k) beta 0
            (isingTorusCoordinateShift i r) := by
      rw [isingTorusTwoPoint_eq_origin_displacement, hxx,
        isingTorusTwoPoint_origin_neg]
    have hrightY : isingTorusTwoPoint beta y.1
        (isingTorusSiteReflect i y.1) =
          isingTorusTwoPoint (k := k) beta 0
            (isingTorusCoordinateShift i r) := by
      rw [isingTorusTwoPoint_eq_origin_displacement, hyy,
        isingTorusTwoPoint_origin_neg]
    rw [hleft, hrightX, hrightY] at hcauchy
    have hznonneg : 0 <= isingTorusTwoPoint beta 0 z := by
      rw [isingTorusTwoPoint_eq_twoPointJ_unitEdge]
      exact twoPointJ_nonneg (isingTorusGraph d k) beta
        (unitEdgeCoupling (isingTorusGraph d k)) hbeta
        (unitEdgeCoupling_nonneg (isingTorusGraph d k)) 0 z
    have haxisnonneg : 0 <= isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) := by
      rw [isingTorusTwoPoint_eq_twoPointJ_unitEdge]
      exact twoPointJ_nonneg (isingTorusGraph d k) beta
        (unitEdgeCoupling (isingTorusGraph d k)) hbeta
        (unitEdgeCoupling_nonneg (isingTorusGraph d k)) 0 _
    nlinarith
  · have hmodlt : r % 2 < 2 := Nat.mod_lt r (by omega)
    have hodd : r % 2 = 1 := by omega
    let q := r / 2
    have hrq : r = 2 * q + 1 := by
      dsimp only [q]
      omega
    have hqhalf : q < 2 ^ (k + 1) := by omega
    let x0 : IsingDyadicTorus d k :=
      Function.update z i (q : ZMod (2 ^ (k + 2)))
    let y0 : IsingDyadicTorus d k := isingTorusCoordinateShift i q
    have hxmem : isingTorusInLowerHalf i x0 := by
      unfold isingTorusInLowerHalf
      dsimp only [x0]
      rw [Function.update_self, ZMod.val_natCast_of_lt]
      · exact hqhalf
      · have hhalfpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        omega
    have hymem : isingTorusInLowerHalf i y0 := by
      unfold isingTorusInLowerHalf
      dsimp only [y0]
      rw [isingTorusCoordinateShift_apply_same, ZMod.val_natCast_of_lt]
      · exact hqhalf
      · have hhalfpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        omega
    let x : IsingTorusLowerSite (k := k) i := ⟨x0, hxmem⟩
    let y : IsingTorusLowerSite (k := k) i := ⟨y0, hymem⟩
    have hcauchy := isingTorusTwoPoint_reflection_cauchy
      (k := k) i beta hbeta x y
    have hxy : isingTorusReflectSite i y.1 - x.1 = -z := by
      funext j
      by_cases hji : j = i
      · subst j
        dsimp only [x, y, x0, y0]
        rw [Pi.sub_apply, isingTorusReflectSite_apply_same,
          isingTorusCoordinateShift_apply_same, Function.update_self,
          Pi.neg_apply, hz, isingTorusReflectCoord_eq_neg_sub_one]
        rw [hrq]
        push_cast
        ring
      · dsimp only [x, y, x0, y0]
        rw [Pi.sub_apply, isingTorusReflectSite_apply_of_ne i j hji,
          isingTorusCoordinateShift_apply_of_ne i j hji,
          Function.update_of_ne hji, Pi.neg_apply]
        ring
    have hxx : isingTorusReflectSite i x.1 - x.1 =
        -isingTorusCoordinateShift i r := by
      funext j
      by_cases hji : j = i
      · subst j
        dsimp only [x, x0]
        rw [Pi.sub_apply, isingTorusReflectSite_apply_same,
          Function.update_self, isingTorusReflectCoord_eq_neg_sub_one,
          Pi.neg_apply, isingTorusCoordinateShift_apply_same]
        rw [hrq]
        push_cast
        ring
      · dsimp only [x, x0]
        rw [Pi.sub_apply, isingTorusReflectSite_apply_of_ne i j hji,
          Function.update_of_ne hji, Pi.neg_apply,
          isingTorusCoordinateShift_apply_of_ne i j hji]
        ring
    have hyy : isingTorusReflectSite i y.1 - y.1 =
        -isingTorusCoordinateShift i r := by
      funext j
      by_cases hji : j = i
      · subst j
        dsimp only [y, y0]
        rw [Pi.sub_apply, isingTorusReflectSite_apply_same,
          isingTorusCoordinateShift_apply_same,
          isingTorusReflectCoord_eq_neg_sub_one, Pi.neg_apply]
        rw [hrq]
        rw [isingTorusCoordinateShift_apply_same]
        push_cast
        ring
      · dsimp only [y, y0]
        rw [Pi.sub_apply, isingTorusReflectSite_apply_of_ne i j hji,
          isingTorusCoordinateShift_apply_of_ne i j hji, Pi.neg_apply]
        rw [isingTorusCoordinateShift_apply_of_ne i j hji]
        ring
    have hleft : isingTorusTwoPoint beta x.1
        (isingTorusReflectSite i y.1) = isingTorusTwoPoint beta 0 z := by
      rw [isingTorusTwoPoint_eq_origin_displacement, hxy,
        isingTorusTwoPoint_origin_neg]
    have hrightX : isingTorusTwoPoint beta x.1
        (isingTorusReflectSite i x.1) =
          isingTorusTwoPoint (k := k) beta 0
            (isingTorusCoordinateShift i r) := by
      rw [isingTorusTwoPoint_eq_origin_displacement, hxx,
        isingTorusTwoPoint_origin_neg]
    have hrightY : isingTorusTwoPoint beta y.1
        (isingTorusReflectSite i y.1) =
          isingTorusTwoPoint (k := k) beta 0
            (isingTorusCoordinateShift i r) := by
      rw [isingTorusTwoPoint_eq_origin_displacement, hyy,
        isingTorusTwoPoint_origin_neg]
    rw [hleft, hrightX, hrightY] at hcauchy
    have hznonneg : 0 <= isingTorusTwoPoint beta 0 z := by
      rw [isingTorusTwoPoint_eq_twoPointJ_unitEdge]
      exact twoPointJ_nonneg (isingTorusGraph d k) beta
        (unitEdgeCoupling (isingTorusGraph d k)) hbeta
        (unitEdgeCoupling_nonneg (isingTorusGraph d k)) 0 z
    have haxisnonneg : 0 <= isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) := by
      rw [isingTorusTwoPoint_eq_twoPointJ_unitEdge]
      exact twoPointJ_nonneg (isingTorusGraph d k) beta
        (unitEdgeCoupling (isingTorusGraph d k)) hbeta
        (unitEdgeCoupling_nonneg (isingTorusGraph d k)) 0 _
    nlinarith

end StatMech.FrontierA
