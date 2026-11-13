/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusSiteReflection

open Finset Set

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

private noncomputable def isingTorusAxisCorrelation
    (i : Fin d) (beta : Real) (n : Nat) : Real :=
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i n)

private theorem isingTorusAxisCorrelation_nonneg
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta) (n : Nat) :
    0 ≤ isingTorusAxisCorrelation (k := k) i beta n := by
  unfold isingTorusAxisCorrelation
  rw [isingTorusTwoPoint_eq_twoPointJ_unitEdge]
  exact twoPointJ_nonneg (isingTorusGraph d k) beta
    (unitEdgeCoupling (isingTorusGraph d k)) hbeta
    (unitEdgeCoupling_nonneg (isingTorusGraph d k)) 0
    (isingTorusCoordinateShift i n)

private theorem isingTorusAxisCorrelation_zero
    (i : Fin d) (beta : Real) :
    isingTorusAxisCorrelation (k := k) i beta 0 = 1 := by
  unfold isingTorusAxisCorrelation
  have hzero : isingTorusCoordinateShift (k := k) i 0 = 0 := by
    funext j
    simp [isingTorusCoordinateShift]
  rw [hzero, isingTorusTwoPoint_eq_twoPointJ_unitEdge,
    twoPointJ_self]



theorem isingTorusAxisCorrelation_logConvex
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (n : Nat) (hn2 : 2 ≤ n) (hnH : n ≤ 2 ^ (k + 1)) :
    isingTorusAxisCorrelation (k := k) i beta n ^ 2 ≤
      isingTorusAxisCorrelation (k := k) i beta (n - 1) *
        isingTorusAxisCorrelation (k := k) i beta (n + 1) := by
  by_cases heven : n % 2 = 0
  · let q := n / 2
    have hnmod : n = 2 * q := by
      dsimp only [q]
      omega
    have hqpos : 0 < q := by omega
    have hqhalf : q < 2 ^ (k + 1) := by
      have hHpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
      omega
    have hqmhalf : q - 1 < 2 ^ (k + 1) := by omega
    have h := isingTorusTwoPoint_axis_midpoint_sq_le
      (k := k) i beta hbeta (q - 1) q hqmhalf hqhalf
    unfold isingTorusAxisCorrelation
    convert h using 1 <;> congr 3 <;> omega
  · have hmodlt : n % 2 < 2 := Nat.mod_lt n (by omega)
    have hodd : n % 2 = 1 := by omega
    let q := n / 2
    have hnmod : n = 2 * q + 1 := by
      dsimp only [q]
      omega
    have hqpos : 0 < q := by omega
    have hq1pos : 0 < q + 1 := by omega
    have hqhalf : q < 2 ^ (k + 1) := by
      have hHpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
      omega
    have hq1half : q + 1 < 2 ^ (k + 1) := by
      have hHeven : 2 ^ (k + 1) % 2 = 0 := by
        rw [show k + 1 = k + 1 by rfl, pow_succ]
        omega
      omega
    have h := isingTorusTwoPoint_axis_site_midpoint_sq_le
      (k := k) i beta q (q + 1) hqpos hq1pos hqhalf hq1half
    unfold isingTorusAxisCorrelation
    convert h using 1 <;> congr 3 <;> omega

private theorem isingTorusCoordinateShift_half_succ_eq_neg_pred
    (i : Fin d) :
    isingTorusCoordinateShift (k := k) i (2 ^ (k + 1) + 1) =
      -isingTorusCoordinateShift i (2 ^ (k + 1) - 1) := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [isingTorusCoordinateShift_apply_same,
      Pi.neg_apply, isingTorusCoordinateShift_apply_same]
    have hHpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
    have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    have hnat : 2 ^ (k + 1) + 1 + (2 ^ (k + 1) - 1) =
        2 ^ (k + 2) := by omega
    have hsum :
        ((2 ^ (k + 1) + 1 : Nat) : ZMod (2 ^ (k + 2))) +
          ((2 ^ (k + 1) - 1 : Nat) : ZMod (2 ^ (k + 2))) = 0 := by
      rw [← Nat.cast_add, hnat, ZMod.natCast_self]
    linear_combination hsum
  · simp [isingTorusCoordinateShift_apply_of_ne i j hji]

private theorem isingTorusAxisCorrelation_half_succ
    (i : Fin d) (beta : Real) :
    isingTorusAxisCorrelation (k := k) i beta (2 ^ (k + 1) + 1) =
      isingTorusAxisCorrelation (k := k) i beta (2 ^ (k + 1) - 1) := by
  unfold isingTorusAxisCorrelation
  rw [isingTorusCoordinateShift_half_succ_eq_neg_pred,
    isingTorusTwoPoint_origin_neg]



theorem isingTorusAxisCorrelation_succ_le
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (n : Nat) (hn : n < 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i (n + 1)) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i n) := by
  change isingTorusAxisCorrelation (k := k) i beta (n + 1) ≤
    isingTorusAxisCorrelation (k := k) i beta n
  by_cases hn0 : n = 0
  · subst n
    rw [isingTorusAxisCorrelation_zero]
    exact isingTorusTwoPoint_le_one beta 0
      (isingTorusCoordinateShift i 1)
  · have hH2 : 2 ≤ 2 ^ (k + 1) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    let H := 2 ^ (k + 1)
    have hbaseLog := isingTorusAxisCorrelation_logConvex
      (k := k) i beta hbeta H hH2 (le_refl H)
    have hsymm := isingTorusAxisCorrelation_half_succ
      (k := k) i beta
    have hbaseNonneg := isingTorusAxisCorrelation_nonneg
      (k := k) i beta hbeta (H - 1)
    have hbase : isingTorusAxisCorrelation (k := k) i beta H ≤
        isingTorusAxisCorrelation (k := k) i beta (H - 1) := by
      rw [hsymm] at hbaseLog
      nlinarith
    have hnle : n ≤ H - 1 := by dsimp only [H]; omega
    have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hHone : 1 ≤ H := by
      have hHpos : 0 < H := by
        dsimp only [H]
        exact pow_pos (by omega) _
      omega
    have hbase' :
        isingTorusAxisCorrelation (k := k) i beta (H - 1 + 1) ≤
          isingTorusAxisCorrelation (k := k) i beta (H - 1) := by
      rw [Nat.sub_add_cancel hHone]
      exact hbase
    exact Nat.decreasingInduction'
      (P := fun m => isingTorusAxisCorrelation (k := k) i beta (m + 1) ≤
        isingTorusAxisCorrelation (k := k) i beta m)
      (m := n) (n := H - 1)
      (fun m hmTop hmBottom ih => by
        change isingTorusAxisCorrelation (k := k) i beta (m + 2) ≤
          isingTorusAxisCorrelation (k := k) i beta (m + 1) at ih
        change isingTorusAxisCorrelation (k := k) i beta (m + 1) ≤
          isingTorusAxisCorrelation (k := k) i beta m
        have hmcenter2 : 2 ≤ m + 1 := by omega
        have hmcenterH : m + 1 ≤ H := by omega
        have hlog := isingTorusAxisCorrelation_logConvex
          (k := k) i beta hbeta (m + 1) hmcenter2 hmcenterH
        have hmnonneg := isingTorusAxisCorrelation_nonneg
          (k := k) i beta hbeta (m + 1)
        have hmprevnonneg := isingTorusAxisCorrelation_nonneg
          (k := k) i beta hbeta m
        have hmnextnonneg := isingTorusAxisCorrelation_nonneg
          (k := k) i beta hbeta (m + 2)
        rw [show m + 1 - 1 = m by omega,
          show m + 1 + 1 = m + 2 by omega] at hlog
        by_cases hmzero :
            isingTorusAxisCorrelation (k := k) i beta (m + 1) = 0
        · rw [hmzero]
          exact hmprevnonneg
        · have hmpos : 0 <
              isingTorusAxisCorrelation (k := k) i beta (m + 1) :=
            lt_of_le_of_ne hmnonneg (Ne.symm hmzero)
          nlinarith)
      hnle hbase'

end StatMech.FrontierA
