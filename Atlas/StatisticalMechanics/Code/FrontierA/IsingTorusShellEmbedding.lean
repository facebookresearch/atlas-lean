/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusShellMonotonicity
import Code.FrontierA.IsingTorusEmbedding

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice

variable {d k : Nat}




theorem isingTorusTwoPoint_embedded_le_axis_of_natAbs_coordinate
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (r : Nat) (hr : r < 2 ^ (k + 1))
    (hxi : (x i).natAbs = r) :
    isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k x) <=
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) := by
  cases hcoord : x i with
  | ofNat n =>
      have hnr : n = r := by simpa [hcoord] using hxi
      rw [← hnr] at hr ⊢
      apply isingTorusTwoPoint_le_axis_of_coordinate_eq
        i beta hbeta (isingSiteToDyadicTorus k x) n hr
      change ((x i : Int) : ZMod (isingDyadicSide k)) =
        (n : ZMod (2 ^ (k + 2)))
      rw [hcoord]
      exact Int.cast_natCast n
  | negSucc n =>
      have hnr : n + 1 = r := by simpa [hcoord] using hxi
      rw [← hnr] at hr ⊢
      have hbound := isingTorusTwoPoint_le_axis_of_coordinate_eq
        i beta hbeta (-(isingSiteToDyadicTorus k x)) (n + 1) hr (by
          simp only [Pi.neg_apply, isingSiteToDyadicTorus, hcoord,
            Int.cast_negSucc]
          push_cast
          abel)
      rwa [isingTorusTwoPoint_origin_neg] at hbound


theorem exists_natAbs_coordinate_eq_of_mem_boxSV_vbF
    {n : Nat} (hn : 1 <= n) (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    ∃ i : Fin d, (x i).natAbs = n := by
  classical
  rw [boxSV_vbF, Finset.mem_sdiff] at hx
  have hin : x ∈ box d n := by
    rw [← boxSV_coe_boxF]
    exact hx.1
  by_contra h
  push Not at h
  apply hx.2
  have hinner : x ∈ box d (n - 1) := by
    intro i
    have hle := hin i
    have hne := h i
    omega
  change x ∈ (boxSV_boxF d (n - 1) : Set (Site d))
  rw [boxSV_coe_boxF]
  exact hinner



theorem exists_isingTorusTwoPoint_embedded_shell_le_axis
    (beta : Real) (hbeta : 0 <= beta) {n : Nat} (hn : 1 <= n)
    (hnHalf : n < 2 ^ (k + 1)) (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    ∃ i : Fin d,
      isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k x) <=
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i n) := by
  obtain ⟨i, hi⟩ := exists_natAbs_coordinate_eq_of_mem_boxSV_vbF hn x hx
  exact ⟨i, isingTorusTwoPoint_embedded_le_axis_of_natAbs_coordinate
    i beta hbeta x n hnHalf hi⟩

end StatMech.FrontierA
