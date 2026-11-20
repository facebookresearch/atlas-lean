/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Code.Universality.IsingFermionicPhysicalCenteredRadialPatch
import Code.Universality.IsingFermionicTensorTentMorera
import Mathlib.Topology.UnitInterval











namespace StatMech.Universality

open Metric Set
open scoped unitInterval

noncomputable section




theorem lipschitzOnWith_of_open_local_on_convex
    (f : Complex -> Complex) (s : Set Complex) (C : NNReal)
    (hs : Convex Real s)
    (hlocal : ∀ z ∈ s, ∃ u : Set Complex,
      IsOpen u ∧ z ∈ u ∧ LipschitzOnWith C f (u ∩ s)) :
    LipschitzOnWith C f s := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let g : Set.Icc (0 : Real) 1 -> Complex := fun t =>
    AffineMap.lineMap x y (t : Real)
  have hgmem (t : Set.Icc (0 : Real) 1) : g t ∈ s := by
    exact hs.lineMap_mem hx hy t.property
  choose u huOpen hgu hLip using fun t => hlocal (g t) (hgmem t)
  let c : Set.Icc (0 : Real) 1 -> Set (Set.Icc (0 : Real) 1) :=
    fun t => g ⁻¹' u t
  have hcOpen : forall t, IsOpen (c t) := by
    intro t
    exact (huOpen t).preimage (by
      dsimp only [g]
      fun_prop)
  have hcCover : Set.univ ⊆ ⋃ t, c t := by
    intro t _ht
    exact Set.mem_iUnion.2 ⟨t, hgu t⟩
  obtain ⟨T, hT0, hTmono, ⟨N, hTN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  have hstep (a : Nat) :
      dist (f (g (T a))) (f (g (T (a + 1)))) <=
        (C : Real) * (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
          ((T a : Set.Icc (0 : Real) 1) : Real)) * dist x y := by
    obtain ⟨q, hq⟩ := hsub a
    have hTa : T a ∈ c q := hq (Set.left_mem_Icc.2 (hTmono (Nat.le_succ a)))
    have hTa1 : T (a + 1) ∈ c q :=
      hq (Set.right_mem_Icc.2 (hTmono (Nat.le_succ a)))
    have hbound := LipschitzOnWith.dist_le_mul (hLip q)
      (g (T a)) ⟨hTa, hgmem (T a)⟩
      (g (T (a + 1))) ⟨hTa1, hgmem (T (a + 1))⟩
    have hcoeff :
        0 <= ((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
          ((T a : Set.Icc (0 : Real) 1) : Real) := by
      exact sub_nonneg.mpr (hTmono (Nat.le_succ a))
    calc
      dist (f (g (T a))) (f (g (T (a + 1)))) <=
          (C : Real) * dist (g (T a)) (g (T (a + 1))) := hbound
      _ = (C : Real) *
          (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
            ((T a : Set.Icc (0 : Real) 1) : Real)) * dist x y := by
        rw [show dist (g (T a)) (g (T (a + 1))) =
            dist ((T a : Set.Icc (0 : Real) 1) : Real)
              ((T (a + 1) : Set.Icc (0 : Real) 1) : Real) * dist x y by
          exact dist_lineMap_lineMap (𝕜 := Real) x y _ _]
        rw [Real.dist_eq, abs_of_nonpos
          (by linarith [hcoeff] :
            ((T a : Set.Icc (0 : Real) 1) : Real) -
              ((T (a + 1) : Set.Icc (0 : Real) 1) : Real) <= 0)]
        ring
  have hpath := dist_le_range_sum_dist (fun a => f (g (T a))) N
  have hsum :
      (∑ a ∈ Finset.range N,
        (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
          ((T a : Set.Icc (0 : Real) 1) : Real))) = 1 := by
    have htel :
        (∑ a ∈ Finset.range N,
          (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
            ((T a : Set.Icc (0 : Real) 1) : Real))) =
          ((T N : Set.Icc (0 : Real) 1) : Real) -
            ((T 0 : Set.Icc (0 : Real) 1) : Real) := by
      simpa only using
        (Finset.sum_range_sub (fun a => ((T a : Set.Icc (0 : Real) 1) : Real)) N)
    rw [htel]
    rw [hTN N (le_refl N), hT0]
    norm_num
  calc
    dist (f x) (f y) = dist (f (g (T 0))) (f (g (T N))) := by
      rw [hT0, hTN N (le_refl N)]
      simp [g]
    _ <= ∑ a ∈ Finset.range N,
        dist (f (g (T a))) (f (g (T (a + 1)))) := hpath
    _ <= ∑ a ∈ Finset.range N,
        ((C : Real) *
          (((T (a + 1) : Set.Icc (0 : Real) 1) : Real) -
            ((T a : Set.Icc (0 : Real) 1) : Real)) * dist x y) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hstep a
    _ = (C : Real) * dist x y := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
      ring



theorem complexBilinearCell_right_eq_left
    (a00 a10 a01 a11 b10 b11 : Complex) (y : Real) :
    complexBilinearCell a00 a10 a01 a11 1 y =
      complexBilinearCell a10 b10 a11 b11 0 y := by
  unfold complexBilinearCell
  push_cast
  ring



theorem complexBilinearCell_top_eq_bottom
    (a00 a10 a01 a11 b01 b11 : Complex) (x : Real) :
    complexBilinearCell a00 a10 a01 a11 x 1 =
      complexBilinearCell a01 a11 b01 b11 x 0 := by
  unfold complexBilinearCell
  push_cast
  ring





theorem complexBilinearCell_horizontalAdjacent_norm_sub_le
    (a00 a10 a01 a11 b10 b11 : Complex)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom : norm (a10 - a00) <= D)
    (haTop : norm (a11 - a01) <= D)
    (haLeft : norm (a01 - a00) <= D)
    (haRight : norm (a11 - a10) <= D)
    (hbBottom : norm (b10 - a10) <= D)
    (hbTop : norm (b11 - a11) <= D)
    (hbRight : norm (b11 - b10) <= D) :
    norm (complexBilinearCell a00 a10 a01 a11 x y -
      complexBilinearCell a10 b10 a11 b11 x' y') <=
        D * ((1 - x) + x' + |y - y'|) := by
  let shared := complexBilinearCell a00 a10 a01 a11 1 y
  have hleft :
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) <=
        D * (1 - x) := by
    have h := complexBilinearCell_norm_sub_le
      a00 a10 a01 a11 x 1 y y D (by norm_num) (by norm_num)
      hy0 hy1 haBottom haTop haLeft haRight
    simpa [shared, abs_of_nonpos (by linarith : x - 1 <= 0)] using h
  have hshared :
      shared = complexBilinearCell a10 b10 a11 b11 0 y := by
    exact complexBilinearCell_right_eq_left _ _ _ _ _ _ _
  have hright :
      norm (shared - complexBilinearCell a10 b10 a11 b11 x' y') <=
        D * (x' + |y - y'|) := by
    rw [hshared]
    have h := complexBilinearCell_norm_sub_le
      a10 b10 a11 b11 0 x' y y' D hx0' hx1' hy0 hy1
      hbBottom hbTop haRight hbRight
    simpa [abs_of_nonneg hx0'] using h
  calc
    norm (complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a10 b10 a11 b11 x' y') <=
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) +
        norm (shared - complexBilinearCell a10 b10 a11 b11 x' y') := by
          rw [show complexBilinearCell a00 a10 a01 a11 x y -
              complexBilinearCell a10 b10 a11 b11 x' y' =
            (complexBilinearCell a00 a10 a01 a11 x y - shared) +
              (shared - complexBilinearCell a10 b10 a11 b11 x' y') by ring]
          exact norm_add_le _ _
    _ <= D * (1 - x) + D * (x' + |y - y'|) := add_le_add hleft hright
    _ = D * ((1 - x) + x' + |y - y'|) := by ring



theorem complexBilinearCell_verticalAdjacent_norm_sub_le
    (a00 a10 a01 a11 b01 b11 : Complex)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom : norm (a10 - a00) <= D)
    (haTop : norm (a11 - a01) <= D)
    (haLeft : norm (a01 - a00) <= D)
    (haRight : norm (a11 - a10) <= D)
    (hbTop : norm (b11 - b01) <= D)
    (hbLeft : norm (b01 - a01) <= D)
    (hbRight : norm (b11 - a11) <= D) :
    norm (complexBilinearCell a00 a10 a01 a11 x y -
      complexBilinearCell a01 a11 b01 b11 x' y') <=
        D * (|x - x'| + (1 - y) + y') := by
  let shared := complexBilinearCell a00 a10 a01 a11 x 1
  have hlower :
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) <=
        D * (1 - y) := by
    have h := complexBilinearCell_norm_sub_le
      a00 a10 a01 a11 x x y 1 D hx0 hx1 hy0 hy1
      haBottom haTop haLeft haRight
    simpa [shared, abs_of_nonpos (by linarith : y - 1 <= 0)] using h
  have hshared :
      shared = complexBilinearCell a01 a11 b01 b11 x 0 := by
    exact complexBilinearCell_top_eq_bottom _ _ _ _ _ _ _
  have hupper :
      norm (shared - complexBilinearCell a01 a11 b01 b11 x' y') <=
        D * (|x - x'| + y') := by
    rw [hshared]
    have h := complexBilinearCell_norm_sub_le
      a01 a11 b01 b11 x x' 0 y' D hx0' hx1' (by norm_num) (by norm_num)
      haTop hbTop hbLeft hbRight
    simpa [abs_of_nonneg hy0'] using h
  calc
    norm (complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a01 a11 b01 b11 x' y') <=
      norm (complexBilinearCell a00 a10 a01 a11 x y - shared) +
        norm (shared - complexBilinearCell a01 a11 b01 b11 x' y') := by
          rw [show complexBilinearCell a00 a10 a01 a11 x y -
              complexBilinearCell a01 a11 b01 b11 x' y' =
            (complexBilinearCell a00 a10 a01 a11 x y - shared) +
              (shared - complexBilinearCell a01 a11 b01 b11 x' y') by ring]
          exact norm_add_le _ _
    _ <= D * (1 - y) + D * (|x - x'| + y') := add_le_add hlower hupper
    _ = D * (|x - x'| + (1 - y) + y') := by ring


def complexBilinearHorizontalStrip
    (a00 a10 a20 a01 a11 a21 : Complex) (x y : Real) : Complex :=
  if x <= 1 then
    complexBilinearCell a00 a10 a01 a11 x y
  else
    complexBilinearCell a10 a20 a11 a21 (x - 1) y



theorem complexBilinearHorizontalStrip_norm_sub_le
    (a00 a10 a20 a01 a11 a21 : Complex) (x x' y D : Real)
    (hx0 : 0 <= x) (hx2 : x <= 2)
    (hx0' : 0 <= x') (hx2' : x' <= 2)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (h00_10 : norm (a10 - a00) <= D)
    (h10_20 : norm (a20 - a10) <= D)
    (h01_11 : norm (a11 - a01) <= D)
    (h11_21 : norm (a21 - a11) <= D)
    (h00_01 : norm (a01 - a00) <= D)
    (h10_11 : norm (a11 - a10) <= D)
    (h20_21 : norm (a21 - a20) <= D) :
    norm (complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x y -
      complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x' y) <=
        D * |x - x'| := by
  by_cases hx : x <= 1
  · by_cases hx' : x' <= 1
    · have h := complexBilinearCell_norm_sub_le
        a00 a10 a01 a11 x x' y y D (by linarith) hx' hy0 hy1
        h00_10 h01_11 h00_01 h10_11
      simpa [complexBilinearHorizontalStrip, hx, hx'] using h
    · have hx'1 : 1 < x' := lt_of_not_ge hx'
      have h := complexBilinearCell_horizontalAdjacent_norm_sub_le
        a00 a10 a01 a11 a20 a21 x (x' - 1) y y D
        hx0 hx (by linarith) (by linarith) hy0 hy1 hy0 hy1
        h00_10 h01_11 h00_01 h10_11 h10_20 h11_21 h20_21
      simpa [complexBilinearHorizontalStrip, hx, hx',
        abs_of_nonpos (by linarith : x - x' <= 0)] using h
  · have hx1 : 1 < x := lt_of_not_ge hx
    by_cases hx' : x' <= 1
    · have h := complexBilinearCell_horizontalAdjacent_norm_sub_le
        a00 a10 a01 a11 a20 a21 x' (x - 1) y y D
        hx0' hx' (by linarith) (by linarith) hy0 hy1 hy0 hy1
        h00_10 h01_11 h00_01 h10_11 h10_20 h11_21 h20_21
      rw [norm_sub_rev]
      simpa [complexBilinearHorizontalStrip, hx, hx',
        abs_of_nonneg (by linarith : 0 <= x - x')] using h
    · have hx'1 : 1 < x' := lt_of_not_ge hx'
      have h := complexBilinearCell_norm_sub_le
        a10 a20 a11 a21 (x - 1) (x' - 1) y y D
        (by linarith) (by linarith) hy0 hy1
        h10_20 h11_21 h10_11 h20_21
      simpa [complexBilinearHorizontalStrip, hx, hx'] using h


def complexBilinearVerticalStrip
    (a00 a10 a01 a11 a02 a12 : Complex) (x y : Real) : Complex :=
  if y <= 1 then
    complexBilinearCell a00 a10 a01 a11 x y
  else
    complexBilinearCell a01 a11 a02 a12 x (y - 1)



theorem complexBilinearVerticalStrip_norm_sub_le
    (a00 a10 a01 a11 a02 a12 : Complex) (x y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy0 : 0 <= y) (hy2 : y <= 2)
    (hy0' : 0 <= y') (hy2' : y' <= 2)
    (h00_10 : norm (a10 - a00) <= D)
    (h01_11 : norm (a11 - a01) <= D)
    (h02_12 : norm (a12 - a02) <= D)
    (h00_01 : norm (a01 - a00) <= D)
    (h01_02 : norm (a02 - a01) <= D)
    (h10_11 : norm (a11 - a10) <= D)
    (h11_12 : norm (a12 - a11) <= D) :
    norm (complexBilinearVerticalStrip a00 a10 a01 a11 a02 a12 x y -
      complexBilinearVerticalStrip a00 a10 a01 a11 a02 a12 x y') <=
        D * |y - y'| := by
  by_cases hy : y <= 1
  · by_cases hy' : y' <= 1
    · have h := complexBilinearCell_norm_sub_le
        a00 a10 a01 a11 x x y y' D hx0 hx1 hy0 hy
        h00_10 h01_11 h00_01 h10_11
      simpa [complexBilinearVerticalStrip, hy, hy'] using h
    · have hy'1 : 1 < y' := lt_of_not_ge hy'
      have h := complexBilinearCell_verticalAdjacent_norm_sub_le
        a00 a10 a01 a11 a02 a12 x x y (y' - 1) D
        hx0 hx1 hx0 hx1 hy0 hy (by linarith) (by linarith)
        h00_10 h01_11 h00_01 h10_11 h02_12 h01_02 h11_12
      simpa [complexBilinearVerticalStrip, hy, hy',
        abs_of_nonpos (by linarith : y - y' <= 0)] using h
  · have hy1 : 1 < y := lt_of_not_ge hy
    by_cases hy' : y' <= 1
    · have h := complexBilinearCell_verticalAdjacent_norm_sub_le
        a00 a10 a01 a11 a02 a12 x x y' (y - 1) D
        hx0 hx1 hx0 hx1 hy0' hy' (by linarith) (by linarith)
        h00_10 h01_11 h00_01 h10_11 h02_12 h01_02 h11_12
      rw [norm_sub_rev]
      simpa [complexBilinearVerticalStrip, hy, hy',
        abs_of_nonneg (by linarith : 0 <= y - y')] using h
    · have hy'1 : 1 < y' := lt_of_not_ge hy'
      have h := complexBilinearCell_norm_sub_le
        a01 a11 a02 a12 x x (y - 1) (y' - 1) D hx0 hx1
        (by linarith) (by linarith) h01_11 h02_12 h01_02 h11_12
      simpa [complexBilinearVerticalStrip, hy, hy'] using h


def complexBilinearTwoByTwo
    (a00 a10 a20 a01 a11 a21 a02 a12 a22 : Complex)
    (x y : Real) : Complex :=
  if y <= 1 then
    complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x y
  else
    complexBilinearHorizontalStrip a01 a11 a21 a02 a12 a22 x (y - 1)



theorem complexBilinearTwoByTwo_norm_sub_le
    (a00 a10 a20 a01 a11 a21 a02 a12 a22 : Complex)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx2 : x <= 2)
    (hx0' : 0 <= x') (hx2' : x' <= 2)
    (hy0 : 0 <= y) (hy2 : y <= 2)
    (hy0' : 0 <= y') (hy2' : y' <= 2)
    (h00_10 : norm (a10 - a00) <= D)
    (h10_20 : norm (a20 - a10) <= D)
    (h01_11 : norm (a11 - a01) <= D)
    (h11_21 : norm (a21 - a11) <= D)
    (h02_12 : norm (a12 - a02) <= D)
    (h12_22 : norm (a22 - a12) <= D)
    (h00_01 : norm (a01 - a00) <= D)
    (h01_02 : norm (a02 - a01) <= D)
    (h10_11 : norm (a11 - a10) <= D)
    (h11_12 : norm (a12 - a11) <= D)
    (h20_21 : norm (a21 - a20) <= D)
    (h21_22 : norm (a22 - a21) <= D) :
    norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') <=
      D * (|x - x'| + |y - y'|) := by
  have hhorizontal :
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y) <=
        D * |x - x'| := by
    by_cases hy : y <= 1
    · simpa [complexBilinearTwoByTwo, hy] using
        complexBilinearHorizontalStrip_norm_sub_le
          a00 a10 a20 a01 a11 a21 x x' y D
          hx0 hx2 hx0' hx2' hy0 hy h00_10 h10_20 h01_11 h11_21
          h00_01 h10_11 h20_21
    · have hy1 : 1 < y := lt_of_not_ge hy
      simpa [complexBilinearTwoByTwo, hy] using
        complexBilinearHorizontalStrip_norm_sub_le
          a01 a11 a21 a02 a12 a22 x x' (y - 1) D
          hx0 hx2 hx0' hx2' (by linarith) (by linarith)
          h01_11 h11_21 h02_12 h12_22 h01_02 h11_12 h21_22
  have hvertical :
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') <=
        D * |y - y'| := by
    by_cases hx' : x' <= 1
    · simpa [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx'] using
        complexBilinearVerticalStrip_norm_sub_le
          a00 a10 a01 a11 a02 a12 x' y y' D
          hx0' hx' hy0 hy2 hy0' hy2'
          h00_10 h01_11 h02_12 h00_01 h01_02 h10_11 h11_12
    · have hx'1 : 1 < x' := lt_of_not_ge hx'
      simpa [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx'] using
        complexBilinearVerticalStrip_norm_sub_le
          a10 a20 a11 a21 a12 a22 (x' - 1) y y' D
          (by linarith) (by linarith) hy0 hy2 hy0' hy2'
          h10_20 h11_21 h12_22 h10_11 h11_12 h20_21 h21_22
  calc
    norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') <=
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y) +
      norm (complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y -
        complexBilinearTwoByTwo
          a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') := by
      rw [show complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
          complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y' =
        (complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x y -
          complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y) +
        (complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y -
          complexBilinearTwoByTwo
            a00 a10 a20 a01 a11 a21 a02 a12 a22 x' y') by ring]
      exact norm_add_le _ _
    _ <= D * |x - x'| + D * |y - y'| :=
      add_le_add hhorizontal hvertical
    _ = D * (|x - x'| + |y - y'|) := by ring



theorem finiteCenteredRadialGridInterpolant_horizontalBoundary
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (y : Real) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j 1 y) =
      finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j 0 y) := by
  apply congrArg (finiteCenteredRadialGridInterpolant n mesh value)
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring



theorem finiteCenteredRadialGridInterpolant_verticalBoundary
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (x : Real) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j x 1) =
      finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x 0) := by
  apply congrArg (finiteCenteredRadialGridInterpolant n mesh value)
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring



theorem isingCenteredRadialGridCellPoint_add_one_x
    (mesh : Real) (n i j : Nat) (x y : Real) :
    isingCenteredRadialGridCellPoint mesh n i j (1 + x) y =
      isingCenteredRadialGridCellPoint mesh n (i + 1) j x y := by
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring



theorem isingCenteredRadialGridCellPoint_add_one_y
    (mesh : Real) (n i j : Nat) (x y : Real) :
    isingCenteredRadialGridCellPoint mesh n i j x (1 + y) =
      isingCenteredRadialGridCellPoint mesh n i (j + 1) x y := by
  unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    push_cast
    ring



theorem finiteCenteredRadialGridInterpolant_twoByTwo
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 2 < 2 * n)
    (x y : Real) (hx0 : 0 <= x) (hx2 : x <= 2)
    (hy0 : 0 <= y) (hy2 : y <= 2) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j x y) =
      complexBilinearTwoByTwo
        (value ⟨i, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
        (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩) x y := by
  by_cases hx : x <= 1
  · by_cases hy : y <= 1
    · rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value i j (by omega) (by omega) x y
        hx0 hx hy0 hy]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]
    · have hy1 : 1 < y := lt_of_not_ge hy
      rw [show isingCenteredRadialGridCellPoint mesh n i j x y =
          isingCenteredRadialGridCellPoint mesh n i (j + 1) x (y - 1) by
        convert isingCenteredRadialGridCellPoint_add_one_y
          mesh n i j x (y - 1) using 1 <;> ring]
      rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value i (j + 1) (by omega) (by omega) x (y - 1)
        hx0 hx (by linarith) (by linarith)]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]
  · have hx1 : 1 < x := lt_of_not_ge hx
    by_cases hy : y <= 1
    · rw [show isingCenteredRadialGridCellPoint mesh n i j x y =
          isingCenteredRadialGridCellPoint mesh n (i + 1) j (x - 1) y by
        convert isingCenteredRadialGridCellPoint_add_one_x
          mesh n i j (x - 1) y using 1 <;> ring]
      rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value (i + 1) j (by omega) (by omega) (x - 1) y
        (by linarith) (by linarith) hy0 hy]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]
    · have hy1 : 1 < y := lt_of_not_ge hy
      rw [show isingCenteredRadialGridCellPoint mesh n i j x y =
          isingCenteredRadialGridCellPoint mesh n (i + 1) (j + 1)
            (x - 1) (y - 1) by
        calc
          isingCenteredRadialGridCellPoint mesh n i j x y =
              isingCenteredRadialGridCellPoint mesh n i j x (1 + (y - 1)) := by
            congr 2
            ring
          _ = isingCenteredRadialGridCellPoint mesh n i (j + 1) x (y - 1) :=
            isingCenteredRadialGridCellPoint_add_one_y
              mesh n i j x (y - 1)
          _ = isingCenteredRadialGridCellPoint mesh n (i + 1) (j + 1)
              (x - 1) (y - 1) := by
            rw [← isingCenteredRadialGridCellPoint_add_one_x
              mesh n i (j + 1) (x - 1) (y - 1)]
            congr 2
            ring]
      rw [finiteCenteredRadialGridInterpolant_cellPoint
        n mesh hmesh value (i + 1) (j + 1) (by omega) (by omega)
        (x - 1) (y - 1) (by linarith) (by linarith)
        (by linarith) (by linarith)]
      simp [complexBilinearTwoByTwo, complexBilinearHorizontalStrip, hx, hy]



theorem finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 2 < 2 * n)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx2 : x <= 2)
    (hx0' : 0 <= x') (hx2' : x' <= 2)
    (hy0 : 0 <= y) (hy2 : y <= 2)
    (hy0' : 0 <= y') (hy2' : y' <= 2)
    (hL : 0 <= L)
    (h00_10 : norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h10_20 : norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h01_11 : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h11_21 : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h02_12 : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
    (h12_22 : norm (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
    (h00_01 : norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h01_02 : norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h10_11 : norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h11_12 : norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (h20_21 : norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
      value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (h21_22 : norm (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ -
      value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x' y')) <=
      4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y') := by
  rw [finiteCenteredRadialGridInterpolant_twoByTwo n mesh hmesh.ne' value
      i j hi hj x y hx0 hx2 hy0 hy2,
    finiteCenteredRadialGridInterpolant_twoByTwo n mesh hmesh.ne' value
      i j hi hj x' y' hx0' hx2' hy0' hy2']
  have hpatch := complexBilinearTwoByTwo_norm_sub_le
    (value ⟨i, by omega⟩ ⟨j, by omega⟩)
    (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
    (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
    (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
    (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
    (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
    (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
    (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
    (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩)
    x x' y y' (mesh * L) hx0 hx2 hx0' hx2' hy0 hy2 hy0' hy2'
    h00_10 h10_20 h01_11 h11_21 h02_12 h12_22
    h00_01 h01_02 h10_11 h11_12 h20_21 h21_22
  have hgeom := abs_mesh_mul_cellCoordinate_l1_le_four_dist
    mesh i j x x' y y'
  have ht : mesh * (|x - x'| + |y - y'|) <=
      4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y') := by
    simpa [abs_of_pos hmesh, isingCenteredRadialGridCellPoint,
      dist_eq_norm] using hgeom
  calc
    norm (complexBilinearTwoByTwo
          (value ⟨i, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩) x y -
        complexBilinearTwoByTwo
          (value ⟨i, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩)
          (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩)
          (value ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩) x' y') <=
        (mesh * L) * (|x - x'| + |y - y'|) := hpatch
    _ = L * (mesh * (|x - x'| + |y - y'|)) := by ring
    _ <= L * (4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y')) := by
      exact mul_le_mul_of_nonneg_left ht hL
    _ = 4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i j x' y') := by ring



theorem finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 1 < 2 * n)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
    (hbBottom :
      norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
    (hbTop :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (hbRight :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= D) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <=
      D * ((1 - x) + x' + |y - y'|) := by
  rw [finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value i j (by omega) hj x y hx0 hx1 hy0 hy1,
    finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value (i + 1) j (by omega) hj x' y'
        hx0' hx1' hy0' hy1']
  exact complexBilinearCell_horizontalAdjacent_norm_sub_le
    _ _ _ _ _ _ x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbBottom hbTop hbRight



theorem finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 1 < 2 * n) (hj : j + 2 < 2 * n)
    (x x' y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= D)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= D)
    (hbTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= D)
    (hbLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= D)
    (hbRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= D) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <=
      D * (|x - x'| + (1 - y) + y') := by
  rw [finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value i j hi (by omega) x y hx0 hx1 hy0 hy1,
    finiteCenteredRadialGridInterpolant_cellPoint
      n mesh hmesh value i (j + 1) hi (by omega) x' y'
        hx0' hx1' hy0' hy1']
  exact complexBilinearCell_verticalAdjacent_norm_sub_le
    _ _ _ _ _ _ x x' y y' D hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbTop hbLeft hbRight




theorem finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le_dist
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 2 < 2 * n) (hj : j + 1 < 2 * n)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hL : 0 <= L)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (hbBottom :
      norm (value ⟨i + 2, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (hbTop :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (hbRight :
      norm (value ⟨i + 2, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 2, by omega⟩ ⟨j, by omega⟩) <= mesh * L) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <=
      4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y') := by
  have hosc :=
    finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le
      n mesh hmesh.ne' value i j hi hj x x' y y' (mesh * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbBottom hbTop hbRight
  have hgeom := abs_mesh_mul_cellCoordinate_l1_le_four_dist
    mesh i j x (1 + x') y y'
  have hpoint :
      isingCenteredRadialGridCellPoint mesh n i j (1 + x') y' =
        isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y' := by
    unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
  have ht :
      mesh * ((1 - x) + x' + |y - y'|) <=
        4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y') := by
    rw [← hpoint]
    calc
      mesh * ((1 - x) + x' + |y - y'|) =
          |mesh| * (|x - (1 + x')| + |y - y'|) := by
        rw [abs_of_pos hmesh,
          abs_of_nonpos (by linarith : x - (1 + x') <= 0)]
        ring
      _ <= 4 * dist
          (isingRadialGridCellPoint mesh i j x y)
          (isingRadialGridCellPoint mesh i j (1 + x') y') := hgeom
      _ = 4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n i j (1 + x') y') := by
        unfold isingCenteredRadialGridCellPoint
        rw [dist_eq_norm, dist_eq_norm]
        congr 2
        ring
  calc
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) <=
      (mesh * L) * ((1 - x) + x' + |y - y'|) := hosc
    _ = L * (mesh * ((1 - x) + x' + |y - y'|)) := by ring
    _ <= L * (4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y')) := by
      gcongr
    _ = 4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n (i + 1) j x' y') := by ring



theorem finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le_dist
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 1 < 2 * n) (hj : j + 2 < 2 * n)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hL : 0 <= L)
    (haBottom :
      norm (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (haLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (haRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩) <= mesh * L)
    (hbTop :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 2, by omega⟩) <= mesh * L)
    (hbLeft :
      norm (value ⟨i, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L)
    (hbRight :
      norm (value ⟨i + 1, by omega⟩ ⟨j + 2, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) <= mesh * L) :
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <=
      4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y') := by
  have hosc :=
    finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le
      n mesh hmesh.ne' value i j hi hj x x' y y' (mesh * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      haBottom haTop haLeft haRight hbTop hbLeft hbRight
  have hgeom := abs_mesh_mul_cellCoordinate_l1_le_four_dist
    mesh i j x x' y (1 + y')
  have hpoint :
      isingCenteredRadialGridCellPoint mesh n i j x' (1 + y') =
        isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y' := by
    unfold isingCenteredRadialGridCellPoint isingRadialGridCellPoint
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]
      push_cast
      ring
  have ht :
      mesh * (|x - x'| + (1 - y) + y') <=
        4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y') := by
    rw [← hpoint]
    calc
      mesh * (|x - x'| + (1 - y) + y') =
          |mesh| * (|x - x'| + |y - (1 + y')|) := by
        rw [abs_of_pos hmesh,
          abs_of_nonpos (by linarith : y - (1 + y') <= 0)]
        ring
      _ <= 4 * dist
          (isingRadialGridCellPoint mesh i j x y)
          (isingRadialGridCellPoint mesh i j x' (1 + y')) := hgeom
      _ = 4 * dist
          (isingCenteredRadialGridCellPoint mesh n i j x y)
          (isingCenteredRadialGridCellPoint mesh n i j x' (1 + y')) := by
        unfold isingCenteredRadialGridCellPoint
        rw [dist_eq_norm, dist_eq_norm]
        congr 2
        ring
  calc
    norm (finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i j x y) -
        finiteCenteredRadialGridInterpolant n mesh value
          (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) <=
      (mesh * L) * (|x - x'| + (1 - y) + y') := hosc
    _ = L * (mesh * (|x - x'| + (1 - y) + y')) := by ring
    _ <= L * (4 * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y')) := by
      gcongr
    _ = 4 * L * dist
        (isingCenteredRadialGridCellPoint mesh n i j x y)
        (isingCenteredRadialGridCellPoint mesh n i (j + 1) x' y') := by ring




noncomputable def isingCenteredRadialGridCoordinate
    (mesh : Real) (n : Nat) (z : Complex) : Real × Real :=
  isingRadialGridCoordinate mesh (z + (mesh * n : Real))

theorem isingCenteredRadialGridCoordinate_cellPoint
    (mesh : Real) (hmesh : mesh ≠ 0) (n i j : Nat) (x y : Real) :
    isingCenteredRadialGridCoordinate mesh n
        (isingCenteredRadialGridCellPoint mesh n i j x y) =
      ((i : Real) + x, (j : Real) + y) := by
  unfold isingCenteredRadialGridCoordinate isingCenteredRadialGridCellPoint
  rw [sub_add_cancel]
  exact isingRadialGridCoordinate_cellPoint mesh hmesh i j x y

theorem isingCenteredRadialGridCellPoint_coordinate
    (mesh : Real) (hmesh : mesh ≠ 0) (n i j : Nat) (z : Complex) :
    isingCenteredRadialGridCellPoint mesh n i j
        ((isingCenteredRadialGridCoordinate mesh n z).1 - i)
        ((isingCenteredRadialGridCoordinate mesh n z).2 - j) = z := by
  unfold isingCenteredRadialGridCoordinate isingCenteredRadialGridCellPoint
    isingRadialGridCoordinate isingRadialGridCellPoint
  apply Complex.ext <;> simp <;> field_simp <;> ring



theorem exists_twoByTwo_cell_of_centeredCoordinate
    (n : Nat) (u : Real) (hlo : 1 < u)
    (hhi : u < (2 * n : Nat) - 2) :
    ∃ i : Nat, i + 2 < 2 * n ∧ (i : Real) < u ∧ u < (i : Real) + 2 := by
  let c : Nat := ⌈u⌉₊
  have hu0 : 0 ≤ u := by linarith
  have hcpos : 0 < c := Nat.ceil_pos.mpr (by linarith)
  have hone : 1 ≤ c := hcpos
  have hn : 2 ≤ n := by
    by_contra hn
    have hn' : n ≤ 1 := by omega
    interval_cases n <;> norm_num at hhi <;> linarith
  have htwo : 2 ≤ 2 * n := by omega
  have hcle : c ≤ 2 * n - 2 := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub htwo]
    norm_num [Nat.cast_mul]
    simpa [Nat.cast_mul] using hhi.le
  refine ⟨c - 1, ?_, ?_, ?_⟩
  · omega
  · have hc_lt : (c : Real) < u + 1 := Nat.ceil_lt_add_one hu0
    rw [Nat.cast_sub hone]
    norm_num
    linarith
  · have hu_le : u ≤ (c : Real) := Nat.le_ceil u
    rw [Nat.cast_sub hone]
    norm_num
    linarith


def finiteCenteredRadialGridStrictInterior
    (n : Nat) (mesh : Real) : Set Complex :=
  {z | 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 2 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 2}



theorem closedBall_subset_finiteCenteredRadialGridStrictInterior
    (n : Nat) (mesh R : Real) (hmesh : 0 < mesh) (hR : 0 <= R)
    (hwide : 2 * R + 4 * mesh <= mesh * n) :
    closedBall (0 : Complex) R ⊆
      finiteCenteredRadialGridStrictInterior n mesh := by
  intro z hz
  have hnorm : norm z <= R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hrelo : -R <= z.re := by
    linarith [neg_le_of_abs_le (hre.trans hnorm)]
  have hrehi : z.re <= R := by
    linarith [le_of_abs_le (hre.trans hnorm)]
  have himlo : -R <= z.im := by
    linarith [neg_le_of_abs_le (him.trans hnorm)]
  have himhi : z.im <= R := by
    linarith [le_of_abs_le (him.trans hnorm)]
  have hq : 2 * R / mesh + 4 <= (n : Real) := by
    calc
      2 * R / mesh + 4 = (2 * R + 4 * mesh) / mesh := by
        field_simp [hmesh.ne']
      _ <= (mesh * (n : Real)) / mesh :=
        (div_le_div_iff_of_pos_right hmesh).mpr hwide
      _ = (n : Real) := by field_simp [hmesh.ne']
  have hsumlo : -2 * R / mesh <= (z.re + z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hsumhi : (z.re + z.im) / mesh <= 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdifflo : -2 * R / mesh <= (z.re - z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdiffhi : (z.re - z.im) / mesh <= 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hneg : -2 * R / mesh = -(2 * R / mesh) := by ring
  rw [hneg] at hsumlo hdifflo
  have hc1 : (isingCenteredRadialGridCoordinate mesh n z).1 =
      (n : Real) + (z.re + z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  have hc2 : (isingCenteredRadialGridCoordinate mesh n z).2 =
      (n : Real) + (z.re - z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  change 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 2 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 2
  rw [hc1, hc2]
  constructor
  · linarith
  constructor
  · push_cast
    linarith
  constructor
  · linarith
  · push_cast
    linarith



def finiteCenteredRadialGridDeeperInterior
    (n : Nat) (mesh : Real) : Set Complex :=
  {z | 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 3 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 3}



theorem closedBall_subset_finiteCenteredRadialGridDeeperInterior
    (n : Nat) (mesh R : Real) (hmesh : 0 < mesh) (hR : 0 ≤ R)
    (hwide : 2 * R + 5 * mesh ≤ mesh * n) :
    closedBall (0 : Complex) R ⊆
      finiteCenteredRadialGridDeeperInterior n mesh := by
  intro z hz
  have hnorm : norm z ≤ R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hrelo : -R ≤ z.re := by
    linarith [neg_le_of_abs_le (hre.trans hnorm)]
  have hrehi : z.re ≤ R := by
    linarith [le_of_abs_le (hre.trans hnorm)]
  have himlo : -R ≤ z.im := by
    linarith [neg_le_of_abs_le (him.trans hnorm)]
  have himhi : z.im ≤ R := by
    linarith [le_of_abs_le (him.trans hnorm)]
  have hq : 2 * R / mesh + 5 ≤ (n : Real) := by
    calc
      2 * R / mesh + 5 = (2 * R + 5 * mesh) / mesh := by
        field_simp [hmesh.ne']
      _ ≤ (mesh * (n : Real)) / mesh :=
        (div_le_div_iff_of_pos_right hmesh).mpr hwide
      _ = (n : Real) := by field_simp [hmesh.ne']
  have hsumlo : -2 * R / mesh ≤ (z.re + z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hsumhi : (z.re + z.im) / mesh ≤ 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdifflo : -2 * R / mesh ≤ (z.re - z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdiffhi : (z.re - z.im) / mesh ≤ 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hneg : -2 * R / mesh = -(2 * R / mesh) := by ring
  rw [hneg] at hsumlo hdifflo
  have hc1 : (isingCenteredRadialGridCoordinate mesh n z).1 =
      (n : Real) + (z.re + z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  have hc2 : (isingCenteredRadialGridCoordinate mesh n z).2 =
      (n : Real) + (z.re - z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  change 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 3 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 3
  rw [hc1, hc2]
  constructor
  · linarith
  constructor
  · push_cast
    linarith
  constructor
  · linarith
  · push_cast
    linarith





theorem finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_neighbor
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (s : Set Complex) (hs : Convex Real s) (L : NNReal)
    (hinside : s ⊆ finiteCenteredRadialGridStrictInterior n mesh)
    (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * n) (hb : b < 2 * n),
      norm (value ⟨a + 1, ha⟩ ⟨b, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real))
    (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * n) (hb : b + 1 < 2 * n),
      norm (value ⟨a, ha⟩ ⟨b + 1, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real)) :
    LipschitzOnWith (4 * L)
      (finiteCenteredRadialGridInterpolant n mesh value) s := by
  apply lipschitzOnWith_of_open_local_on_convex _ _ _ hs
  intro z hz
  have hzint := hinside hz
  obtain ⟨i, hi, hi0, hi2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).1 hzint.1 hzint.2.1
  obtain ⟨j, hj, hj0, hj2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).2
        hzint.2.2.1 hzint.2.2.2
  let U : Set Complex := {w |
    (i : Real) < (isingCenteredRadialGridCoordinate mesh n w).1 ∧
    (isingCenteredRadialGridCoordinate mesh n w).1 < (i : Real) + 2 ∧
    (j : Real) < (isingCenteredRadialGridCoordinate mesh n w).2 ∧
    (isingCenteredRadialGridCoordinate mesh n w).2 < (j : Real) + 2}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hc1 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).1) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    have hc2 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).2) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    exact (isOpen_lt continuous_const hc1).inter
      ((isOpen_lt hc1 continuous_const).inter
        ((isOpen_lt continuous_const hc2).inter
          (isOpen_lt hc2 continuous_const)))
  · exact ⟨hi0, hi2, hj0, hj2⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    let xp : Real := (isingCenteredRadialGridCoordinate mesh n p).1 - i
    let xq : Real := (isingCenteredRadialGridCoordinate mesh n q).1 - i
    let yp : Real := (isingCenteredRadialGridCoordinate mesh n p).2 - j
    let yq : Real := (isingCenteredRadialGridCoordinate mesh n q).2 - j
    have hxp0 : 0 <= xp := by dsimp only [xp]; linarith [hp.1.1]
    have hxp2 : xp <= 2 := by dsimp only [xp]; linarith [hp.1.2.1]
    have hxq0 : 0 <= xq := by dsimp only [xq]; linarith [hq.1.1]
    have hxq2 : xq <= 2 := by dsimp only [xq]; linarith [hq.1.2.1]
    have hyp0 : 0 <= yp := by dsimp only [yp]; linarith [hp.1.2.2.1]
    have hyp2 : yp <= 2 := by dsimp only [yp]; linarith [hp.1.2.2.2]
    have hyq0 : 0 <= yq := by dsimp only [yq]; linarith [hq.1.2.2.1]
    have hyq2 : yq <= 2 := by dsimp only [yq]; linarith [hq.1.2.2.2]
    have H := finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist
      n mesh hmesh value i j hi hj xp xq yp yq (L : Real)
      hxp0 hxp2 hxq0 hxq2 hyp0 hyp2 hyq0 hyq2 L.2
      (hI i j (by omega) (by omega))
      (hI (i + 1) j (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega))
      (hI (i + 1) (j + 1) (by omega) (by omega))
      (hI i (j + 2) (by omega) (by omega))
      (hI (i + 1) (j + 2) (by omega) (by omega))
      (hJ i j (by omega) (by omega))
      (hJ i (j + 1) (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega))
      (hJ (i + 1) (j + 1) (by omega) (by omega))
      (hJ (i + 2) j (by omega) (by omega))
      (hJ (i + 2) (j + 1) (by omega) (by omega))
    have hpPoint :
        isingCenteredRadialGridCellPoint mesh n i j xp yp = p :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j p
    have hqPoint :
        isingCenteredRadialGridCellPoint mesh n i j xq yq = q :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j q
    rw [hpPoint, hqPoint] at H
    simpa [dist_eq_norm] using H



theorem finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_strictNeighbor
    (n : Nat) (mesh : Real) (hmesh : 0 < mesh)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (s : Set Complex) (hs : Convex Real s) (L : NNReal)
    (hinside : s ⊆ finiteCenteredRadialGridDeeperInterior n mesh)
    (hI : ∀ a b : Nat, ∀ (ha : a + 1 < 2 * n) (hb : b < 2 * n),
      a + 2 < 2 * n → b + 1 < 2 * n →
      norm (value ⟨a + 1, ha⟩ ⟨b, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real))
    (hJ : ∀ a b : Nat, ∀ (ha : a < 2 * n) (hb : b + 1 < 2 * n),
      a + 1 < 2 * n → b + 2 < 2 * n →
      norm (value ⟨a, ha⟩ ⟨b + 1, hb⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩) <= mesh * (L : Real)) :
    LipschitzOnWith (4 * L)
      (finiteCenteredRadialGridInterpolant n mesh value) s := by
  apply lipschitzOnWith_of_open_local_on_convex _ _ _ hs
  intro z hz
  have hzint := hinside hz
  obtain ⟨i, hi, hi0, hi2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).1 hzint.1 (by
        linarith [hzint.2.1])
  obtain ⟨j, hj, hj0, hj2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate mesh n z).2 hzint.2.2.1 (by
        linarith [hzint.2.2.2])
  have hi3 : i + 3 < 2 * n := by
    have hcast : (i : Real) + 3 < (2 * n : Nat) := by
      linarith [hi0, hzint.2.1]
    exact_mod_cast hcast
  have hj3 : j + 3 < 2 * n := by
    have hcast : (j : Real) + 3 < (2 * n : Nat) := by
      linarith [hj0, hzint.2.2.2]
    exact_mod_cast hcast
  let U : Set Complex := {w |
    (i : Real) < (isingCenteredRadialGridCoordinate mesh n w).1 ∧
    (isingCenteredRadialGridCoordinate mesh n w).1 < (i : Real) + 2 ∧
    (j : Real) < (isingCenteredRadialGridCoordinate mesh n w).2 ∧
    (isingCenteredRadialGridCoordinate mesh n w).2 < (j : Real) + 2}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hc1 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).1) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    have hc2 : Continuous (fun w : Complex =>
        (isingCenteredRadialGridCoordinate mesh n w).2) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    exact (isOpen_lt continuous_const hc1).inter
      ((isOpen_lt hc1 continuous_const).inter
        ((isOpen_lt continuous_const hc2).inter
          (isOpen_lt hc2 continuous_const)))
  · exact ⟨hi0, hi2, hj0, hj2⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    let xp : Real := (isingCenteredRadialGridCoordinate mesh n p).1 - i
    let xq : Real := (isingCenteredRadialGridCoordinate mesh n q).1 - i
    let yp : Real := (isingCenteredRadialGridCoordinate mesh n p).2 - j
    let yq : Real := (isingCenteredRadialGridCoordinate mesh n q).2 - j
    have hxp0 : 0 <= xp := by dsimp only [xp]; linarith [hp.1.1]
    have hxp2 : xp <= 2 := by dsimp only [xp]; linarith [hp.1.2.1]
    have hxq0 : 0 <= xq := by dsimp only [xq]; linarith [hq.1.1]
    have hxq2 : xq <= 2 := by dsimp only [xq]; linarith [hq.1.2.1]
    have hyp0 : 0 <= yp := by dsimp only [yp]; linarith [hp.1.2.2.1]
    have hyp2 : yp <= 2 := by dsimp only [yp]; linarith [hp.1.2.2.2]
    have hyq0 : 0 <= yq := by dsimp only [yq]; linarith [hq.1.2.2.1]
    have hyq2 : yq <= 2 := by dsimp only [yq]; linarith [hq.1.2.2.2]
    have H := finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist
      n mesh hmesh value i j hi hj xp xq yp yq (L : Real)
      hxp0 hxp2 hxq0 hxq2 hyp0 hyp2 hyq0 hyq2 L.2
      (hI i j (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) j (by omega) (by omega) (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hI i (j + 2) (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) (j + 2) (by omega) (by omega) (by omega) (by omega))
      (hJ i j (by omega) (by omega) (by omega) (by omega))
      (hJ i (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 2) j (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 2) (j + 1) (by omega) (by omega) (by omega) (by omega))
    have hpPoint :
        isingCenteredRadialGridCellPoint mesh n i j xp yp = p :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j p
    have hqPoint :
        isingCenteredRadialGridCellPoint mesh n i j xq yq = q :=
      isingCenteredRadialGridCellPoint_coordinate mesh hmesh.ne' n i j q
    rw [hpPoint, hqPoint] at H
    simpa [dist_eq_norm] using H



private theorem isingLinearTent_mem_unit (x : Real) :
    0 <= isingLinearTent x ∧ isingLinearTent x <= 1 := by
  unfold isingLinearTent
  constructor
  · exact le_max_left _ _
  · rw [max_le_iff]
    exact ⟨by norm_num, by linarith [abs_nonneg x]⟩

theorem isingLinearTent_lipschitzWith :
    LipschitzWith 1 isingLinearTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  unfold isingLinearTent
  calc
    |max 0 (1 - |x|) - max 0 (1 - |y|)| =
        |max (1 - |x|) 0 - max (1 - |y|) 0| := by
      rw [max_comm 0, max_comm 0]
    _ <= |(1 - |x|) - (1 - |y|)| :=
      abs_max_sub_max_le_abs _ _ _
    _ = abs (|x| - |y|) := by
      rw [show (1 - |x|) - (1 - |y|) = -(|x| - |y|) by ring, abs_neg]
    _ <= |x - y| := abs_abs_sub_abs_le_abs_sub x y

private theorem locallyLipschitz_mul_of_mem_unit
    {f g : Complex -> Real} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g)
    (hfmem : ∀ z, 0 <= f z ∧ f z <= 1)
    (hgmem : ∀ z, 0 <= g z ∧ g z <= 1) :
    LocallyLipschitz (fun z => f z * g z) := by
  intro z
  obtain ⟨Kf, u, hu, hfu⟩ := hf z
  obtain ⟨Kg, v, hv, hgv⟩ := hg z
  refine ⟨Kf + Kg, u ∩ v, Filter.inter_mem hu hv, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  have hfp := hfmem p
  have hfq := hfmem q
  have hgp := hgmem p
  have hgq := hgmem q
  have hfd := hfu.dist_le_mul p hp.1 q hq.1
  have hgd := hgv.dist_le_mul p hp.2 q hq.2
  simp only [Real.dist_eq] at hfd hgd ⊢
  calc
    |f p * g p - f q * g q| =
        |(f p - f q) * g p + f q * (g p - g q)| := by
      congr 1
      ring
    _ <= |(f p - f q) * g p| + |f q * (g p - g q)| :=
      abs_add_le _ _
    _ = |f p - f q| * |g p| + |f q| * |g p - g q| := by
      rw [abs_mul, abs_mul]
    _ <= |f p - f q| + |g p - g q| := by
      rw [abs_of_nonneg hgp.1, abs_of_nonneg hfq.1]
      exact add_le_add
        (mul_le_of_le_one_right (abs_nonneg _) hgp.2)
        (mul_le_of_le_one_left (abs_nonneg _) hfq.2)
    _ <= (Kf : Real) * dist p q + (Kg : Real) * dist p q :=
      add_le_add hfd hgd
    _ = ((Kf + Kg : NNReal) : Real) * dist p q := by
      push_cast
      ring

private theorem locallyLipschitz_complex_add
    {f g : Complex -> Complex} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g) : LocallyLipschitz (fun z => f z + g z) := by
  have hadd : LocallyLipschitz (fun p : Complex × Complex => p.1 + p.2) :=
    (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).locallyLipschitz
  exact hadd.comp (hf.prodMk hg)

private theorem locallyLipschitz_finset_sum
    {α : Type*} (s : Finset α) (f : α -> Complex -> Complex)
    (hf : ∀ a ∈ s, LocallyLipschitz (f a)) :
    LocallyLipschitz (fun z => ∑ a ∈ s, f a z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (LocallyLipschitz.const (α := Complex) (0 : Complex))
  | @insert a s ha ih =>
      simp only [Finset.mem_insert] at hf
      simpa [Finset.sum_insert ha] using locallyLipschitz_complex_add
        (hf a (by simp)) (ih (fun b hb => hf b (by simp [hb])))




theorem finiteRadialGridInterpolant_locallyLipschitz
    (m : Nat) (mesh : Real)
    (value : Fin m -> Fin m -> Complex) :
    LocallyLipschitz (finiteRadialGridInterpolant m mesh value) := by
  classical
  have hre : LipschitzWith ‖mesh⁻¹‖₊ (fun z : Complex => z.re / mesh) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (lipschitzWith_smul (mesh⁻¹ : Real)).comp RCLike.lipschitzWith_re
  have him : LipschitzWith ‖mesh⁻¹‖₊ (fun z : Complex => z.im / mesh) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (lipschitzWith_smul (mesh⁻¹ : Real)).comp RCLike.lipschitzWith_im
  have hc1 : LocallyLipschitz (fun z : Complex =>
      (isingRadialGridCoordinate mesh z).1) := by
    unfold isingRadialGridCoordinate
    exact ((hre.vadd him).vsub
      (LipschitzWith.const (1 / 2))).locallyLipschitz
  have hc2 : LocallyLipschitz (fun z : Complex =>
      (isingRadialGridCoordinate mesh z).2) := by
    unfold isingRadialGridCoordinate
    exact ((hre.vsub him).vsub
      (LipschitzWith.const (1 / 2))).locallyLipschitz
  unfold finiteRadialGridInterpolant
  apply locallyLipschitz_finset_sum Finset.univ
  intro i _hi
  apply locallyLipschitz_finset_sum Finset.univ
  intro j _hj
  let fi : Complex -> Real := fun z =>
    isingLinearTent ((isingRadialGridCoordinate mesh z).1 - (i.1 : Real))
  let gj : Complex -> Real := fun z =>
    isingLinearTent ((isingRadialGridCoordinate mesh z).2 - (j.1 : Real))
  have hfi : LocallyLipschitz fi := by
    apply isingLinearTent_lipschitzWith.locallyLipschitz.comp
    exact ((LipschitzWith.prod_fst.vsub
      LipschitzWith.prod_snd).locallyLipschitz).comp
        (hc1.prodMk (LocallyLipschitz.const (i.1 : Real)))
  have hgj : LocallyLipschitz gj := by
    apply isingLinearTent_lipschitzWith.locallyLipschitz.comp
    exact ((LipschitzWith.prod_fst.vsub
      LipschitzWith.prod_snd).locallyLipschitz).comp
        (hc2.prodMk (LocallyLipschitz.const (j.1 : Real)))
  have hprod : LocallyLipschitz (fun z => fi z * gj z) :=
    locallyLipschitz_mul_of_mem_unit hfi hgj
      (fun _ => isingLinearTent_mem_unit _)
      (fun _ => isingLinearTent_mem_unit _)
  have hscale : LocallyLipschitz (fun r : Real =>
      ((r : Real) : Complex) * value i j) := by
    have h : LipschitzWith ‖value i j‖₊ (fun r : Real =>
        ((r : Real) : Complex) * value i j) := by
      apply LipschitzWith.of_dist_le_mul
      intro r t
      calc
        dist (((r : Real) : Complex) * value i j)
            (((t : Real) : Complex) * value i j) =
            |r - t| * norm (value i j) := by
          rw [dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
            Complex.norm_real, Real.norm_eq_abs]
        _ = (‖value i j‖₊ : Real) * dist r t := by
          simp only [Real.dist_eq, coe_nnnorm]
          ring
        _ <= (‖value i j‖₊ : Real) * dist r t := le_rfl
    exact h.locallyLipschitz
  exact hscale.comp hprod

theorem finiteCenteredRadialGridInterpolant_locallyLipschitz
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
    LocallyLipschitz (finiteCenteredRadialGridInterpolant n mesh value) := by
  unfold finiteCenteredRadialGridInterpolant
  apply (finiteRadialGridInterpolant_locallyLipschitz
    (2 * n) mesh value).comp
  exact (LipschitzWith.id.vadd
    (LipschitzWith.const ((mesh * n : Real) : Complex))).locallyLipschitz

theorem fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz
    (k : Nat) :
    LocallyLipschitz
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) := by
  unfold fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
  apply (finiteCenteredRadialGridInterpolant_locallyLipschitz _ _ _).comp
  exact star_isometry.lipschitz.locallyLipschitz



theorem exists_lipschitzOnWith_forall_lt_of_locallyLipschitz
    (F : Nat -> Complex -> Complex) (hF : ∀ k, LocallyLipschitz (F k))
    (K : Set Complex) (hK : IsCompact K) (N : Nat) :
    ∃ C : NNReal, ∀ k < N, LipschitzOnWith C (F k) K := by
  induction N with
  | zero => exact ⟨0, by omega⟩
  | succ N ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨D, hD⟩ :=
        LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
          (hF N).locallyLipschitzOn
      refine ⟨max C D, ?_⟩
      intro k hk
      by_cases hkn : k < N
      · exact (hC k hkn).weaken (le_max_left _ _)
      · have hkeq : k = N := by omega
        subst k
        exact hD.weaken (le_max_right _ _)






theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_neighbor
    (k : Nat) (R : Real) (L : NNReal) (hR : 0 <= R)
    (hwide : 2 * R + 4 * fkIsingExpandingSquareScale k <=
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
    (hI : ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))
    (hJ : ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) :
    LipschitzOnWith (4 * L)
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (closedBall (0 : Complex) R) := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) i j /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have hinside := closedBall_subset_finiteCenteredRadialGridStrictInterior
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) R
    (fkIsingExpandingSquareScale_pos k) hR hwide
  have hf := finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_neighbor
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
    (fkIsingExpandingSquareScale_pos k) value (closedBall 0 R)
    (convex_closedBall 0 R) L hinside hI hJ
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hzs : star z ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hws : star w ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hw
  have h := hf.dist_le_mul (star z) hzs (star w) hws
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value,
    star_isometry.dist_eq] using h




theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_strictNeighbor
    (k : Nat) (R : Real) (L : NNReal) (hR : 0 <= R)
    (hwide : 2 * R + 5 * fkIsingExpandingSquareScale k <=
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
    (hI : ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      a + 2 < 2 * fkIsingExpandingSquareSide k →
      b + 1 < 2 * fkIsingExpandingSquareSide k →
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))
    (hJ : ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      a + 1 < 2 * fkIsingExpandingSquareSide k →
      b + 2 < 2 * fkIsingExpandingSquareSide k →
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) :
    LipschitzOnWith (4 * L)
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (closedBall (0 : Complex) R) := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) i j /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have hinside := closedBall_subset_finiteCenteredRadialGridDeeperInterior
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) R
    (fkIsingExpandingSquareScale_pos k) hR hwide
  have hf := finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_strictNeighbor
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
    (fkIsingExpandingSquareScale_pos k) value (closedBall 0 R)
    (convex_closedBall 0 R) L hinside hI hJ
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hzs : star z ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hws : star w ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hw
  have h := hf.dist_le_mul (star z) hzs (star w) hws
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value,
    star_isometry.dist_eq] using h





theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_horizontalAdjacent_norm_sub_le_of_neighbor
    (k i j : Nat)
    (hi : i + 2 < 2 * fkIsingExpandingSquareSide k)
    (hj : j + 1 < 2 * fkIsingExpandingSquareSide k)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hI : forall a b
      (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L)
    (hJ : forall a b
      (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L) :
    norm
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) i j x y)) -
        fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) (i + 1) j x' y'))) <=
      (fkIsingExpandingSquareScale k * L) *
        ((1 - x) + x' + |y - y'|) := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun a b =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) a b /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have h :=
    finiteCenteredRadialGridInterpolant_horizontalAdjacent_norm_sub_le
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
      (fkIsingExpandingSquareScale_pos k).ne' value i j hi hj
      x x' y y' (fkIsingExpandingSquareScale k * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      (hI i j (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega))
      (hJ i j (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega))
      (hI (i + 1) j (by omega) (by omega))
      (hI (i + 1) (j + 1) (by omega) (by omega))
      (hJ (i + 2) j (by omega) (by omega))
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value] using h



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_verticalAdjacent_norm_sub_le_of_neighbor
    (k i j : Nat)
    (hi : i + 1 < 2 * fkIsingExpandingSquareSide k)
    (hj : j + 2 < 2 * fkIsingExpandingSquareSide k)
    (x x' y y' L : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hx0' : 0 <= x') (hx1' : x' <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (hy0' : 0 <= y') (hy1' : y' <= 1)
    (hI : forall a b
      (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L)
    (hJ : forall a b
      (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k)
              ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * L) :
    norm
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) i j x y)) -
        fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k
          ((starRingEnd Complex)
            (isingCenteredRadialGridCellPoint
              (fkIsingExpandingSquareScale k)
              (fkIsingExpandingSquareSide k) i (j + 1) x' y'))) <=
      (fkIsingExpandingSquareScale k * L) *
        (|x - x'| + (1 - y) + y') := by
  let value : Fin (2 * fkIsingExpandingSquareSide k) ->
      Fin (2 * fkIsingExpandingSquareSide k) -> Complex := fun a b =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable
        (fkIsingExpandingSquareSide k)
        (fkIsingExpandingSquareSide_pos k) a b /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)
  have h :=
    finiteCenteredRadialGridInterpolant_verticalAdjacent_norm_sub_le
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k)
      (fkIsingExpandingSquareScale_pos k).ne' value i j hi hj
      x x' y y' (fkIsingExpandingSquareScale k * L)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
      (hI i j (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega))
      (hJ i j (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega))
      (hI i (j + 2) (by omega) (by omega))
      (hJ i (j + 1) (by omega) (by omega))
      (hJ (i + 1) (j + 1) (by omega) (by omega))
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, value] using h




def FKIsingExpandingCenteredNeighborTransport : Prop :=
  ∃ L : NNReal, ∃ N : Nat, ∀ k, N <= k ->
    (∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) ∧
    (∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))




def FKIsingExpandingCenteredStrictNeighborTransport : Prop :=
  ∃ L : NNReal, ∃ N : Nat, ∀ k, N <= k ->
    (∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
      a + 2 < 2 * fkIsingExpandingSquareSide k ->
      b + 1 < 2 * fkIsingExpandingSquareSide k ->
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real)) ∧
    (∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      a + 1 < 2 * fkIsingExpandingSquareSide k ->
      b + 2 < 2 * fkIsingExpandingSquareSide k ->
      norm
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservable
              (fkIsingExpandingSquareSide k)
              (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
            (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
        fkIsingExpandingSquareScale k * (L : Real))



def isingCenteredRadialIndexSector (n a b : Nat) : Fin 4 :=
  if a < n then
    if b < n then 0 else 1
  else if b < n then 2 else 3


def FKIsingExpandingCenteredHorizontalNeighborBound
    (L : NNReal) (k a b : Nat) : Prop :=
  ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
    (hb : b < 2 * fkIsingExpandingSquareSide k),
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a + 1, ha⟩ ⟨b, hb⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) ≤
      fkIsingExpandingSquareScale k * (L : Real)


def FKIsingExpandingCenteredVerticalNeighborBound
    (L : NNReal) (k a b : Nat) : Prop :=
  ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
    (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a, ha⟩ ⟨b + 1, hb⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k) ⟨a, by omega⟩ ⟨b, by omega⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) ≤
      fkIsingExpandingSquareScale k * (L : Real)




theorem fkIsingExpandingCenteredNeighborTransport_of_four_sector_bounds
    (L : NNReal) (N : Nat)
    (hI : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ a b,
      isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) a b = q →
        FKIsingExpandingCenteredHorizontalNeighborBound L k a b)
    (hJ : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ a b,
      isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) a b = q →
        FKIsingExpandingCenteredVerticalNeighborBound L k a b) :
    FKIsingExpandingCenteredNeighborTransport := by
  refine ⟨L, N, ?_⟩
  intro k hk
  constructor
  · intro a b ha hb
    exact hI (isingCenteredRadialIndexSector
      (fkIsingExpandingSquareSide k) a b) k hk a b rfl ha hb
  · intro a b ha hb
    exact hJ (isingCenteredRadialIndexSector
      (fkIsingExpandingSquareSide k) a b) k hk a b rfl ha hb





theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredNeighbor
    (hneighbor : FKIsingExpandingCenteredNeighborTransport) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
  obtain ⟨L, N, hN⟩ := hneighbor
  constructor
  intro K hK _hKU
  obtain ⟨R, hKR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Complex)).mp hK.isBounded
  let R0 : Real := max R 0
  have hR0 : 0 <= R0 := le_max_right _ _
  have hKR0 : K ⊆ closedBall (0 : Complex) R0 :=
    hKR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hevent :=
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (2 * R0) 4
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Nr, hNr⟩ := hevent
  let M : Nat := max N Nr
  obtain ⟨Cpre, hpre⟩ :=
    exists_lipschitzOnWith_forall_lt_of_locallyLipschitz
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz
      K hK M
  refine ⟨max Cpre (4 * L), 1, by norm_num, ?_⟩
  intro k
  apply LipschitzOnWith.holderOnWith
  by_cases hk : k < M
  · exact (hpre k hk).weaken (le_max_left _ _)
  · have hMk : M <= k := by omega
    have hNk : N <= k := le_trans (le_max_left N Nr) hMk
    have hNrk : Nr <= k := le_trans (le_max_right N Nr) hMk
    have hrad := hNr k hNrk
    have hwide : 2 * R0 + 4 * fkIsingExpandingSquareScale k <=
        fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k := by
      nlinarith
    have hbound := hN k hNk
    exact
      ((fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_neighbor
          k R0 L hR0 hwide hbound.1 hbound.2).mono hKR0).weaken
        (le_max_right _ _)




theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_of_centeredStrictNeighbor
    (hneighbor : FKIsingExpandingCenteredStrictNeighborTransport) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
  obtain ⟨L, N, hN⟩ := hneighbor
  constructor
  intro K hK _hKU
  obtain ⟨R, hKR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Complex)).mp hK.isBounded
  let R0 : Real := max R 0
  have hR0 : 0 <= R0 := le_max_right _ _
  have hKR0 : K ⊆ closedBall (0 : Complex) R0 :=
    hKR.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hevent :=
    fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior
      (2 * R0) 5
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Nr, hNr⟩ := hevent
  let M : Nat := max N Nr
  obtain ⟨Cpre, hpre⟩ :=
    exists_lipschitzOnWith_forall_lt_of_locallyLipschitz
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz
      K hK M
  refine ⟨max Cpre (4 * L), 1, by norm_num, ?_⟩
  intro k
  apply LipschitzOnWith.holderOnWith
  by_cases hk : k < M
  · exact (hpre k hk).weaken (le_max_left _ _)
  · have hMk : M <= k := by omega
    have hNk : N <= k := le_trans (le_max_left N Nr) hMk
    have hNrk : Nr <= k := le_trans (le_max_right N Nr) hMk
    have hrad := hNr k hNrk
    have hwide : 2 * R0 + 5 * fkIsingExpandingSquareScale k <=
        fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k := by
      nlinarith
    have hbound := hN k hNk
    exact
      ((fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_strictNeighbor
          k R0 L hR0 hwide hbound.1 hbound.2).mono hKR0).weaken
        (le_max_right _ _)





theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_radialPatch
    (n m a b : Nat) (hn : 0 < n) (hm : m ≤ n)
    (ha : a < m) (hb : b < m) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ =
      fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp only [fkIsingSquareBoundaryCenteredRadialPatchFullObservable,
    fkIsingSquareBoundaryRadialPatchFullObservable]
  rw [fkIsingSquareCenteredRadialPatchEdge_add_side_eq_radialPatchEdge
    n m a b hm ha hb]



theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
        ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩ =
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
        n m baseI baseJ R hn hm hfitI hfitJ p := by
  unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_radialPatch




theorem
    fkIsingSquareBoundaryCenteredRadialPatch_add_side_normalizedNeighbor_norm_sub_le
    (n m baseI baseJ R rho : Nat) (mesh d H V : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r ≤ V)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hradius : d ≤ mesh * (rho : Real))
    (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
            ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩ /
          (Real.sqrt (2 * mesh) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
            ⟨n + (baseI + p'.1.1), by have := p'.1.2; omega⟩
            ⟨n + (baseJ + p'.2.1), by have := p'.2.2; omega⟩ /
          (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * H := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
      n m baseI baseJ R hn hm hfitI hfitJ p,
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
      n m baseI baseJ R hn hm hfitI hfitJ p']
  exact
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
      n m baseI baseJ R rho mesh d H V hn hm hm2
      hfitI hfitJ hmesh r hdeep hV hd hH hradius hscale
      p p' hrho hp hp' hpp'





theorem
    fkIsingSquareBoundaryCenteredRadialPatch_add_side_cell_edges_halfScale
    (n m baseI baseJ R rho cutoff : Nat)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hcutoff : 0 < cutoff)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 cutoff)
    (hmcutoff : m ≤ 2 * cutoff) (hmrho : m ≤ 2 * rho)
    (a b : Nat) (ha0 : 0 < a) (haR : a < R)
    (hb0 : 0 < b) (hbR : b < R)
    (hrho : 0 < rho)
    (hmarginN : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
    (hmarginE : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b, by omega⟩))
    (hmarginS : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
    (hmarginW : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)) :
    let F : IsingLeapfrogBox R → Complex := fun p ↦
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
        ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩
    let normalization := Real.sqrt (2 * (1 / (m : Real)))
    let delta := (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real))
    ‖F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization -
        F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧
      ‖F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization -
        F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧
      ‖F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization -
        F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤
          2 * delta ∧
      ‖F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization -
        F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤ 2 * delta := by
  let F : IsingLeapfrogBox R → Complex := fun p ↦
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨n + (baseI + p.1.1), by have := p.1.2; omega⟩
      ⟨n + (baseJ + p.2.1), by have := p.2.2; omega⟩
  have hF : F = fkIsingSquareBoundaryRadialPatchFullObservableWindow
      n m baseI baseJ R hn hm hfitI hfitJ := by
    funext p
    exact
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_add_side_eq_window
        n m baseI baseJ R hn hm hfitI hfitJ p
  have h :=
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_cell_edges_halfScale
      n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ
      hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho
      hmarginN hmarginE hmarginS hmarginW
  rw [← hF] at h
  simpa only [F] using h







theorem
    fkIsingSquareBoundaryCenteredRadialPatch_normalizedNeighbor_norm_sub_le_of_radialWindow
    (n m baseI baseJ R rho : Nat) (mesh d H V : Real)
    (hn : 0 < n) (hm : m <= n) (hm2 : 2 <= m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : forall q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r <= V)
    (hd : 0 <= d) (hH : 0 <= H)
    (hradius : d <= mesh * (rho : Real))
    (hscale : 1032080 * V <= H ^ 2 * d ^ 3)
    (i j i' j' : Fin (2 * n))
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p')
    (hfirst :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j =
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p)
    (hsecond :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i' j' =
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p') :
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
          (Real.sqrt (2 * mesh) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i' j' /
          (Real.sqrt (2 * mesh) : Complex)) <= mesh * H := by
  rw [hfirst, hsecond]
  exact
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
      n m baseI baseJ R rho mesh d H V hn hm hm2 hfitI hfitJ hmesh
      r hdeep hV hd hH hradius hscale p p' hrho hp hp' hpp'

end

end StatMech.Universality
