/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexPeriodicStraightIntersection









open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice

private theorem affineInt_mem_interval' (a b : Int) (t : unitInterval) :
    ((min a b : Int) : Real) <=
        (t : Real) * ((b : Real) - (a : Real)) + (a : Real) /\
      (t : Real) * ((b : Real) - (a : Real)) + (a : Real) <=
        ((max a b : Int) : Real) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    have habR : (a : Real) <= b := by exact_mod_cast hab
    constructor <;> nlinarith [t.2.1, t.2.2]
  · rw [min_eq_right hba, max_eq_left hba]
    have hbaR : (b : Real) <= a := by exact_mod_cast hba
    constructor <;> nlinarith [t.2.1, t.2.2]

@[simp] theorem triangularSegment_re_scaled
    (x y : Site 2) (t : unitInterval) :
    3 * (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex y) t).re =
        (t : Real) * ((3 * y 0 : Int) - (3 * x 0 : Int)) +
          (3 * x 0 : Int) := by
  rw [triangularSegment_re]
  push_cast
  ring

@[simp] theorem triangularSegment_im_scaled
    (x y : Site 2) (t : unitInterval) :
    3 * (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex y) t).im =
        (t : Real) * ((3 * y 1 : Int) - (3 * x 1 : Int)) +
          (3 * x 1 : Int) := by
  rw [triangularSegment_im]
  push_cast
  ring



theorem triHexCanonicalPairedSegments_crossing (a : TriHexEdgeIndex) :
    ∃ t u : unitInterval,
      Path.segment (triangularPlaneVertex a.1)
          (triangularPlaneVertex (a.1 + triangularStep a.2)) t =
        Path.segment
          (hexagonalPlaneVertex ((triHexIndexEquiv a).1, false))
          (hexagonalPlaneVertex
            ((triHexIndexEquiv a).1 + hexagonalStep (triHexIndexEquiv a).2,
              true)) u := by
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  refine ⟨half, half, ?_⟩
  apply Complex.ext
  · apply (mul_left_cancel₀ (by norm_num : (3 : Real) ≠ 0))
    rw [triangularSegment_re_scaled, hexagonalSegment_re_scaled]
    rcases a with ⟨x, i⟩
    have hxHead : Matrix.vecHead x = x 0 := rfl
    have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
    fin_cases i <;>
      simp [half, triHexIndexEquiv, triangularStep, hexagonalStep,
        hexagonalScaledCoordinate, hxHead, hxTail] <;> ring
  · apply (mul_left_cancel₀ (by norm_num : (3 : Real) ≠ 0))
    rw [triangularSegment_im_scaled, hexagonalSegment_im_scaled]
    rcases a with ⟨x, i⟩
    have hxHead : Matrix.vecHead x = x 0 := rfl
    have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
    fin_cases i <;>
      simp [half, triHexIndexEquiv, triangularStep, hexagonalStep,
        hexagonalScaledCoordinate, hxHead, hxTail] <;> ring

set_option maxHeartbeats 800000 in



theorem triHexCanonicalSegments_of_crossing
    (x z : Site 2) (i j : Fin 3) (p : Complex)
    (hp : p ∈ Set.range (Path.segment
      (triangularPlaneVertex x)
      (triangularPlaneVertex (x + triangularStep i))))
    (hq : p ∈ Set.range (Path.segment
      (hexagonalPlaneVertex (z, false))
      (hexagonalPlaneVertex (z + hexagonalStep j, true)))) :
    triHexIndexEquiv (x, i) = (z, j) := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨u, hu⟩ := hq
  have hre := congrArg Complex.re (ht.trans hu.symm)
  have him := congrArg Complex.im (ht.trans hu.symm)
  let a0 : Int := 3 * x 0
  let a1 : Int := 3 * x 1
  let b0 : Int := 3 * (x + triangularStep i) 0
  let b1 : Int := 3 * (x + triangularStep i) 1
  let c0 : Int := hexagonalScaledCoordinate (z, false) 0
  let c1 : Int := hexagonalScaledCoordinate (z, false) 1
  let d0 : Int := hexagonalScaledCoordinate (z + hexagonalStep j, true) 0
  let d1 : Int := hexagonalScaledCoordinate (z + hexagonalStep j, true) 1
  have h0eq :
      (t : Real) * ((b0 : Real) - (a0 : Real)) + (a0 : Real) =
        (u : Real) * ((d0 : Real) - (c0 : Real)) + (c0 : Real) := by
    calc
      _ = 3 * (Path.segment (triangularPlaneVertex x)
          (triangularPlaneVertex (x + triangularStep i)) t).re := by
        exact (triangularSegment_re_scaled x
          (x + triangularStep i) t).symm
      _ = 3 * (Path.segment (hexagonalPlaneVertex (z, false))
          (hexagonalPlaneVertex (z + hexagonalStep j, true)) u).re :=
        congrArg (fun r : Real => 3 * r) hre
      _ = _ := hexagonalSegment_re_scaled
        (z, false) (z + hexagonalStep j, true) u
  have h1eq :
      (t : Real) * ((b1 : Real) - (a1 : Real)) + (a1 : Real) =
        (u : Real) * ((d1 : Real) - (c1 : Real)) + (c1 : Real) := by
    calc
      _ = 3 * (Path.segment (triangularPlaneVertex x)
          (triangularPlaneVertex (x + triangularStep i)) t).im := by
        exact (triangularSegment_im_scaled x
          (x + triangularStep i) t).symm
      _ = 3 * (Path.segment (hexagonalPlaneVertex (z, false))
          (hexagonalPlaneVertex (z + hexagonalStep j, true)) u).im :=
        congrArg (fun r : Real => 3 * r) him
      _ = _ := hexagonalSegment_im_scaled
        (z, false) (z + hexagonalStep j, true) u
  have ha0 := affineInt_mem_interval' a0 b0 t
  have hc0 := affineInt_mem_interval' c0 d0 u
  have ha1 := affineInt_mem_interval' a1 b1 t
  have hc1 := affineInt_mem_interval' c1 d1 u
  have has := affineInt_mem_interval' (a0 + a1) (b0 + b1) t
  have hcs := affineInt_mem_interval' (c0 + c1) (d0 + d1) u
  have hseq :
      (t : Real) * (((b0 + b1 : Int) : Real) -
          ((a0 + a1 : Int) : Real)) + ((a0 + a1 : Int) : Real) =
        (u : Real) * (((d0 + d1 : Int) : Real) -
          ((c0 + c1 : Int) : Real)) + ((c0 + c1 : Int) : Real) := by
    push_cast
    linarith
  have h00R : ((min a0 b0 : Int) : Real) <= ((max c0 d0 : Int) : Real) :=
    ha0.1.trans (h0eq.trans_le hc0.2)
  have h01R : ((min c0 d0 : Int) : Real) <= ((max a0 b0 : Int) : Real) :=
    hc0.1.trans (h0eq.symm.trans_le ha0.2)
  have h10R : ((min a1 b1 : Int) : Real) <= ((max c1 d1 : Int) : Real) :=
    ha1.1.trans (h1eq.trans_le hc1.2)
  have h11R : ((min c1 d1 : Int) : Real) <= ((max a1 b1 : Int) : Real) :=
    hc1.1.trans (h1eq.symm.trans_le ha1.2)
  have hs0R : ((min (a0 + a1) (b0 + b1) : Int) : Real) <=
      ((max (c0 + c1) (d0 + d1) : Int) : Real) :=
    has.1.trans (hseq.trans_le hcs.2)
  have hs1R : ((min (c0 + c1) (d0 + d1) : Int) : Real) <=
      ((max (a0 + a1) (b0 + b1) : Int) : Real) :=
    hcs.1.trans (hseq.symm.trans_le has.2)
  have h00 : min a0 b0 <= max c0 d0 := by exact_mod_cast h00R
  have h01 : min c0 d0 <= max a0 b0 := by exact_mod_cast h01R
  have h10 : min a1 b1 <= max c1 d1 := by exact_mod_cast h10R
  have h11 : min c1 d1 <= max a1 b1 := by exact_mod_cast h11R
  have hs0 : min (a0 + a1) (b0 + b1) <= max (c0 + c1) (d0 + d1) := by
    exact_mod_cast hs0R
  have hs1 : min (c0 + c1) (d0 + d1) <= max (a0 + a1) (b0 + b1) := by
    exact_mod_cast hs1R
  dsimp [a0, a1, b0, b1, c0, c1, d0, d1] at h00 h01 h10 h11 hs0 hs1
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  fin_cases i <;> fin_cases j
  all_goals
    simp [triHexIndexEquiv, triangularStep, hexagonalStep,
      hexagonalScaledCoordinate, funext_iff, hxHead, hxTail]
      at h00 h01 h10 h11 hs0 hs1 ⊢
  all_goals omega



theorem triangularStraightEdgeArc_range_chart
    {x y : Site 2} (hxy : triangularGraph.Adj x y) :
    let e : triangularGraph.edgeSet := ⟨s(x, y), hxy⟩
    let a := triangularEdgeChartEquiv.symm e
    Set.range (triangularStraightEdgeArc hxy) =
      Set.range (Path.segment (triangularPlaneVertex a.1)
        (triangularPlaneVertex (a.1 + triangularStep a.2))) := by
  dsimp only
  let e : triangularGraph.edgeSet := ⟨s(x, y), hxy⟩
  let a := triangularEdgeChartEquiv.symm e
  change Set.range (triangularStraightEdgeArc hxy) =
    Set.range (Path.segment (triangularPlaneVertex a.1)
      (triangularPlaneVertex (a.1 + triangularStep a.2)))
  have ha : triangularIndexedEdge a = s(x, y) := by
    exact congrArg Subtype.val (triangularEdgeChartEquiv.apply_symm_apply e)
  rw [triangularIndexedEdge, Sym2.eq_iff] at ha
  rcases ha with ha | ha
  · simp only [triangularStraightEdgeArc, Path.range_segment]
    rw [ha.2, ha.1]
  · simp only [triangularStraightEdgeArc, Path.range_segment]
    rw [ha.2, ha.1]
    exact segment_symm Real _ _



theorem hexagonalStraightEdgeArc_range_chart
    {x y : HexVertex} (hxy : hexagonalGraph.Adj x y) :
    let e : hexagonalGraph.edgeSet := ⟨s(x, y), hxy⟩
    let a := hexagonalEdgeChartEquiv.symm e
    Set.range (hexagonalStraightEdgeArc hxy) =
      Set.range (Path.segment (hexagonalPlaneVertex (a.1, false))
        (hexagonalPlaneVertex (a.1 + hexagonalStep a.2, true))) := by
  dsimp only
  let e : hexagonalGraph.edgeSet := ⟨s(x, y), hxy⟩
  let a := hexagonalEdgeChartEquiv.symm e
  change Set.range (hexagonalStraightEdgeArc hxy) =
    Set.range (Path.segment (hexagonalPlaneVertex (a.1, false))
      (hexagonalPlaneVertex (a.1 + hexagonalStep a.2, true)))
  have ha : hexagonalIndexedEdge a = s(x, y) := by
    exact congrArg Subtype.val (hexagonalEdgeChartEquiv.apply_symm_apply e)
  rw [hexagonalIndexedEdge, Sym2.eq_iff] at ha
  rcases ha with ha | ha
  · simp only [hexagonalStraightEdgeArc, Path.range_segment]
    rw [ha.2, ha.1]
  · simp only [hexagonalStraightEdgeArc, Path.range_segment]
    rw [ha.2, ha.1]
    exact segment_symm Real _ _



theorem triHexStraightEdge_crossing_iff_dual
    {x y : Site 2} {z w : HexVertex}
    (hxy : triangularGraph.Adj x y) (hzw : hexagonalGraph.Adj z w) :
    (∃ t u,
      triangularStraightEdgeArc hxy t = hexagonalStraightEdgeArc hzw u) ↔
      triHexDualEdgeEquiv ⟨s(x, y), hxy⟩ = ⟨s(z, w), hzw⟩ := by
  let e : triangularGraph.edgeSet := ⟨s(x, y), hxy⟩
  let f : hexagonalGraph.edgeSet := ⟨s(z, w), hzw⟩
  let a := triangularEdgeChartEquiv.symm e
  let b := hexagonalEdgeChartEquiv.symm f
  have he : triangularEdgeChart a = e :=
    triangularEdgeChartEquiv.apply_symm_apply e
  have hf : hexagonalEdgeChart b = f :=
    hexagonalEdgeChartEquiv.apply_symm_apply f
  have hrangeP := triangularStraightEdgeArc_range_chart hxy
  have hrangeD := hexagonalStraightEdgeArc_range_chart hzw
  change Set.range (triangularStraightEdgeArc hxy) =
      Set.range (Path.segment (triangularPlaneVertex a.1)
        (triangularPlaneVertex (a.1 + triangularStep a.2))) at hrangeP
  change Set.range (hexagonalStraightEdgeArc hzw) =
      Set.range (Path.segment (hexagonalPlaneVertex (b.1, false))
        (hexagonalPlaneVertex (b.1 + hexagonalStep b.2, true))) at hrangeD
  constructor
  · rintro ⟨t, u, htu⟩
    let p := triangularStraightEdgeArc hxy t
    have hp : p ∈ Set.range (triangularStraightEdgeArc hxy) := ⟨t, rfl⟩
    have hq : p ∈ Set.range (hexagonalStraightEdgeArc hzw) := ⟨u, htu.symm⟩
    rw [hrangeP] at hp
    rw [hrangeD] at hq
    have hab := triHexCanonicalSegments_of_crossing a.1 b.1 a.2 b.2 p hp hq
    change triHexDualEdgeEquiv e = f
    rw [← he, ← hf]
    apply Subtype.ext
    rw [triHexDualEdgeEquiv_chart, hab]
    rfl
  · intro hdual
    have hdual' :
        triHexDualEdgeEquiv (triangularEdgeChart a) =
          hexagonalEdgeChart b := by
      rw [he, hf]
      exact hdual
    have hab : triHexIndexEquiv a = b := by
      have hpaired : triHexDualEdgeEquiv (triangularEdgeChart a) =
          hexagonalEdgeChart (triHexIndexEquiv a) := by
        apply Subtype.ext
        exact triHexDualEdgeEquiv_chart a
      rw [hpaired] at hdual'
      exact hexagonalEdgeChart_injective hdual'
    obtain ⟨t0, u0, h0⟩ := triHexCanonicalPairedSegments_crossing a
    let p := Path.segment (triangularPlaneVertex a.1)
      (triangularPlaneVertex (a.1 + triangularStep a.2)) t0
    have hpCanon : p ∈ Set.range (Path.segment (triangularPlaneVertex a.1)
        (triangularPlaneVertex (a.1 + triangularStep a.2))) := ⟨t0, rfl⟩
    have hqCanon : p ∈ Set.range (Path.segment
        (hexagonalPlaneVertex (b.1, false))
        (hexagonalPlaneVertex (b.1 + hexagonalStep b.2, true))) := by
      refine ⟨u0, ?_⟩
      dsimp [p]
      rw [← hab]
      exact h0.symm
    rw [← hrangeP] at hpCanon
    rw [← hrangeD] at hqCanon
    obtain ⟨t, ht⟩ := hpCanon
    obtain ⟨u, hu⟩ := hqCanon
    exact ⟨t, u, ht.trans hu.symm⟩

end StatMech.FK.PeriodicPlanar
