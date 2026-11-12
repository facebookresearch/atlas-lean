/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexPeriodicPlaneEmbedding









open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice

@[simp] theorem triangularCanonicalSegment_re
    (x : Site 2) (i : Fin 3) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex (x + triangularStep i)) t).re =
        (x 0 : Real) + (t : Real) * (triangularStep i 0 : Real) := by
  change (((t : Real) •
    (triHexPlanePeriod (x + triangularStep i) - triHexPlanePeriod x) +
      triHexPlanePeriod x)).re = _
  rw [map_add]
  simp [Complex.real_smul]
  ring

@[simp] theorem triangularCanonicalSegment_im
    (x : Site 2) (i : Fin 3) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex (x + triangularStep i)) t).im =
        (x 1 : Real) + (t : Real) * (triangularStep i 1 : Real) := by
  change (((t : Real) •
    (triHexPlanePeriod (x + triangularStep i) - triHexPlanePeriod x) +
      triHexPlanePeriod x)).im = _
  rw [map_add]
  simp [Complex.real_smul]
  ring

private theorem affineInt_mem_interval (a b : Int) (t : unitInterval) :
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


theorem triangularCanonicalSegments_commonEndpoint
    (x z : Site 2) (i j : Fin 3) (p : Complex)
    (hp : p ∈ Set.range (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex (x + triangularStep i))))
    (hq : p ∈ Set.range (Path.segment (triangularPlaneVertex z)
      (triangularPlaneVertex (z + triangularStep j)))) :
    x = z ∨ x = z + triangularStep j ∨
      x + triangularStep i = z ∨
      x + triangularStep i = z + triangularStep j := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨u, hu⟩ := hq
  have hre := congrArg Complex.re (ht.trans hu.symm)
  have him := congrArg Complex.im (ht.trans hu.symm)
  simp only [triangularCanonicalSegment_re] at hre
  simp only [triangularCanonicalSegment_im] at him
  let y := x + triangularStep i
  let w := z + triangularStep j
  have h0eq :
      (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) =
        (u : Real) * ((w 0 : Real) - (z 0 : Real)) + (z 0 : Real) := by
    dsimp [y, w]
    simpa only [Pi.add_apply, Int.cast_add, add_sub_cancel_left,
      add_comm] using hre
  have h1eq :
      (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) =
        (u : Real) * ((w 1 : Real) - (z 1 : Real)) + (z 1 : Real) := by
    dsimp [y, w]
    simpa only [Pi.add_apply, Int.cast_add, add_sub_cancel_left,
      add_comm] using him
  have hx0 := affineInt_mem_interval (x 0) (y 0) t
  have hz0 := affineInt_mem_interval (z 0) (w 0) u
  have hx1 := affineInt_mem_interval (x 1) (y 1) t
  have hz1 := affineInt_mem_interval (z 1) (w 1) u
  have hxs := affineInt_mem_interval (x 0 + x 1) (y 0 + y 1) t
  have hzs := affineInt_mem_interval (z 0 + z 1) (w 0 + w 1) u
  have hseq :
      (t : Real) * (((y 0 + y 1 : Int) : Real) -
          ((x 0 + x 1 : Int) : Real)) + ((x 0 + x 1 : Int) : Real) =
        (u : Real) * (((w 0 + w 1 : Int) : Real) -
          ((z 0 + z 1 : Int) : Real)) + ((z 0 + z 1 : Int) : Real) := by
    push_cast
    linarith
  have h00R : ((min (x 0) (y 0) : Int) : Real) <=
      ((max (z 0) (w 0) : Int) : Real) := hx0.1.trans (h0eq.trans_le hz0.2)
  have h01R : ((min (z 0) (w 0) : Int) : Real) <=
      ((max (x 0) (y 0) : Int) : Real) := hz0.1.trans (h0eq.symm.trans_le hx0.2)
  have h10R : ((min (x 1) (y 1) : Int) : Real) <=
      ((max (z 1) (w 1) : Int) : Real) := hx1.1.trans (h1eq.trans_le hz1.2)
  have h11R : ((min (z 1) (w 1) : Int) : Real) <=
      ((max (x 1) (y 1) : Int) : Real) := hz1.1.trans (h1eq.symm.trans_le hx1.2)
  have hs0R : ((min (x 0 + x 1) (y 0 + y 1) : Int) : Real) <=
      ((max (z 0 + z 1) (w 0 + w 1) : Int) : Real) :=
    hxs.1.trans (hseq.trans_le hzs.2)
  have hs1R : ((min (z 0 + z 1) (w 0 + w 1) : Int) : Real) <=
      ((max (x 0 + x 1) (y 0 + y 1) : Int) : Real) :=
    hzs.1.trans (hseq.symm.trans_le hxs.2)
  have h00 : min (x 0) (y 0) <= max (z 0) (w 0) := by exact_mod_cast h00R
  have h01 : min (z 0) (w 0) <= max (x 0) (y 0) := by exact_mod_cast h01R
  have h10 : min (x 1) (y 1) <= max (z 1) (w 1) := by exact_mod_cast h10R
  have h11 : min (z 1) (w 1) <= max (x 1) (y 1) := by exact_mod_cast h11R
  have hs0 : min (x 0 + x 1) (y 0 + y 1) <=
      max (z 0 + z 1) (w 0 + w 1) := by exact_mod_cast hs0R
  have hs1 : min (z 0 + z 1) (w 0 + w 1) <=
      max (x 0 + x 1) (y 0 + y 1) := by exact_mod_cast hs1R
  dsimp [y, w] at h00 h01 h10 h11 hs0 hs1
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  have hzHead : Matrix.vecHead z = z 0 := rfl
  have hzTail : Matrix.vecHead (Matrix.vecTail z) = z 1 := rfl
  fin_cases i <;> fin_cases j
  all_goals
    simp [triangularStep, funext_iff, hxHead, hxTail, hzHead, hzTail]
      at h00 h01 h10 h11 hs0 hs1 ⊢
  all_goals omega

@[simp] theorem triangularSegment_re
    (x y : Site 2) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).re =
      (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) := by
  change (((t : Real) • (triHexPlanePeriod y - triHexPlanePeriod x) +
    triHexPlanePeriod x)).re = _
  simp [Complex.real_smul]

@[simp] theorem triangularSegment_im
    (x y : Site 2) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).im =
      (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) := by
  change (((t : Real) • (triHexPlanePeriod y - triHexPlanePeriod x) +
    triHexPlanePeriod x)).im = _
  simp [Complex.real_smul]

theorem mem_range_triangularSegment_symm (x y : Site 2) {p : Complex}
    (hp : p ∈ Set.range
      (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y))) :
    p ∈ Set.range
      (Path.segment (triangularPlaneVertex y) (triangularPlaneVertex x)) := by
  rw [Path.range_segment, segment_symm]
  simpa only [Path.range_segment] using hp


theorem triangularNeighborSegments_inter_eq
    {v a b : Site 2}
    (hva : triangularGraph.Adj v a) (hvb : triangularGraph.Adj v b)
    (hab : Ne a b) {p : Complex}
    (hpa : p ∈ Set.range
      (Path.segment (triangularPlaneVertex v) (triangularPlaneVertex a)))
    (hpb : p ∈ Set.range
      (Path.segment (triangularPlaneVertex v) (triangularPlaneVertex b))) :
    p = triangularPlaneVertex v := by
  obtain ⟨t, rfl⟩ := hpa
  obtain ⟨u, hu⟩ := hpb
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp only [triangularSegment_re] at hre
  simp only [triangularSegment_im] at him
  obtain ⟨ia, _hia, rfl⟩ := Finset.mem_image.mp
    (triangular_mem_candidates_of_adj hva)
  obtain ⟨ib, _hib, rfl⟩ := Finset.mem_image.mp
    (triangular_mem_candidates_of_adj hvb)
  rcases ia with ⟨i, bi⟩
  rcases ib with ⟨j, bj⟩
  fin_cases i <;> fin_cases j <;> cases bi <;> cases bj
  all_goals
    simp [triangularNeighbor, triangularStep, funext_iff] at hre him hab
  all_goals
    have htR : (t : Real) = 0 := by
      first
      | exact hre
      | exact congrArg Subtype.val hre
      | exact him
      | exact congrArg Subtype.val him
      | have huR : (u : Real) = 0 := congrArg Subtype.val him
        linarith [hre, huR]
      | have huR : (u : Real) = 0 := congrArg Subtype.val hre
        linarith [him, huR]
      | linarith [hre, him, t.2.1, u.2.1]
    have ht : t = 0 := Subtype.ext htR
    rw [ht]
    exact (Path.segment (triangularPlaneVertex v)
      (triangularPlaneVertex _)).source

private theorem triangularEdges_commonEndpoint_of_intersection
    {x y z w : Site 2}
    (hxy : triangularGraph.Adj x y) (hzw : triangularGraph.Adj z w)
    (p : Complex)
    (hp : p ∈ Set.range (triangularStraightEdgeArc hxy))
    (hq : p ∈ Set.range (triangularStraightEdgeArc hzw)) :
    ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) := by
  let exy : triangularGraph.edgeSet := ⟨s(x, y), hxy⟩
  let ezw : triangularGraph.edgeSet := ⟨s(z, w), hzw⟩
  let a := triangularEdgeChartEquiv.symm exy
  let b := triangularEdgeChartEquiv.symm ezw
  have ha : triangularIndexedEdge a = s(x, y) := by
    have h := congrArg Subtype.val
      (triangularEdgeChartEquiv.apply_symm_apply exy)
    exact h
  have hb : triangularIndexedEdge b = s(z, w) := by
    have h := congrArg Subtype.val
      (triangularEdgeChartEquiv.apply_symm_apply ezw)
    exact h
  rw [triangularIndexedEdge, Sym2.eq_iff] at ha hb
  have hp0 : p ∈ Set.range
      (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y)) := hp
  have hq0 : p ∈ Set.range
      (Path.segment (triangularPlaneVertex z) (triangularPlaneVertex w)) := hq
  rcases ha with ha | ha
  · have hp' : p ∈ Set.range (Path.segment
    (triangularPlaneVertex a.1)
        (triangularPlaneVertex (a.1 + triangularStep a.2))) := by
      rw [ha.2, ha.1]
      exact hp0
    rcases hb with hb | hb
    · have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hq0
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inl ha.1, Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inl ha.1, Or.inr (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inr (h.trans hb.2)⟩
    · have hqRev := mem_range_triangularSegment_symm z w hq0
      have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hqRev
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inl ha.1, Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inl ha.1, Or.inl (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inl (h.trans hb.2)⟩
  · have hpRev := mem_range_triangularSegment_symm x y hp0
    have hp' : p ∈ Set.range (Path.segment
        (triangularPlaneVertex a.1)
        (triangularPlaneVertex (a.1 + triangularStep a.2))) := by
      rw [ha.2, ha.1]
      exact hpRev
    rcases hb with hb | hb
    · have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hq0
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inr ha.1, Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inr ha.1, Or.inr (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inr (h.trans hb.2)⟩
    · have hqRev := mem_range_triangularSegment_symm z w hq0
      have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hqRev
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inr ha.1, Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inr ha.1, Or.inl (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inl (h.trans hb.2)⟩


theorem triangularStraightEdgeIntersection :
    TriangularStraightEdgeIntersectionProperty := by
  intro x y z w hxy hzw p hne hp hq
  have hpMem := hp
  have hqMem := hq
  obtain ⟨v, hvxy, hvzw⟩ :=
    triangularEdges_commonEndpoint_of_intersection hxy hzw p hp hq
  rcases hvxy with hvx | hvy
  · subst v
    rcases hvzw with hvz | hvw
    · subst z
      have hyw : Ne y w := by
        intro hyw
        subst w
        exact hne rfl
      have hv := triangularNeighborSegments_inter_eq hxy hzw hyw hpMem hqMem
      exact ⟨x, Or.inl rfl, Or.inl rfl, hv.symm⟩
    · subst w
      have hyz : Ne y z := by
        intro hyz
        subst z
        exact hne Sym2.eq_swap
      have hq' := mem_range_triangularSegment_symm z x hqMem
      have hv := triangularNeighborSegments_inter_eq hxy hzw.symm hyz hpMem hq'
      exact ⟨x, Or.inl rfl, Or.inr rfl, hv.symm⟩
  · subst v
    rcases hvzw with hvz | hvw
    · subst z
      have hxw : Ne x w := by
        intro hxw
        subst w
        exact hne Sym2.eq_swap
      have hp' := mem_range_triangularSegment_symm x y hpMem
      have hv := triangularNeighborSegments_inter_eq hxy.symm hzw hxw hp' hqMem
      exact ⟨y, Or.inr rfl, Or.inl rfl, hv.symm⟩
    · subst w
      have hxz : Ne x z := by
        intro hxz
        subst z
        exact hne rfl
      have hp' := mem_range_triangularSegment_symm x y hpMem
      have hq' := mem_range_triangularSegment_symm z y hqMem
      have hv := triangularNeighborSegments_inter_eq hxy.symm hzw.symm hxz hp' hq'
      exact ⟨y, Or.inr rfl, Or.inr rfl, hv.symm⟩





def hexagonalScaledCoordinate (u : HexVertex) (k : Fin 2) : Int :=
  3 * u.1 k + if u.2 then -1 else 1

private theorem complexSegment_re (a b : Complex) (t : unitInterval) :
    (Path.segment a b t).re =
      (t : Real) * (b.re - a.re) + a.re := by
  change (((t : Real) • (b - a) + a)).re = _
  simp [Complex.real_smul]

private theorem complexSegment_im (a b : Complex) (t : unitInterval) :
    (Path.segment a b t).im =
      (t : Real) * (b.im - a.im) + a.im := by
  change (((t : Real) • (b - a) + a)).im = _
  simp [Complex.real_smul]

@[simp] theorem hexagonalPlaneVertex_re_scaled (u : HexVertex) :
    (hexagonalPlaneVertex u : Complex).re =
      (hexagonalScaledCoordinate u 0 : Real) / 3 := by
  rcases u with ⟨x, b⟩
  cases b <;>
    simp [hexagonalPlaneVertex, hexagonalPlaneVertexValue,
      hexagonalScaledCoordinate, hexagonalFaceCenterOffset, triHexPlanePeriod] <;>
    ring

@[simp] theorem hexagonalPlaneVertex_im_scaled (u : HexVertex) :
    (hexagonalPlaneVertex u : Complex).im =
      (hexagonalScaledCoordinate u 1 : Real) / 3 := by
  rcases u with ⟨x, b⟩
  cases b <;>
    simp [hexagonalPlaneVertex, hexagonalPlaneVertexValue,
      hexagonalScaledCoordinate, hexagonalFaceCenterOffset, triHexPlanePeriod] <;>
    ring

@[simp] theorem hexagonalSegment_re_scaled
    (u v : HexVertex) (t : unitInterval) :
    3 * (Path.segment (hexagonalPlaneVertex u)
      (hexagonalPlaneVertex v) t).re =
        (t : Real) * ((hexagonalScaledCoordinate v 0 : Real) -
          (hexagonalScaledCoordinate u 0 : Real)) +
        (hexagonalScaledCoordinate u 0 : Real) := by
  rw [complexSegment_re]
  rw [hexagonalPlaneVertex_re_scaled, hexagonalPlaneVertex_re_scaled]
  ring

@[simp] theorem hexagonalSegment_im_scaled
    (u v : HexVertex) (t : unitInterval) :
    3 * (Path.segment (hexagonalPlaneVertex u)
      (hexagonalPlaneVertex v) t).im =
        (t : Real) * ((hexagonalScaledCoordinate v 1 : Real) -
          (hexagonalScaledCoordinate u 1 : Real)) +
        (hexagonalScaledCoordinate u 1 : Real) := by
  rw [complexSegment_im]
  rw [hexagonalPlaneVertex_im_scaled, hexagonalPlaneVertex_im_scaled]
  ring

set_option maxHeartbeats 800000 in


theorem hexagonalCanonicalSegments_commonEndpoint
    (x z : Site 2) (i j : Fin 3) (p : Complex)
    (hp : p ∈ Set.range (Path.segment
      (hexagonalPlaneVertex (x, false))
      (hexagonalPlaneVertex (x + hexagonalStep i, true))))
    (hq : p ∈ Set.range (Path.segment
      (hexagonalPlaneVertex (z, false))
      (hexagonalPlaneVertex (z + hexagonalStep j, true)))) :
    (x, false) = (z, false) ∨
      (x + hexagonalStep i, true) = (z + hexagonalStep j, true) := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨u, hu⟩ := hq
  have hre := congrArg Complex.re (ht.trans hu.symm)
  have him := congrArg Complex.im (ht.trans hu.symm)
  let a : HexVertex := (x, false)
  let b : HexVertex := (x + hexagonalStep i, true)
  let c : HexVertex := (z, false)
  let d : HexVertex := (z + hexagonalStep j, true)
  have h0eq :
      (t : Real) * ((hexagonalScaledCoordinate b 0 : Real) -
          (hexagonalScaledCoordinate a 0 : Real)) +
          (hexagonalScaledCoordinate a 0 : Real) =
        (u : Real) * ((hexagonalScaledCoordinate d 0 : Real) -
          (hexagonalScaledCoordinate c 0 : Real)) +
          (hexagonalScaledCoordinate c 0 : Real) := by
    calc
      _ = 3 * (Path.segment (hexagonalPlaneVertex a)
          (hexagonalPlaneVertex b) t).re :=
        (hexagonalSegment_re_scaled a b t).symm
      _ = 3 * (Path.segment (hexagonalPlaneVertex c)
          (hexagonalPlaneVertex d) u).re := by
        exact congrArg (fun r : Real => 3 * r) hre
      _ = _ := hexagonalSegment_re_scaled c d u
  have h1eq :
      (t : Real) * ((hexagonalScaledCoordinate b 1 : Real) -
          (hexagonalScaledCoordinate a 1 : Real)) +
          (hexagonalScaledCoordinate a 1 : Real) =
        (u : Real) * ((hexagonalScaledCoordinate d 1 : Real) -
          (hexagonalScaledCoordinate c 1 : Real)) +
          (hexagonalScaledCoordinate c 1 : Real) := by
    calc
      _ = 3 * (Path.segment (hexagonalPlaneVertex a)
          (hexagonalPlaneVertex b) t).im :=
        (hexagonalSegment_im_scaled a b t).symm
      _ = 3 * (Path.segment (hexagonalPlaneVertex c)
          (hexagonalPlaneVertex d) u).im := by
        exact congrArg (fun r : Real => 3 * r) him
      _ = _ := hexagonalSegment_im_scaled c d u
  have ha0 := affineInt_mem_interval
    (hexagonalScaledCoordinate a 0) (hexagonalScaledCoordinate b 0) t
  have hc0 := affineInt_mem_interval
    (hexagonalScaledCoordinate c 0) (hexagonalScaledCoordinate d 0) u
  have ha1 := affineInt_mem_interval
    (hexagonalScaledCoordinate a 1) (hexagonalScaledCoordinate b 1) t
  have hc1 := affineInt_mem_interval
    (hexagonalScaledCoordinate c 1) (hexagonalScaledCoordinate d 1) u
  have has := affineInt_mem_interval
    (hexagonalScaledCoordinate a 0 + hexagonalScaledCoordinate a 1)
    (hexagonalScaledCoordinate b 0 + hexagonalScaledCoordinate b 1) t
  have hcs := affineInt_mem_interval
    (hexagonalScaledCoordinate c 0 + hexagonalScaledCoordinate c 1)
    (hexagonalScaledCoordinate d 0 + hexagonalScaledCoordinate d 1) u
  have hseq :
      (t : Real) *
          (((hexagonalScaledCoordinate b 0 + hexagonalScaledCoordinate b 1 : Int) : Real) -
            ((hexagonalScaledCoordinate a 0 + hexagonalScaledCoordinate a 1 : Int) : Real)) +
          ((hexagonalScaledCoordinate a 0 + hexagonalScaledCoordinate a 1 : Int) : Real) =
        (u : Real) *
          (((hexagonalScaledCoordinate d 0 + hexagonalScaledCoordinate d 1 : Int) : Real) -
            ((hexagonalScaledCoordinate c 0 + hexagonalScaledCoordinate c 1 : Int) : Real)) +
          ((hexagonalScaledCoordinate c 0 + hexagonalScaledCoordinate c 1 : Int) : Real) := by
    push_cast
    linarith
  have h00R : ((min (hexagonalScaledCoordinate a 0)
      (hexagonalScaledCoordinate b 0) : Int) : Real) <=
      ((max (hexagonalScaledCoordinate c 0)
        (hexagonalScaledCoordinate d 0) : Int) : Real) :=
    ha0.1.trans (h0eq.trans_le hc0.2)
  have h01R : ((min (hexagonalScaledCoordinate c 0)
      (hexagonalScaledCoordinate d 0) : Int) : Real) <=
      ((max (hexagonalScaledCoordinate a 0)
        (hexagonalScaledCoordinate b 0) : Int) : Real) :=
    hc0.1.trans (h0eq.symm.trans_le ha0.2)
  have h10R : ((min (hexagonalScaledCoordinate a 1)
      (hexagonalScaledCoordinate b 1) : Int) : Real) <=
      ((max (hexagonalScaledCoordinate c 1)
        (hexagonalScaledCoordinate d 1) : Int) : Real) :=
    ha1.1.trans (h1eq.trans_le hc1.2)
  have h11R : ((min (hexagonalScaledCoordinate c 1)
      (hexagonalScaledCoordinate d 1) : Int) : Real) <=
      ((max (hexagonalScaledCoordinate a 1)
        (hexagonalScaledCoordinate b 1) : Int) : Real) :=
    hc1.1.trans (h1eq.symm.trans_le ha1.2)
  have hs0R : ((min
      (hexagonalScaledCoordinate a 0 + hexagonalScaledCoordinate a 1)
      (hexagonalScaledCoordinate b 0 + hexagonalScaledCoordinate b 1) : Int) : Real) <=
      ((max
        (hexagonalScaledCoordinate c 0 + hexagonalScaledCoordinate c 1)
        (hexagonalScaledCoordinate d 0 + hexagonalScaledCoordinate d 1) : Int) : Real) :=
    has.1.trans (hseq.trans_le hcs.2)
  have hs1R : ((min
      (hexagonalScaledCoordinate c 0 + hexagonalScaledCoordinate c 1)
      (hexagonalScaledCoordinate d 0 + hexagonalScaledCoordinate d 1) : Int) : Real) <=
      ((max
        (hexagonalScaledCoordinate a 0 + hexagonalScaledCoordinate a 1)
        (hexagonalScaledCoordinate b 0 + hexagonalScaledCoordinate b 1) : Int) : Real) :=
    hcs.1.trans (hseq.symm.trans_le has.2)
  have h00 := (by exact_mod_cast h00R :
    min (hexagonalScaledCoordinate a 0) (hexagonalScaledCoordinate b 0) <=
      max (hexagonalScaledCoordinate c 0) (hexagonalScaledCoordinate d 0))
  have h01 := (by exact_mod_cast h01R :
    min (hexagonalScaledCoordinate c 0) (hexagonalScaledCoordinate d 0) <=
      max (hexagonalScaledCoordinate a 0) (hexagonalScaledCoordinate b 0))
  have h10 := (by exact_mod_cast h10R :
    min (hexagonalScaledCoordinate a 1) (hexagonalScaledCoordinate b 1) <=
      max (hexagonalScaledCoordinate c 1) (hexagonalScaledCoordinate d 1))
  have h11 := (by exact_mod_cast h11R :
    min (hexagonalScaledCoordinate c 1) (hexagonalScaledCoordinate d 1) <=
      max (hexagonalScaledCoordinate a 1) (hexagonalScaledCoordinate b 1))
  have hs0 := (by exact_mod_cast hs0R :
    min (hexagonalScaledCoordinate a 0 + hexagonalScaledCoordinate a 1)
        (hexagonalScaledCoordinate b 0 + hexagonalScaledCoordinate b 1) <=
      max (hexagonalScaledCoordinate c 0 + hexagonalScaledCoordinate c 1)
        (hexagonalScaledCoordinate d 0 + hexagonalScaledCoordinate d 1))
  have hs1 := (by exact_mod_cast hs1R :
    min (hexagonalScaledCoordinate c 0 + hexagonalScaledCoordinate c 1)
        (hexagonalScaledCoordinate d 0 + hexagonalScaledCoordinate d 1) <=
      max (hexagonalScaledCoordinate a 0 + hexagonalScaledCoordinate a 1)
        (hexagonalScaledCoordinate b 0 + hexagonalScaledCoordinate b 1))
  dsimp [a, b, c, d] at h00 h01 h10 h11 hs0 hs1
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  have hzHead : Matrix.vecHead z = z 0 := rfl
  have hzTail : Matrix.vecHead (Matrix.vecTail z) = z 1 := rfl
  fin_cases i <;> fin_cases j
  all_goals
    simp [hexagonalScaledCoordinate, hexagonalStep, funext_iff,
      hxHead, hxTail, hzHead, hzTail] at h00 h01 h10 h11 hs0 hs1 ⊢
  all_goals omega

theorem mem_range_hexagonalSegment_symm (u v : HexVertex) {p : Complex}
    (hp : p ∈ Set.range
      (Path.segment (hexagonalPlaneVertex u) (hexagonalPlaneVertex v))) :
    p ∈ Set.range
      (Path.segment (hexagonalPlaneVertex v) (hexagonalPlaneVertex u)) := by
  rw [Path.range_segment, segment_symm]
  simpa only [Path.range_segment] using hp


theorem hexagonalNeighborSegments_inter_eq
    {v a b : HexVertex}
    (hva : hexagonalGraph.Adj v a) (hvb : hexagonalGraph.Adj v b)
    (hab : Ne a b) {p : Complex}
    (hpa : p ∈ Set.range
      (Path.segment (hexagonalPlaneVertex v) (hexagonalPlaneVertex a)))
    (hpb : p ∈ Set.range
      (Path.segment (hexagonalPlaneVertex v) (hexagonalPlaneVertex b))) :
    p = hexagonalPlaneVertex v := by
  obtain ⟨t, rfl⟩ := hpa
  obtain ⟨u, hu⟩ := hpb
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  rw [complexSegment_re, complexSegment_re] at hre
  rw [complexSegment_im, complexSegment_im] at him
  simp only [hexagonalPlaneVertex_re_scaled] at hre
  simp only [hexagonalPlaneVertex_im_scaled] at him
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp
    (hexagonal_mem_candidates_of_adj hva)
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp
    (hexagonal_mem_candidates_of_adj hvb)
  rcases v with ⟨x, bv⟩
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  fin_cases i <;> fin_cases j <;> cases bv
  all_goals
    simp [hexagonalNeighbor, hexagonalScaledCoordinate, hexagonalStep,
      funext_iff, hxHead, hxTail] at hre him hab
  all_goals
    have htR : (t : Real) = 0 := by
      first
      | exact hre
      | exact congrArg Subtype.val hre
      | exact him
      | exact congrArg Subtype.val him
      | linarith [hre, him, t.2.1, u.2.1]
    have ht : t = 0 := Subtype.ext htR
    rw [ht]
    exact (Path.segment (hexagonalPlaneVertex (x, _))
      (hexagonalPlaneVertex _)).source

private theorem hexagonalEdges_commonEndpoint_of_intersection
    {x y z w : HexVertex}
    (hxy : hexagonalGraph.Adj x y) (hzw : hexagonalGraph.Adj z w)
    (p : Complex)
    (hp : p ∈ Set.range (hexagonalStraightEdgeArc hxy))
    (hq : p ∈ Set.range (hexagonalStraightEdgeArc hzw)) :
    ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) := by
  let exy : hexagonalGraph.edgeSet := ⟨s(x, y), hxy⟩
  let ezw : hexagonalGraph.edgeSet := ⟨s(z, w), hzw⟩
  let a := hexagonalEdgeChartEquiv.symm exy
  let b := hexagonalEdgeChartEquiv.symm ezw
  have ha : hexagonalIndexedEdge a = s(x, y) := by
    have h := congrArg Subtype.val
      (hexagonalEdgeChartEquiv.apply_symm_apply exy)
    exact h
  have hb : hexagonalIndexedEdge b = s(z, w) := by
    have h := congrArg Subtype.val
      (hexagonalEdgeChartEquiv.apply_symm_apply ezw)
    exact h
  rw [hexagonalIndexedEdge, Sym2.eq_iff] at ha hb
  have hp0 : p ∈ Set.range
      (Path.segment (hexagonalPlaneVertex x) (hexagonalPlaneVertex y)) := hp
  have hq0 : p ∈ Set.range
      (Path.segment (hexagonalPlaneVertex z) (hexagonalPlaneVertex w)) := hq
  rcases ha with ha | ha
  · have hp' : p ∈ Set.range (Path.segment
        (hexagonalPlaneVertex (a.1, false))
        (hexagonalPlaneVertex (a.1 + hexagonalStep a.2, true))) := by
      rw [ha.2, ha.1]
      exact hp0
    rcases hb with hb | hb
    · have hq' : p ∈ Set.range (Path.segment
          (hexagonalPlaneVertex (b.1, false))
          (hexagonalPlaneVertex (b.1 + hexagonalStep b.2, true))) := by
        rw [hb.2, hb.1]
        exact hq0
      rcases hexagonalCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h
      · exact ⟨(a.1, false), Or.inl ha.1, Or.inl (h.trans hb.1)⟩
      · exact ⟨(a.1 + hexagonalStep a.2, true), Or.inr ha.2,
          Or.inr (h.trans hb.2)⟩
    · have hqRev := mem_range_hexagonalSegment_symm z w hq0
      have hq' : p ∈ Set.range (Path.segment
          (hexagonalPlaneVertex (b.1, false))
          (hexagonalPlaneVertex (b.1 + hexagonalStep b.2, true))) := by
        rw [hb.2, hb.1]
        exact hqRev
      rcases hexagonalCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h
      · exact ⟨(a.1, false), Or.inl ha.1, Or.inr (h.trans hb.1)⟩
      · exact ⟨(a.1 + hexagonalStep a.2, true), Or.inr ha.2,
          Or.inl (h.trans hb.2)⟩
  · have hpRev := mem_range_hexagonalSegment_symm x y hp0
    have hp' : p ∈ Set.range (Path.segment
        (hexagonalPlaneVertex (a.1, false))
        (hexagonalPlaneVertex (a.1 + hexagonalStep a.2, true))) := by
      rw [ha.2, ha.1]
      exact hpRev
    rcases hb with hb | hb
    · have hq' : p ∈ Set.range (Path.segment
          (hexagonalPlaneVertex (b.1, false))
          (hexagonalPlaneVertex (b.1 + hexagonalStep b.2, true))) := by
        rw [hb.2, hb.1]
        exact hq0
      rcases hexagonalCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h
      · exact ⟨(a.1, false), Or.inr ha.1, Or.inl (h.trans hb.1)⟩
      · exact ⟨(a.1 + hexagonalStep a.2, true), Or.inl ha.2,
          Or.inr (h.trans hb.2)⟩
    · have hqRev := mem_range_hexagonalSegment_symm z w hq0
      have hq' : p ∈ Set.range (Path.segment
          (hexagonalPlaneVertex (b.1, false))
          (hexagonalPlaneVertex (b.1 + hexagonalStep b.2, true))) := by
        rw [hb.2, hb.1]
        exact hqRev
      rcases hexagonalCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h
      · exact ⟨(a.1, false), Or.inr ha.1, Or.inr (h.trans hb.1)⟩
      · exact ⟨(a.1 + hexagonalStep a.2, true), Or.inl ha.2,
          Or.inl (h.trans hb.2)⟩


theorem hexagonalStraightEdgeIntersection :
    HexagonalStraightEdgeIntersectionProperty := by
  intro x y z w hxy hzw p hne hp hq
  have hpMem := hp
  have hqMem := hq
  obtain ⟨v, hvxy, hvzw⟩ :=
    hexagonalEdges_commonEndpoint_of_intersection hxy hzw p hp hq
  rcases hvxy with hvx | hvy
  · subst v
    rcases hvzw with hvz | hvw
    · subst z
      have hyw : Ne y w := by
        intro hyw
        subst w
        exact hne rfl
      have hv := hexagonalNeighborSegments_inter_eq hxy hzw hyw hpMem hqMem
      exact ⟨x, Or.inl rfl, Or.inl rfl, hv.symm⟩
    · subst w
      have hyz : Ne y z := by
        intro hyz
        subst z
        exact hne Sym2.eq_swap
      have hq' := mem_range_hexagonalSegment_symm z x hqMem
      have hv := hexagonalNeighborSegments_inter_eq hxy hzw.symm hyz hpMem hq'
      exact ⟨x, Or.inl rfl, Or.inr rfl, hv.symm⟩
  · subst v
    rcases hvzw with hvz | hvw
    · subst z
      have hxw : Ne x w := by
        intro hxw
        subst w
        exact hne Sym2.eq_swap
      have hp' := mem_range_hexagonalSegment_symm x y hpMem
      have hv := hexagonalNeighborSegments_inter_eq hxy.symm hzw hxw hp' hqMem
      exact ⟨y, Or.inr rfl, Or.inl rfl, hv.symm⟩
    · subst w
      have hxz : Ne x z := by
        intro hxz
        subst z
        exact hne rfl
      have hp' := mem_range_hexagonalSegment_symm x y hpMem
      have hq' := mem_range_hexagonalSegment_symm z y hqMem
      have hv := hexagonalNeighborSegments_inter_eq hxy.symm hzw.symm hxz hp' hq'
      exact ⟨y, Or.inr rfl, Or.inr rfl, hv.symm⟩


noncomputable def triangularPeriodicPlaneEmbedding :
    PeriodicPlaneEmbedding triangular :=
  triangularPeriodicPlaneEmbedding_of_intersection
    triangularStraightEdgeIntersection


noncomputable def hexagonalPeriodicPlaneEmbedding :
    PeriodicPlaneEmbedding hexagonal :=
  hexagonalPeriodicPlaneEmbedding_of_intersection
    hexagonalStraightEdgeIntersection

end StatMech.FK.PeriodicPlanar
