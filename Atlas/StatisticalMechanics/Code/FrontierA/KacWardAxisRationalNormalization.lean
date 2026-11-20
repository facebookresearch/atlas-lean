/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardIntegralAxisSubdivision
import Code.FrontierA.KacWardRationalNormalization





namespace StatMech.FrontierA

open Set
open scoped BigOperators



noncomputable def kwRatApprox (eps : ℝ) (heps : 0 < eps) (x : ℝ) : ℚ :=
  Classical.choose (exists_rat_btwn (by linarith : x - eps < x + eps))

theorem kwRatApprox_spec (eps : ℝ) (heps : 0 < eps) (x : ℝ) :
    x - eps < (kwRatApprox eps heps x : ℝ) ∧
      (kwRatApprox eps heps x : ℝ) < x + eps :=
  Classical.choose_spec (exists_rat_btwn (by linarith : x - eps < x + eps))

theorem abs_kwRatApprox_sub_lt (eps : ℝ) (heps : 0 < eps) (x : ℝ) :
    |(kwRatApprox eps heps x : ℝ) - x| < eps := by
  rw [abs_lt]
  constructor <;> linarith [kwRatApprox_spec eps heps x]


noncomputable def kwAxisRatData
    {n : ℕ} (vertex : Fin n → ℂ) (eps : ℝ) (heps : 0 < eps) :
    Fin n → ℚ × ℚ :=
  fun i ↦ (kwRatApprox eps heps (vertex i).re,
    kwRatApprox eps heps (vertex i).im)

theorem kwAxisRatVertex_re_close
    {n : ℕ} (vertex : Fin n → ℂ) (eps : ℝ) (heps : 0 < eps)
    (i : Fin n) :
    |(kwRatVertex (kwAxisRatData vertex eps heps) i).re - (vertex i).re| <
      eps := by
  simpa [kwRatVertex, kwRatComplex, kwAxisRatData] using
    abs_kwRatApprox_sub_lt eps heps (vertex i).re

theorem kwAxisRatVertex_im_close
    {n : ℕ} (vertex : Fin n → ℂ) (eps : ℝ) (heps : 0 < eps)
    (i : Fin n) :
    |(kwRatVertex (kwAxisRatData vertex eps heps) i).im - (vertex i).im| <
      eps := by
  simpa [kwRatVertex, kwRatComplex, kwAxisRatData] using
    abs_kwRatApprox_sub_lt eps heps (vertex i).im

theorem dist_kwAxisRatVertex_lt_two_mul
    {n : ℕ} (vertex : Fin n → ℂ) (eps : ℝ) (heps : 0 < eps)
    (i : Fin n) :
    dist (kwRatVertex (kwAxisRatData vertex eps heps) i) (vertex i) <
      2 * eps := by
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  have hre := kwAxisRatVertex_re_close vertex eps heps i
  have him := kwAxisRatVertex_im_close vertex eps heps i
  simpa only [Complex.sub_re, Complex.sub_im, two_mul] using add_lt_add hre him

theorem kwAxisRatVertex_preserves_re_eq
    {n : ℕ} (vertex : Fin n → ℂ) (eps : ℝ) (heps : 0 < eps)
    {i j : Fin n} (h : (vertex i).re = (vertex j).re) :
    (kwRatVertex (kwAxisRatData vertex eps heps) i).re =
      (kwRatVertex (kwAxisRatData vertex eps heps) j).re := by
  simp [kwRatVertex, kwRatComplex, kwAxisRatData, h]

theorem kwAxisRatVertex_preserves_im_eq
    {n : ℕ} (vertex : Fin n → ℂ) (eps : ℝ) (heps : 0 < eps)
    {i j : Fin n} (h : (vertex i).im = (vertex j).im) :
    (kwRatVertex (kwAxisRatData vertex eps heps) i).im =
      (kwRatVertex (kwAxisRatData vertex eps heps) j).im := by
  simp [kwRatVertex, kwRatComplex, kwAxisRatData, h]

private theorem axis_vector_pos_scale_of_close
    (z w : ℂ) (hz : z ≠ 0)
    (haxis : z.re = 0 ∨ z.im = 0)
    (hzero : (z.re = 0 → w.re = 0) ∧ (z.im = 0 → w.im = 0))
    (hre : z.re ≠ 0 → |w.re - z.re| < |z.re|)
    (him : z.im ≠ 0 → |w.im - z.im| < |z.im|) :
    ∃ r : ℝ, 0 < r ∧ w = r * z := by
  rcases haxis with hzre | hzim
  · have hzimne : z.im ≠ 0 := by
      intro hi
      apply hz
      apply Complex.ext <;> simp [hzre, hi]
    have hwre : w.re = 0 := hzero.1 hzre
    have him' := him hzimne
    by_cases hs : 0 < z.im
    · have hwt : 0 < w.im := by
        rw [abs_of_pos hs] at him'
        have hb := abs_lt.mp him'
        linarith
      refine ⟨w.im / z.im, div_pos hwt hs, ?_⟩
      apply Complex.ext
      · simp [hwre, hzre]
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero]
        field_simp
    · have hsneg : z.im < 0 := lt_of_le_of_ne (not_lt.mp hs) hzimne
      have hwt : w.im < 0 := by
        rw [abs_of_neg hsneg] at him'
        have hb := abs_lt.mp him'
        linarith
      refine ⟨w.im / z.im, div_pos_of_neg_of_neg hwt hsneg, ?_⟩
      apply Complex.ext
      · simp [hwre, hzre]
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero]
        field_simp
  · have hzrene : z.re ≠ 0 := by
      intro hr
      apply hz
      apply Complex.ext <;> simp [hr, hzim]
    have hwim : w.im = 0 := hzero.2 hzim
    have hre' := hre hzrene
    by_cases hs : 0 < z.re
    · have hwt : 0 < w.re := by
        rw [abs_of_pos hs] at hre'
        have hb := abs_lt.mp hre'
        linarith
      refine ⟨w.re / z.re, div_pos hwt hs, ?_⟩
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        field_simp
      · simp [hwim, hzim]
    · have hsneg : z.re < 0 := lt_of_le_of_ne (not_lt.mp hs) hzrene
      have hwt : w.re < 0 := by
        rw [abs_of_neg hsneg] at hre'
        have hb := abs_lt.mp hre'
        linarith
      refine ⟨w.re / z.re, div_pos_of_neg_of_neg hwt hsneg, ?_⟩
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        field_simp
      · simp [hwim, hzim]

private theorem kwComplexCross_real_scales
    (r s : ℝ) (z w : ℂ) :
    kwComplexCross (r * z) (s * w) = r * s * kwComplexCross z w := by
  unfold kwComplexCross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

theorem KWRawTurnAdmissible.of_pos_edge_scales
    {n : ℕ} [NeZero n] {source target : Fin n → ℂ}
    (hsource : ∀ i, KWRawTurnAdmissible source i)
    (scale : Fin n → ℝ) (hscale : ∀ i, 0 < scale i)
    (hedge : ∀ i, kwRawEdge target i = scale i * kwRawEdge source i) :
    ∀ i, KWRawTurnAdmissible target i := by
  intro i
  rcases hsource i with hcross | ⟨r, hr, hforward⟩
  · left
    rw [hedge i, hedge (i + 1), kwComplexCross_real_scales]
    exact mul_ne_zero (mul_ne_zero (hscale i).ne' (hscale (i + 1)).ne') hcross
  · right
    refine ⟨scale (i + 1) * r / scale i,
      div_pos (mul_pos (hscale (i + 1)) hr) (hscale i), ?_⟩
    rw [hedge i, hedge (i + 1), hforward]
    push_cast
    field_simp [(hscale i).ne']



theorem KWFiniteSimplePolygon.exists_rational_axis_phaseModel
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (haxis : ∀ i, (polygon.edgeVector i).re = 0 ∨
      (polygon.edgeVector i).im = 0)
    (hturn : ∀ i, KWRawTurnAdmissible polygon.vertex i) :
    ∃ (q : Fin n → ℚ × ℚ) (rational : KWFiniteSimplePolygon n),
      rational.vertex = kwRatVertex q ∧
      KWRawNonbacktrackingSimpleData rational.vertex ∧
      (∀ i, KWRawTurnAdmissible rational.vertex i) ∧
      (∀ i, (rational.edgeVector i).re = 0 ∨
        (rational.edgeVector i).im = 0) ∧
      kwVectorPhaseCycle polygon.edgeList =
        kwVectorPhaseCycle rational.edgeList := by
  obtain ⟨vertexRadius, hvertexRadius, hvertexSep⟩ :=
    polygon.exists_uniform_vertex_separation
  obtain ⟨edgeRadius, hedgeRadius, hedgeSep⟩ :=
    polygon.exists_uniform_nonincident_edge_dist_separation
  let eps : ℝ := min ((vertexRadius : ℝ) / 8) ((edgeRadius : ℝ) / 8)
  have heps : 0 < eps := by
    dsimp only [eps]
    exact lt_min (by positivity) (by positivity)
  let q := kwAxisRatData polygon.vertex eps heps
  let target := kwRatVertex q
  have hpoint (i : Fin n) : dist (target i) (polygon.vertex i) < 2 * eps := by
    exact dist_kwAxisRatVertex_lt_two_mul polygon.vertex eps heps i
  have hedgeLower (i : Fin n) :
      (vertexRadius : ℝ) < ‖polygon.edgeVector i‖ := by
    have h := hvertexSep (i + 1) i (polygon.add_one_ne_self i)
    simpa only [KWFiniteSimplePolygon.edgeVector, dist_eq_norm] using h
  have hreError (i : Fin n) :
      |(kwRawEdge target i).re - (polygon.edgeVector i).re| < 2 * eps := by
    calc
      |(kwRawEdge target i).re - (polygon.edgeVector i).re| =
          |((target (i + 1)).re - (polygon.vertex (i + 1)).re) -
            ((target i).re - (polygon.vertex i).re)| := by
              unfold kwRawEdge KWFiniteSimplePolygon.edgeVector
              simp only [Complex.sub_re]
              congr 1
              ring
      _ ≤ |(target (i + 1)).re - (polygon.vertex (i + 1)).re| +
          |(target i).re - (polygon.vertex i).re| := abs_sub _ _
      _ < eps + eps := add_lt_add
        (kwAxisRatVertex_re_close polygon.vertex eps heps (i + 1))
        (kwAxisRatVertex_re_close polygon.vertex eps heps i)
      _ = 2 * eps := by ring
  have himError (i : Fin n) :
      |(kwRawEdge target i).im - (polygon.edgeVector i).im| < 2 * eps := by
    calc
      |(kwRawEdge target i).im - (polygon.edgeVector i).im| =
          |((target (i + 1)).im - (polygon.vertex (i + 1)).im) -
            ((target i).im - (polygon.vertex i).im)| := by
              unfold kwRawEdge KWFiniteSimplePolygon.edgeVector
              simp only [Complex.sub_im]
              congr 1
              ring
      _ ≤ |(target (i + 1)).im - (polygon.vertex (i + 1)).im| +
          |(target i).im - (polygon.vertex i).im| := abs_sub _ _
      _ < eps + eps := add_lt_add
        (kwAxisRatVertex_im_close polygon.vertex eps heps (i + 1))
        (kwAxisRatVertex_im_close polygon.vertex eps heps i)
      _ = 2 * eps := by ring
  have hscale : ∀ i : Fin n, ∃ r : ℝ, 0 < r ∧
      kwRawEdge target i = r * polygon.edgeVector i := by
    intro i
    apply axis_vector_pos_scale_of_close
    · exact polygon.edgeVector_ne_zero i
    · exact haxis i
    · constructor
      · intro hz
        have hs : (polygon.vertex (i + 1)).re = (polygon.vertex i).re := by
          simpa only [KWFiniteSimplePolygon.edgeVector, Complex.sub_re,
            sub_eq_zero] using hz
        unfold kwRawEdge
        rw [Complex.sub_re, sub_eq_zero]
        exact kwAxisRatVertex_preserves_re_eq polygon.vertex eps heps hs
      · intro hz
        have hs : (polygon.vertex (i + 1)).im = (polygon.vertex i).im := by
          simpa only [KWFiniteSimplePolygon.edgeVector, Complex.sub_im,
            sub_eq_zero] using hz
        unfold kwRawEdge
        rw [Complex.sub_im, sub_eq_zero]
        exact kwAxisRatVertex_preserves_im_eq polygon.vertex eps heps hs
    · intro hre
      have hzero : (polygon.edgeVector i).im = 0 :=
        (haxis i).resolve_left hre
      calc
        |(kwRawEdge target i).re - (polygon.edgeVector i).re| < 2 * eps :=
          hreError i
        _ < (vertexRadius : ℝ) := by
          have hepsVertex : eps ≤ (vertexRadius : ℝ) / 8 :=
            min_le_left _ _
          have hvpos : 0 < (vertexRadius : ℝ) := by exact_mod_cast hvertexRadius
          linarith
        _ < |(polygon.edgeVector i).re| := by
          rw [Complex.abs_re_eq_norm.mpr hzero]
          exact hedgeLower i
    · intro him
      have hzero : (polygon.edgeVector i).re = 0 :=
        (haxis i).resolve_right him
      calc
        |(kwRawEdge target i).im - (polygon.edgeVector i).im| < 2 * eps :=
          himError i
        _ < (vertexRadius : ℝ) := by
          have hepsVertex : eps ≤ (vertexRadius : ℝ) / 8 :=
            min_le_left _ _
          have hvpos : 0 < (vertexRadius : ℝ) := by exact_mod_cast hvertexRadius
          linarith
        _ < |(polygon.edgeVector i).im| := by
          rw [Complex.abs_im_eq_norm.mpr hzero]
          exact hedgeLower i
  choose scale hscalePos hedgeScale using hscale
  have htargetEdge (i : Fin n) : kwRawEdge target i ≠ 0 := by
    rw [hedgeScale i]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hscalePos i).ne')
      (polygon.edgeVector_ne_zero i)
  have htargetTurn : ∀ i, KWRawTurnAdmissible target i :=
    KWRawTurnAdmissible.of_pos_edge_scales hturn scale hscalePos (by
      intro i
      simpa only [KWFiniteSimplePolygon.edgeVector] using hedgeScale i)
  have htargetNonincident : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge target i) (kwRawClosedEdge target j) := by
    intro i j hij
    apply segment_disjoint_of_perturbation
      (le_of_lt (hpoint i)) (le_of_lt (hpoint (i + 1)))
      (le_of_lt (hpoint j)) (le_of_lt (hpoint (j + 1)))
      (hedgeSep i j hij)
    have hepsEdge : eps ≤ (edgeRadius : ℝ) / 8 := min_le_right _ _
    have hepos : 0 < (edgeRadius : ℝ) := by exact_mod_cast hedgeRadius
    linarith
  let raw : KWRawNonbacktrackingSimpleData target :=
    KWRawNonbacktrackingSimpleData.of_turnAdmissible target polygon.three_le
      htargetEdge htargetTurn htargetNonincident
  let rational := raw.toFiniteSimplePolygon
  have hphase : kwVectorPhaseCycle polygon.edgeList =
      kwVectorPhaseCycle rational.edgeList := by
    rw [KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn,
      KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn]
    unfold kwLoopPhaseProduct
    apply Finset.prod_congr rfl
    intro i hi
    change kwVectorTurnPhase (polygon.edgeVector i)
        (polygon.edgeVector (i + 1)) =
      kwVectorTurnPhase (kwRawEdge target i) (kwRawEdge target (i + 1))
    rw [hedgeScale i, hedgeScale (i + 1)]
    symm
    exact kwVectorTurnPhase_pos_scales
      (scale i) (scale (i + 1)) (hscalePos i) (hscalePos (i + 1))
      (polygon.edgeVector i) (polygon.edgeVector (i + 1))
      (polygon.edgeVector_ne_zero i) (polygon.edgeVector_ne_zero (i + 1))
  refine ⟨q, rational, rfl, raw, htargetTurn, ?_, hphase⟩
  intro i
  rw [KWFiniteSimplePolygon.edgeVector]
  change (kwRawEdge target i).re = 0 ∨ (kwRawEdge target i).im = 0
  rcases haxis i with h | h
  · left
    rw [hedgeScale i]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [h, mul_zero]
  · right
    rw [hedgeScale i]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [h, mul_zero]

theorem kwIntComplex_sub (a b : ℤ × ℤ) :
    kwIntComplex (a - b) = kwIntComplex a - kwIntComplex b := by
  apply Complex.ext <;> simp [kwIntComplex]



theorem KWFiniteSimplePolygon.axis_phaseCycle_eq_neg_one
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (haxis : ∀ i, (polygon.edgeVector i).re = 0 ∨
      (polygon.edgeVector i).im = 0)
    (hturn : ∀ i, KWRawTurnAdmissible polygon.vertex i) :
    kwVectorPhaseCycle polygon.edgeList = -1 := by
  obtain ⟨q, rational, hq, hraw, hrturn, hraxis, hphase⟩ :=
    polygon.exists_rational_axis_phaseModel haxis hturn
  obtain ⟨D, hD, p, hp⟩ :=
    rational.exists_integral_positive_scale q hq
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  let scaled := rational.mapLinearEquiv
    (kwPositiveScaleLinearEquiv (D : ℝ) hDreal)
  have hscaledEdge (i : Fin n) :
      kwRawEdge scaled.vertex i =
        (D : ℝ) * kwRawEdge rational.vertex i := by
    change scaled.edgeVector i = (D : ℝ) * rational.edgeVector i
    exact KWFiniteSimplePolygon.mapLinearEquiv_edgeVector _ _ _
  have hscaledTurn : ∀ i, KWRawTurnAdmissible scaled.vertex i :=
    KWRawTurnAdmissible.of_pos_edge_scales hrturn
      (fun _ ↦ (D : ℝ)) (fun _ ↦ hDreal) hscaledEdge
  have hscaledRaw : KWRawNonbacktrackingSimpleData scaled.vertex := by
    apply KWRawNonbacktrackingSimpleData.of_turnAdmissible
      scaled.vertex scaled.three_le
    · intro i
      change scaled.edgeVector i ≠ 0
      exact scaled.edgeVector_ne_zero i
    · exact hscaledTurn
    · intro i j hij
      simpa only [kwRawClosedEdge, KWFiniteSimplePolygon.closedEdge] using
        scaled.closedEdge_disjoint_of_nonincident hij
  have hpvertex : scaled.vertex = fun i ↦ kwIntComplex (p i) := by
    funext i
    exact hp i
  have hrawInt : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i)) := by
    rw [← hpvertex]
    exact hscaledRaw
  have hpedge (i : Fin n) : scaled.edgeVector i =
      kwIntComplex (p (i + 1) - p i) := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [hp (i + 1), hp i, kwIntComplex_sub]
  have hscaledAxis (i : Fin n) :
      (scaled.edgeVector i).re = 0 ∨ (scaled.edgeVector i).im = 0 := by
    have hedgeMap := KWFiniteSimplePolygon.mapLinearEquiv_edgeVector
      rational (kwPositiveScaleLinearEquiv (D : ℝ) hDreal) i
    change scaled.edgeVector i = (D : ℝ) * rational.edgeVector i at hedgeMap
    rcases hraxis i with h | h
    · left
      rw [hedgeMap]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [h, mul_zero]
    · right
      rw [hedgeMap]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      rw [h, mul_zero]
  have hpaxis (i : Fin n) :
      (p (i + 1) - p i).1 = 0 ∨ (p (i + 1) - p i).2 = 0 := by
    have hs := hscaledAxis i
    rw [hpedge i] at hs
    rcases hs with h | h
    · left
      have h' : (((p (i + 1) - p i).1 : ℤ) : ℝ) = 0 := by
        simpa [kwIntComplex] using h
      exact_mod_cast h'
    · right
      have h' : (((p (i + 1) - p i).2 : ℤ) : ℝ) = 0 := by
        simpa [kwIntComplex] using h
      exact_mod_cast h'
  have hedgeList : scaled.edgeList =
      List.ofFn (fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) := by
    unfold KWFiniteSimplePolygon.edgeList
    apply congrArg List.ofFn
    funext i
    exact hpedge i
  have hintegral := kwIntegralAxisPolygon_phaseCycle_eq_neg_one
    p hpaxis hrawInt
  rw [← hedgeList] at hintegral
  exact hphase.trans
    ((rational.phaseCycle_mapPositiveScale (D : ℝ) hDreal).trans hintegral)

end StatMech.FrontierA
