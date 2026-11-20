/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPolygonPerturbation
import Code.FrontierA.KacWardAngleHomotopy










namespace StatMech.FrontierA

open scoped BigOperators
open Set

theorem dist_vertexLine_lt_certificate
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    {target : Fin n → ℂ} (htarget : dist target polygon.vertex < h.radius)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (AffineMap.lineMap polygon.vertex target t) polygon.vertex <
      h.radius := by
  rw [dist_lineMap_left]
  have hnorm : ‖t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  calc
    ‖t‖ * dist polygon.vertex target ≤
        1 * dist polygon.vertex target :=
      mul_le_mul_of_nonneg_right hnorm dist_nonneg
    _ = dist target polygon.vertex := by rw [one_mul, dist_comm]
    _ < h.radius := htarget




noncomputable def KWPolygonPerturbationCertificate.pathPolygon
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    (target : Fin n → ℂ) (htarget : dist target polygon.vertex < h.radius)
    (t : ℝ) : KWFiniteSimplePolygon n :=
  if ht : t ∈ Icc (0 : ℝ) 1 then
    (h.rawSimple (AffineMap.lineMap polygon.vertex target t)
      (dist_vertexLine_lt_certificate h htarget ht)).toFiniteSimplePolygon
  else polygon

@[simp] theorem KWPolygonPerturbationCertificate.pathPolygon_vertex
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    (target : Fin n → ℂ) (htarget : dist target polygon.vertex < h.radius)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (h.pathPolygon target htarget t).vertex =
      AffineMap.lineMap polygon.vertex target t := by
  simp only [KWPolygonPerturbationCertificate.pathPolygon, ht, dite_true]
  rfl

theorem KWPolygonPerturbationCertificate.pathPolygon_vertex_continuous
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    (target : Fin n → ℂ) (htarget : dist target polygon.vertex < h.radius)
    (k : Fin n) :
    ContinuousOn (fun t : ℝ ↦ (h.pathPolygon target htarget t).vertex k)
      (Icc 0 1) := by
  have hline : Continuous (fun t : ℝ ↦
      (AffineMap.lineMap polygon.vertex target t) k) := by
    simp only [AffineMap.lineMap_apply_module, Pi.smul_apply, Pi.add_apply]
    fun_prop
  apply hline.continuousOn.congr
  intro t ht
  change (h.pathPolygon target htarget t).vertex k =
    (AffineMap.lineMap polygon.vertex target t) k
  exact congrFun (h.pathPolygon_vertex target htarget ht) k

theorem KWPolygonPerturbationCertificate.pathPolygon_angle_continuous
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    (target : Fin n → ℂ) (htarget : dist target polygon.vertex < h.radius)
    (k : Fin n) :
    ContinuousOn (fun t : ℝ ↦
      (Complex.arg ((h.pathPolygon target htarget t).edgeVector k) :
        Real.Angle)) (Icc 0 1) := by
  intro t ht
  have hedge : ContinuousWithinAt
      (fun s : ℝ ↦ (h.pathPolygon target htarget s).edgeVector k)
      (Icc 0 1) t := by
    unfold KWFiniteSimplePolygon.edgeVector
    exact (h.pathPolygon_vertex_continuous target htarget (k + 1) t ht).sub
      (h.pathPolygon_vertex_continuous target htarget k t ht)
  have hne : (h.pathPolygon target htarget t).edgeVector k ≠ 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [sub_ne_zero]
    exact (h.pathPolygon target htarget t).vertex_injective.ne
      ((h.pathPolygon target htarget t).add_one_ne_self k)
  simpa only [Function.comp_apply] using
    (Complex.continuousAt_arg_coe_angle hne).comp_continuousWithinAt
      (f := fun s : ℝ ↦
        (h.pathPolygon target htarget s).edgeVector k) hedge

private theorem edgeList_eq_of_vertex_eq
    {n : ℕ} [NeZero n] {p q : KWFiniteSimplePolygon n}
    (hvertex : p.vertex = q.vertex) : p.edgeList = q.edgeList := by
  unfold KWFiniteSimplePolygon.edgeList KWFiniteSimplePolygon.edgeVector
  rw [hvertex]



theorem KWPolygonPerturbationCertificate.phaseCycle_eq
    {n : ℕ} [NeZero n] {polygon target : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    (htarget : dist target.vertex polygon.vertex < h.radius) :
    kwVectorPhaseCycle polygon.edgeList =
      kwVectorPhaseCycle target.edgeList := by
  let path : ℝ → KWFiniteSimplePolygon n :=
    h.pathPolygon target.vertex htarget
  let angle : ℝ → Fin n → Real.Angle := fun t k ↦
    (Complex.arg ((path t).edgeVector k) : Real.Angle)
  have hcontinuous (k : Fin n) : ContinuousOn
      (fun t ↦ kwPrincipalHalfAnglePhase (angle t) k (k + 1))
      (Icc 0 1) := by
    apply kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1) k (k + 1)
    · exact h.pathPolygon_angle_continuous target.vertex htarget k
    · exact h.pathPolygon_angle_continuous target.vertex htarget (k + 1)
    · intro t ht
      exact (path t).consecutive_turn_ne_pi k
  have hinvariant := kwLoopPhaseProduct_principal_homotopy
    angle (fun k : Fin n ↦ k) hcontinuous
  have hpathPhase : kwVectorPhaseCycle (path 0).edgeList =
      kwVectorPhaseCycle (path 1).edgeList := by
    rw [KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn,
      KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn]
    simpa only [kwLoopPhaseProduct, kwPrincipalHalfAnglePhase,
      kwVectorTurnPhase, angle] using hinvariant
  have hzeroVertex : (path (0 : ℝ)).vertex = polygon.vertex := by
    rw [show (path (0 : ℝ)).vertex = AffineMap.lineMap polygon.vertex
        target.vertex (0 : ℝ) by
      exact h.pathPolygon_vertex target.vertex htarget (by norm_num)]
    exact AffineMap.lineMap_apply_zero (k := ℝ)
      polygon.vertex target.vertex
  have honeVertex : (path (1 : ℝ)).vertex = target.vertex := by
    rw [show (path (1 : ℝ)).vertex = AffineMap.lineMap polygon.vertex
        target.vertex (1 : ℝ) by
      exact h.pathPolygon_vertex target.vertex htarget (by norm_num)]
    exact AffineMap.lineMap_apply_one (k := ℝ)
      polygon.vertex target.vertex
  rw [edgeList_eq_of_vertex_eq hzeroVertex,
    edgeList_eq_of_vertex_eq honeVertex] at hpathPhase
  exact hpathPhase



theorem KWFiniteSimplePolygon.exists_rational_phaseModel
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) :
    ∃ (q : Fin n → ℚ × ℚ) (rational : KWFiniteSimplePolygon n),
      rational.vertex = kwRatVertex q ∧
      kwVectorPhaseCycle polygon.edgeList =
        kwVectorPhaseCycle rational.edgeList := by
  let h := (polygon.exists_perturbationCertificate hcross).some
  obtain ⟨q, hq⟩ := (denseRange_kwRatVertex (n := n)).exists_mem_open
    (s := Metric.ball polygon.vertex h.radius) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr h.radius_pos)
  have hqdist : dist (kwRatVertex q) polygon.vertex < h.radius := by
    simpa only [Metric.mem_ball] using hq
  let rational := (h.rawSimple (kwRatVertex q) hqdist).toFiniteSimplePolygon
  refine ⟨q, rational, rfl, ?_⟩
  exact h.phaseCycle_eq hqdist

end StatMech.FrontierA
