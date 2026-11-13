/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardGenericShear
import Code.FrontierA.KacWardAntipodalExclusion
import Code.FrontierA.KacWardAngleHomotopy










namespace StatMech.FrontierA

open scoped BigOperators
open Set

private theorem fin_add_two_ne_self
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) : i + 2 ≠ i := by
  intro h
  have htwo : (2 : Fin n) ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp [Nat.mod_eq_of_lt (by omega : 2 < n)]
  apply htwo
  calc
    (2 : Fin n) = (i + 2) - i := by abel
    _ = i - i := by rw [h]
    _ = 0 := sub_self i



theorem KWFiniteSimplePolygon.consecutive_turn_ne_pi
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (k : Fin n) :
    (Complex.arg (polygon.edgeVector (k + 1)) : Real.Angle) -
        (Complex.arg (polygon.edgeVector k) : Real.Angle) ≠
      (Real.pi : Real.Angle) := by
  have hk1k : k + 1 ≠ k := polygon.add_one_ne_self k
  have hk2k : (k + 1) + 1 ≠ k := by
    have h := fin_add_two_ne_self polygon.three_le k
    have hkstep : k + 2 = (k + 1) + 1 := by
      apply Fin.ext
      simp [Fin.val_add]
    intro heq
    exact h (hkstep.trans heq)
  have hk2k1 : (k + 1) + 1 ≠ k + 1 :=
    polygon.add_one_ne_self (k + 1)
  have hPnot : ¬Sbtw ℝ (polygon.vertex (k + 1)) (polygon.vertex k)
      (polygon.vertex ((k + 1) + 1)) := by
    apply polygon.vertex_not_strictly_between (k + 1) k
    · exact hk1k.symm
    · exact hk2k.symm
  have hCnot : ¬Sbtw ℝ (polygon.vertex k)
      (polygon.vertex ((k + 1) + 1))
      (polygon.vertex (k + 1)) := by
    apply polygon.vertex_not_strictly_between k ((k + 1) + 1)
    · exact hk2k
    · exact hk2k1
  have h := kw_angle_diagonal_ne_pi_of_no_between
    (P := polygon.vertex k) (A := polygon.vertex (k + 1))
    (C := polygon.vertex ((k + 1) + 1))
    (polygon.vertex_injective.ne hk1k.symm)
    (polygon.vertex_injective.ne hk2k1.symm)
    (polygon.vertex_injective.ne hk2k.symm) hPnot hCnot
  simpa only [KWFiniteSimplePolygon.edgeVector] using h



noncomputable def kwDoubleShearLinearEquiv (tx ty t : ℝ) : ℂ ≃ₗ[ℝ] ℂ :=
  (kwShearXLinearEquiv (t * tx)).trans (kwShearYLinearEquiv (t * ty))

@[simp] theorem kwDoubleShearLinearEquiv_zero (tx ty : ℝ) (z : ℂ) :
    kwDoubleShearLinearEquiv tx ty 0 z = z := by
  apply Complex.ext <;>
    simp [kwDoubleShearLinearEquiv, kwShearXLinearEquiv,
      kwShearYLinearEquiv, kwShearX, kwShearY]

@[simp] theorem kwDoubleShearLinearEquiv_one (tx ty : ℝ) (z : ℂ) :
    kwDoubleShearLinearEquiv tx ty 1 z =
      kwShearY ty (kwShearX tx z) := by
  simp [kwDoubleShearLinearEquiv, kwShearXLinearEquiv,
    kwShearYLinearEquiv]

theorem continuous_kwDoubleShearLinearEquiv_apply (tx ty : ℝ) (z : ℂ) :
    Continuous (fun t : ℝ ↦ kwDoubleShearLinearEquiv tx ty t z) := by
  change Continuous (fun t : ℝ ↦
    kwShearY (t * ty) (kwShearX (t * tx) z))
  unfold kwShearX kwShearY
  fun_prop

theorem continuousOn_kwDoubleShear_edge_arg
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (tx ty : ℝ) (k : Fin n) :
    ContinuousOn (fun t : ℝ ↦
      (Complex.arg (kwDoubleShearLinearEquiv tx ty t
        (polygon.edgeVector k)) : Real.Angle)) (Icc 0 1) := by
  intro t _
  have hedge : ContinuousAt (fun s : ℝ ↦
      kwDoubleShearLinearEquiv tx ty s (polygon.edgeVector k)) t :=
    (continuous_kwDoubleShearLinearEquiv_apply tx ty
      (polygon.edgeVector k)).continuousAt
  have hedgeNe : kwDoubleShearLinearEquiv tx ty t
      (polygon.edgeVector k) ≠ 0 := by
    apply (kwDoubleShearLinearEquiv tx ty t).map_ne_zero_iff.mpr
    unfold KWFiniteSimplePolygon.edgeVector
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne
      (polygon.add_one_ne_self k))
  have hc := (Complex.continuousAt_arg_coe_angle hedgeNe).comp
    (f := fun s : ℝ ↦ kwDoubleShearLinearEquiv tx ty s
      (polygon.edgeVector k)) hedge
  simpa only [Function.comp_apply] using hc.continuousWithinAt



theorem KWFiniteSimplePolygon.phaseCycle_mapDoubleShear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (tx ty : ℝ) :
    kwVectorPhaseCycle polygon.edgeList =
      kwVectorPhaseCycle
        (polygon.mapLinearEquiv
          (kwDoubleShearLinearEquiv tx ty 1)).edgeList := by
  let angle : ℝ → Fin n → Real.Angle := fun t k ↦
    (Complex.arg (kwDoubleShearLinearEquiv tx ty t
      (polygon.edgeVector k)) : Real.Angle)
  have hcontinuous (k : Fin n) : ContinuousOn
      (fun t ↦ kwPrincipalHalfAnglePhase (angle t) k (k + 1))
      (Icc 0 1) := by
    apply kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1) k (k + 1)
    · exact continuousOn_kwDoubleShear_edge_arg polygon tx ty k
    · exact continuousOn_kwDoubleShear_edge_arg polygon tx ty (k + 1)
    · intro t _
      let transformed := polygon.mapLinearEquiv
        (kwDoubleShearLinearEquiv tx ty t)
      have hturn := transformed.consecutive_turn_ne_pi k
      simpa only [transformed, KWFiniteSimplePolygon.mapLinearEquiv_edgeVector,
        angle] using hturn
  have hinvariant := kwLoopPhaseProduct_principal_homotopy
    angle (fun k : Fin n ↦ k) hcontinuous
  rw [KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn,
    KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn]
  simpa only [kwLoopPhaseProduct, kwPrincipalHalfAnglePhase,
    kwVectorTurnPhase, kwAngleTurnPhase, angle,
    kwDoubleShearLinearEquiv_zero,
    KWFiniteSimplePolygon.mapLinearEquiv_edgeVector] using hinvariant

end StatMech.FrontierA
