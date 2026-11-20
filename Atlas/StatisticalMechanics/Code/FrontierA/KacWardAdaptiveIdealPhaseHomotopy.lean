/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealHomotopyTurns
import Code.FrontierA.KacWardAngleHomotopy





namespace StatMech.FrontierA

open scoped BigOperators
open Set


theorem KWRawTurnAdmissible.angle_ne_pi
    {m : ℕ} [NeZero m] {vertex : Fin m → ℂ} {i : Fin m}
    (hedge : ∀ j : Fin m, kwRawEdge vertex j ≠ 0)
    (h : KWRawTurnAdmissible vertex i) :
    (Complex.arg (kwRawEdge vertex (i + 1)) : Real.Angle) -
        (Complex.arg (kwRawEdge vertex i) : Real.Angle) ≠
      (Real.pi : Real.Angle) := by
  rcases h with hcross | ⟨r, hr, hforward⟩
  · exact kw_angle_sub_ne_pi_of_cross_ne_zero
      (hedge i) (hedge (i + 1)) hcross
  · rw [hforward, Complex.arg_real_mul _ hr, sub_self]
    intro hzero
    have hreal := congrArg Real.Angle.toReal hzero
    rw [Real.Angle.toReal_zero, Real.Angle.toReal_pi] at hreal
    exact Real.pi_ne_zero hreal.symm

theorem KWAdaptivePatchedData.idealAxisHomotopy_angle_continuous
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (k : Fin (n * (2 * (M + 1)))) :
    ContinuousOn (fun t : ℝ ↦
      (Complex.arg (kwRawEdge (patch.idealAxisHomotopyVertex t) k) :
        Real.Angle)) (Icc 0 1) := by
  intro t ht
  have hedge : ContinuousAt (fun s : ℝ ↦
      kwRawEdge (patch.idealAxisHomotopyVertex s) k) t := by
    unfold kwRawEdge
    exact (patch.idealAxisHomotopyVertex_continuous (k + 1)).continuousAt.sub
      (patch.idealAxisHomotopyVertex_continuous k).continuousAt
  have hne := patch.idealAxisHomotopy_rawEdge_ne_zero hcoords ht k
  simpa only [Function.comp_apply] using
    ((Complex.continuousAt_arg_coe_angle hne).comp
      (f := fun s : ℝ ↦
        kwRawEdge (patch.idealAxisHomotopyVertex s) k) hedge).continuousWithinAt



theorem KWAdaptivePatchedData.idealAxisHomotopy_phaseProduct
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    (∏ k : Fin (n * (2 * (M + 1))),
        kwVectorTurnPhase (kwRawEdge patch.idealVertex k)
          (kwRawEdge patch.idealVertex (k + 1))) =
      ∏ k : Fin (n * (2 * (M + 1))),
        kwVectorTurnPhase (kwRawEdge patch.vertex k)
          (kwRawEdge patch.vertex (k + 1)) := by
  let angle : ℝ → Fin (n * (2 * (M + 1))) → Real.Angle :=
    fun t k ↦
      (Complex.arg (kwRawEdge (patch.idealAxisHomotopyVertex t) k) :
        Real.Angle)
  have hcontinuous (k : Fin (n * (2 * (M + 1)))) : ContinuousOn
      (fun t ↦ kwPrincipalHalfAnglePhase (angle t) k (k + 1))
      (Icc 0 1) := by
    apply kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1) k (k + 1)
    · exact patch.idealAxisHomotopy_angle_continuous hcoords k
    · exact patch.idealAxisHomotopy_angle_continuous hcoords (k + 1)
    · intro t ht
      exact (patch.idealAxisHomotopy_turnAdmissible hcoords ht k).angle_ne_pi
        (patch.idealAxisHomotopy_rawEdge_ne_zero hcoords ht)
  have hinvariant := kwLoopPhaseProduct_principal_homotopy
    angle (fun k : Fin (n * (2 * (M + 1))) ↦ k) hcontinuous
  simpa only [kwLoopPhaseProduct, kwPrincipalHalfAnglePhase,
    kwVectorTurnPhase, angle,
    KWAdaptivePatchedData.idealAxisHomotopyVertex_zero,
    KWAdaptivePatchedData.idealAxisHomotopyVertex_one] using hinvariant

theorem KWAdaptivePatchedData.idealAxisHomotopy_phaseCycle
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
    kwVectorPhaseCycle (List.ofFn (kwRawEdge patch.idealVertex)) =
      kwVectorPhaseCycle (List.ofFn (kwRawEdge patch.vertex)) := by
  rw [kwVectorPhaseCycle_ofFn, kwVectorPhaseCycle_ofFn]
  exact patch.idealAxisHomotopy_phaseProduct hcoords

end StatMech.FrontierA
