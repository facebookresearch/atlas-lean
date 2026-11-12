/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusCycleHolonomy








open scoped BigOperators

namespace StatMech.FrontierA

noncomputable def triangularTorusDirectionAngleReal : Fin 6 -> Real :=
  ![Real.pi, 0, -Real.pi / 2, Real.pi / 2,
    -3 * Real.pi / 4, Real.pi / 4]

noncomputable def triangularTorusDirectionAngle (a : Fin 6) : Real.Angle :=
  (triangularTorusDirectionAngleReal a : Real.Angle)

private theorem angle_sub_toReal_of_eq_mod
    (x y r : Real)
    (hmod : exists k : Int, x - y - r = 2 * Real.pi * k)
    (hrange : -Real.pi < r /\ r <= Real.pi) :
    ((x : Real.Angle) - (y : Real.Angle)).toReal = r := by
  rw [<- Real.Angle.coe_sub]
  have hangle : ((x - y : Real) : Real.Angle) = (r : Real.Angle) :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr hmod
  rw [hangle]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr hrange

theorem triangularTorusDirectionAngle_turn
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    (triangularTorusDirectionAngle b -
        triangularTorusDirectionAngle a).toReal =
      (triangularTorusTurnExponent a b : Real) * (Real.pi / 4) := by
  apply angle_sub_toReal_of_eq_mod
  · fin_cases a <;> fin_cases b <;>
      simp [triangularTorusDirectionAngleReal,
        triangularTorusDirectionReverse,
        triangularTorusTurnExponent] at hne ⊢
    all_goals
      solve
      | (refine ⟨(-1 : Int), ?_⟩; push_cast; ring)
      | (refine ⟨0, ?_⟩; push_cast; ring)
      | (refine ⟨1, ?_⟩; push_cast; ring)
  · fin_cases a <;> fin_cases b <;>
      simp [triangularTorusDirectionReverse,
        triangularTorusTurnExponent] at hne ⊢ <;>
      constructor <;> nlinarith [Real.pi_pos]

private theorem complex_arg_one_add_I_angle :
    (Complex.arg (1 + Complex.I) : Real.Angle) =
      ((Real.pi / 4 : Real) : Real.Angle) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [show (1 : Complex) + Complex.I =
      (Real.sqrt 2 : Complex) *
        (Real.cos (Real.pi / 4) +
          Real.sin (Real.pi / 4) * Complex.I) by
    apply Complex.ext <;>
      simp [Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]]
  exact Complex.arg_mul_cos_add_sin_mul_I_coe_angle hsqrt
    ((Real.pi / 4 : Real) : Real.Angle)

def triangularIntVector (a : Fin 6) : Complex :=
  triangularIntPoint (triangularIntStep a)

theorem triangularIntVector_arg (a : Fin 6) :
    (Complex.arg (triangularIntVector a) : Real.Angle) =
      triangularTorusDirectionAngle a := by
  fin_cases a
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_neg_one]
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_one]
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_neg_I]
    rw [<- Real.Angle.coe_neg]
    congr 1
    ring
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_I]
  · dsimp [triangularIntVector, triangularIntPoint,
      triangularIntStep, triangularTorusDirectionAngle,
      triangularTorusDirectionAngleReal]
    norm_num
    rw [show (-1 : Complex) + -Complex.I =
      -((1 : Complex) + Complex.I) by ring]
    rw [Complex.arg_neg_coe_angle (by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre),
      complex_arg_one_add_I_angle]
    have hang : ((Real.pi / 4 : Real) : Real.Angle) + Real.pi =
        ((-3 * Real.pi / 4 : Real) : Real.Angle) := by
      rw [<- Real.Angle.coe_add]
      rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      exact ⟨1, by push_cast; ring⟩
    rw [hang]
    congr 1
    ring
  · simpa [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal] using
      complex_arg_one_add_I_angle

theorem triangularIntPoint_add_sub (p q : Int × Int) :
    triangularIntPoint (p + q) - triangularIntPoint p =
      triangularIntPoint q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp [triangularIntPoint]
  push_cast
  ring

theorem triangularIntSimplePolygon_edgeVector
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 <= n) (hinjective : Function.Injective (triangularIntPos direction))
    (i : Fin n) :
    (triangularIntSimplePolygon direction hclosed hn hinjective).edgeVector i =
      triangularIntVector (direction i) := by
  unfold KWFiniteSimplePolygon.edgeVector
  dsimp only [triangularIntSimplePolygon]
  rw [triangularIntPos_succ direction hclosed i]
  exact triangularIntPoint_add_sub _ _

theorem kwVectorTurnPhase_triangularIntVector
    (a b : Fin 6) :
    kwVectorTurnPhase (triangularIntVector a) (triangularIntVector b) =
      kwAngleTurnPhase (triangularTorusDirectionAngle a)
        (triangularTorusDirectionAngle b) := by
  unfold kwVectorTurnPhase
  rw [triangularIntVector_arg, triangularIntVector_arg]



theorem exists_triangularTorusTurnExponent_sum_eq_eight_mul_odd_of_closed
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 <= n)
    (hinjective : Function.Injective (triangularIntPos direction)) :
    exists m : Int,
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * (2 * m + 1) := by
  let polygon := triangularIntSimplePolygon direction hclosed hn hinjective
  have hpolygon := kwFiniteSimplePolygonPhaseSign_adaptive polygon
  have hphase : kwLoopPhaseProduct
      (fun a b => kwAngleTurnPhase
        (triangularTorusDirectionAngle a)
        (triangularTorusDirectionAngle b)) direction = -1 := by
    have hedges : polygon.edgeList =
        List.ofFn (fun i => triangularIntVector (direction i)) := by
      unfold KWFiniteSimplePolygon.edgeList
      congr 1
      funext i
      dsimp only [polygon]
      exact triangularIntSimplePolygon_edgeVector
        direction hclosed hn hinjective i
    rw [hedges, kwVectorPhaseCycle_ofFn] at hpolygon
    unfold kwLoopPhaseProduct at hpolygon ⊢
    simpa only [kwVectorTurnPhase_triangularIntVector] using hpolygon
  obtain ⟨winding, hturn⟩ :=
    kw_totalPrincipalTurn_eq_int_mul_two_pi
      triangularTorusDirectionAngle direction
  have hodd : Odd winding :=
    kw_odd_winding_of_angleTurnPhase_eq_neg_one
      triangularTorusDirectionAngle direction winding hturn hphase
  have hsum :
      (∑ k, (triangularTorusDirectionAngle (direction (k + 1)) -
        triangularTorusDirectionAngle (direction k)).toReal : Real) =
      ((∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : Int) : Real) *
          (Real.pi / 4) := by
    rw [show (∑ k, (triangularTorusDirectionAngle (direction (k + 1)) -
        triangularTorusDirectionAngle (direction k)).toReal : Real) =
        ∑ k, (triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Real) *
            (Real.pi / 4) by
      apply Finset.sum_congr rfl
      intro k _
      exact triangularTorusDirectionAngle_turn _ _ (hnonbacktracking k)]
    rw [<- Finset.sum_mul]
    norm_cast
  have hreal :
      (((∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : Int) : Real) *
          (Real.pi / 4)) =
        (winding : Real) * (2 * Real.pi) := hsum.symm.trans hturn
  have hcast :
      (((∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : Int) : Real)) =
        8 * (winding : Real) := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp at hreal ⊢
    nlinarith
  have hint :
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * winding := by
    exact_mod_cast hcast
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m, ?_⟩
  rw [hint, hm]

end StatMech.FrontierA
