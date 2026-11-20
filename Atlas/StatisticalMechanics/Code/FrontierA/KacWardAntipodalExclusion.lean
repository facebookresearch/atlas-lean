/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPolygonTurning





namespace StatMech.FrontierA




theorem kw_angle_diagonal_ne_pi_of_no_between {P A C : ℂ}
    (hPA : P ≠ A) (hAC : A ≠ C) (hPC : P ≠ C)
    (hPnot : ¬Sbtw ℝ A P C)
    (hCnot : ¬Sbtw ℝ P C A) :
    (Complex.arg (C - A) : Real.Angle) -
        (Complex.arg (A - P) : Real.Angle) ≠
      (Real.pi : Real.Angle) := by
  intro hpi
  have hx : A - P ≠ 0 := sub_ne_zero.mpr hPA.symm
  have hy : C - A ≠ 0 := sub_ne_zero.mpr hAC.symm
  have harg : Complex.arg ((C - A) / (A - P)) = Real.pi := by
    rw [← kw_angle_sub_toReal_eq_arg_div hx hy, hpi,
      Real.Angle.toReal_pi]
  have hneg := (Complex.arg_eq_pi_iff.mp harg).1
  have him := (Complex.arg_eq_pi_iff.mp harg).2
  let t : Real := -((C - A) / (A - P)).re
  have ht : 0 < t := by dsimp only [t]; linarith
  have hquot : (C - A) / (A - P) = (-(t : Real) : ℂ) := by
    apply Complex.ext
    · dsimp only [t]
      simp
    · simpa using him
  have hvec : C - A = (t : ℂ) * (P - A) := by
    have hmul := (div_eq_iff hx).mp hquot
    push_cast at hmul
    linear_combination hmul
  have hCline : C = AffineMap.lineMap A P t := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    linear_combination hvec
  rcases lt_trichotomy t 1 with htOne | htOne | htOne
  · apply hCnot
    apply (sbtw_comm).mpr
    rw [hCline]
    exact sbtw_lineMap_iff.mpr ⟨hPA.symm, ht, htOne⟩
  · apply hPC
    have htEq : t = 1 := htOne
    rw [hCline, htEq, AffineMap.lineMap_apply]
    simp
  · apply hPnot
    have htNe : t ≠ 0 := ht.ne'
    have hscale : ((t⁻¹ : Real) : ℂ) * (C - A) = P - A := by
      rw [hvec]
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ htNe]
      norm_num
    have hPline : P = AffineMap.lineMap A C t⁻¹ := by
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
      calc
        P = (P - A) + A := by ring
        _ = ((t⁻¹ : Real) : ℂ) * (C - A) + A := by rw [hscale]
    rw [hPline]
    exact sbtw_lineMap_iff.mpr
      ⟨hAC, inv_pos.mpr ht, inv_lt_one_of_one_lt₀ htOne⟩

end StatMech.FrontierA
