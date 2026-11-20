/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.LogNonnegativeSinusoid
import Code.FrontierA.TriangularIsingSymbol
import Mathlib.Analysis.SpecialFunctions.Complex.Arg









open MeasureTheory

namespace StatMech.FrontierA

noncomputable def triangularIsingSliceA
    (J1 J2 J3 p : Real) : Real :=
  Real.cosh (2 * J1) * Real.cosh (2 * J2) * Real.cosh (2 * J3) +
    Real.sinh (2 * J1) * Real.sinh (2 * J2) * Real.sinh (2 * J3) -
    Real.sinh (2 * J1) * Real.cos p

noncomputable def triangularIsingSliceU
    (J2 J3 p : Real) : Real :=
  Real.sinh (2 * J2) + Real.sinh (2 * J3) * Real.cos p

noncomputable def triangularIsingSliceV
    (J3 p : Real) : Real :=
  -Real.sinh (2 * J3) * Real.sin p

theorem one_add_abs_sinh_mul_le_cosh_mul (x y : Real) :
    1 + |Real.sinh x * Real.sinh y| <= Real.cosh x * Real.cosh y := by
  have hx := Real.cosh_sq_sub_sinh_sq x
  have hy := Real.cosh_sq_sub_sinh_sq y
  have habs : |Real.sinh x * Real.sinh y| ^ 2 =
      Real.sinh x ^ 2 * Real.sinh y ^ 2 := by
    rw [abs_mul, mul_pow, sq_abs, sq_abs]
  have hdiff :
      0 <= (|Real.sinh x| - |Real.sinh y|) ^ 2 := sq_nonneg _
  have hx' : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := by linarith
  have hy' : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := by linarith
  have hsq :
      (1 + |Real.sinh x * Real.sinh y|) ^ 2 <=
        (Real.cosh x * Real.cosh y) ^ 2 := by
    rw [abs_mul]
    rw [mul_pow, hx', hy']
    nlinarith [sq_abs (Real.sinh x), sq_abs (Real.sinh y)]
  have hleft : 0 <= 1 + |Real.sinh x * Real.sinh y| := by positivity
  have hright : 0 <= Real.cosh x * Real.cosh y := by positivity
  nlinarith

theorem abs_sinh_lt_cosh (x : Real) : |Real.sinh x| < Real.cosh x := by
  have h := Real.cosh_sq_sub_sinh_sq x
  have ha := sq_abs (Real.sinh x)
  have hc := Real.cosh_pos x
  have habs := abs_nonneg (Real.sinh x)
  nlinarith



theorem triangularIsingSliceA_pos (J1 J2 J3 p : Real) :
    0 < triangularIsingSliceA J1 J2 J3 p := by
  let s1 := Real.sinh (2 * J1)
  let s2 := Real.sinh (2 * J2)
  let s3 := Real.sinh (2 * J3)
  let c1 := Real.cosh (2 * J1)
  let c2 := Real.cosh (2 * J2)
  let c3 := Real.cosh (2 * J3)
  have hc23 : 1 + |s2 * s3| <= c2 * c3 := by
    simpa [s2, s3, c2, c3] using
      one_add_abs_sinh_mul_le_cosh_mul (2 * J2) (2 * J3)
  have hc1 : |s1| < c1 := by
    simpa [s1, c1] using abs_sinh_lt_cosh (2 * J1)
  have hc10 : 0 <= c1 := (Real.cosh_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hc23 hc10
  have hs : -(|s1| * |s2 * s3|) <= s1 * (s2 * s3) := by
    simpa [abs_mul, mul_assoc] using neg_abs_le (s1 * (s2 * s3))
  have hconstant : |s1| < c1 * c2 * c3 + s1 * s2 * s3 := by
    have hgap : 0 <= (c1 - |s1|) * |s2 * s3| := by positivity
    nlinarith
  have hcos : s1 * Real.cos p <= |s1| := by
    calc
      s1 * Real.cos p <= |s1 * Real.cos p| := le_abs_self _
      _ = |s1| * |Real.cos p| := abs_mul _ _
      _ <= |s1| := mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one p)
  dsimp [triangularIsingSliceA, s1, s2, s3, c1, c2, c3]
  dsimp [s1, s2, s3, c1, c2, c3] at hconstant hcos
  linarith

theorem triangularIsingSymbol_eq_slice
    (J1 J2 J3 p q : Real) :
    triangularIsingSymbol J1 J2 J3 p q =
      triangularIsingSliceA J1 J2 J3 p -
        triangularIsingSliceU J2 J3 p * Real.cos q -
        triangularIsingSliceV J3 p * Real.sin q := by
  unfold triangularIsingSymbol triangularIsingSliceA
    triangularIsingSliceU triangularIsingSliceV
  rw [Real.cos_add]
  ring



theorem triangularIsingSlice_discriminant_nonneg
    {J1 J2 J3 p : Real}
    (hA : 0 < triangularIsingSliceA J1 J2 J3 p)
    (hnonneg : forall q, 0 <= triangularIsingSymbol J1 J2 J3 p q) :
    0 <= triangularIsingSliceA J1 J2 J3 p ^ 2 -
      (triangularIsingSliceU J2 J3 p ^ 2 +
        triangularIsingSliceV J3 p ^ 2) := by
  let A := triangularIsingSliceA J1 J2 J3 p
  let u := triangularIsingSliceU J2 J3 p
  let v := triangularIsingSliceV J3 p
  let z : Complex := (u : Complex) + (v : Complex) * Complex.I
  change 0 < A at hA
  change 0 <= A ^ 2 - (u ^ 2 + v ^ 2)
  by_cases hz : z = 0
  · have hure : z.re = 0 := by rw [hz]; rfl
    have hvim : z.im = 0 := by rw [hz]; rfl
    have hu : u = 0 := by simpa [z] using hure
    have hv : v = 0 := by simpa [z] using hvim
    rw [hu, hv]
    nlinarith
  · have hu : ‖z‖ * Real.cos (Complex.arg z) = u := by
      simpa [z] using Complex.norm_mul_cos_arg z
    have hv : ‖z‖ * Real.sin (Complex.arg z) = v := by
      simpa [z] using Complex.norm_mul_sin_arg z
    have hdirection :
        u * Real.cos (Complex.arg z) +
            v * Real.sin (Complex.arg z) = ‖z‖ := by
      calc
        _ = ‖z‖ * (Real.cos (Complex.arg z) ^ 2 +
            Real.sin (Complex.arg z) ^ 2) := by rw [← hu, ← hv]; ring
        _ = ‖z‖ := by rw [Real.cos_sq_add_sin_sq, mul_one]
    have hslice := hnonneg (Complex.arg z)
    rw [triangularIsingSymbol_eq_slice] at hslice
    change 0 <= A - u * Real.cos (Complex.arg z) -
      v * Real.sin (Complex.arg z) at hslice
    have hAnorm : ‖z‖ <= A := by linarith
    have hzsq : ‖z‖ ^ 2 = u ^ 2 + v ^ 2 := by
      rw [Complex.sq_norm]
      simp [z, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg z]



theorem integral_log_triangularIsingSymbol_slice
    {J1 J2 J3 p : Real}
    (hA : 0 < triangularIsingSliceA J1 J2 J3 p)
    (hnonneg : forall q, 0 <= triangularIsingSymbol J1 J2 J3 p q) :
    (∫ q in (-Real.pi)..Real.pi,
        Real.log (triangularIsingSymbol J1 J2 J3 p q)) =
      2 * Real.pi * Real.log
        (nonnegativeSinusoidQ
          (triangularIsingSliceA J1 J2 J3 p)
          (triangularIsingSliceU J2 J3 p)
          (triangularIsingSliceV J3 p) / 2) := by
  simp_rw [triangularIsingSymbol_eq_slice]
  exact integral_log_nonnegativeSinusoid hA
    (triangularIsingSlice_discriminant_nonneg hA hnonneg)

end StatMech.FrontierA
