/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Ported from fairinternal/formal-math `MathlibExtTest/Geometry/TwoD.lean`
at commit 5971cd008f11196e18b863495ddad4501d3e5585.
The test statements and proofs are retained; only the Atlas adapter
import prefix is removed for the native ATLAS module identities.
-/

module

public import MathlibExt.Geometry.TwoD

open scoped EuclideanSpace

@[expose] public section

universe u

-- Universe polymorphism: `Set.IsIsosceles` accepts a set in an arbitrary
-- universe with an arbitrary `Dist` instance.
example {α : Type u} [Dist α] (A : Set α) : Prop := A.IsIsosceles

noncomputable example : EuclideanGeometry.IsCcwConvexPolygon
    ![!₂[(0 : ℝ), 0], !₂[1, 0], !₂[0, 1]] := by
  have htriangle :
      (EuclideanGeometry.oangle !₂[(0 : ℝ), 0] !₂[1, 0] !₂[0, 1]).sign = -1 := by
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    have he : ![e 0, e 1] = e := by funext i; fin_cases i <;> rfl
    have harea : EuclideanGeometry.o.areaForm (e 0) (e 1) = 1 := by
      rw [Orientation.areaForm_to_volumeForm,
        EuclideanGeometry.o.volumeForm_robust e rfl, he]
      exact e.toBasis.det_self
    have hsign : (EuclideanGeometry.o.oangle (e 0) (e 1)).sign = 1 := by
      simp [Orientation.oangle, Orientation.kahler_apply_apply, harea, Real.Angle.sign]
    have hcalc := EuclideanGeometry.o.oangle_sign_smul_add_smul_smul_add_smul
      (e 0) (e 1) (-1) 0 (-1) 1
    have hsub1 : !₂[(0 : ℝ), 0] -ᵥ !₂[1, 0] = (-1 : ℝ) • e 0 + 0 • e 1 := by
      ext i; fin_cases i <;> simp [e]
    have hsub2 : !₂[(0 : ℝ), 1] -ᵥ !₂[1, 0] = (-1 : ℝ) • e 0 + 1 • e 1 := by
      ext i; fin_cases i <;> simp [e]
    unfold EuclideanGeometry.oangle
    rw [hsub1, hsub2]
    simp [hsign]
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
