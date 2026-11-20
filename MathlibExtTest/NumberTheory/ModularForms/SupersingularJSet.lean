/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.SupersingularJSet

namespace ModularCurve

/-- Consumer with the original binders for the supersingular `j` set. -/
theorem exactSource {p : ℕ} {K : Type*} [Field K] [DecidableEq K] {j : K}
    (h : j ∈ ssJSet p K) (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.j = j)
    (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 :=
  (mem_ssJSet_iff.mp h) W hW P hP

example : eichlerMass 1 13 = 1 := by norm_num [eichlerMass_one]
example : autWeight 2 0 = 12 := autWeight_two_zero
example : autWeight 3 0 = 6 := autWeight_three_zero
example (j : ZMod 5) (h0 : j ≠ 0) (h : j ≠ 1728) : autWeight 5 j = 1 :=
  autWeight_of_ne (by norm_num) (by norm_num) h0 h
example : ssPolyTwo = Polynomial.X - Polynomial.C 0 := ssPolyTwo_eq
example : ssSetEleven.card = 2 := card_ssSetEleven
example : ssModelA 5 0 = 0 := ssModelA_zero 5
example : ssModelB 5 0 = 1 := ssModelB_zero 5
example (A B : ZMod 5) : affinePointCount 5 A B ≤ 25 := by
  have h := affinePointCount_le 5 A B
  norm_num at h ⊢
  exact h

/-- A higher-universe field can be used for the supersingular `j` set. -/
example {p : ℕ} {K : Type 1} [Field K] [DecidableEq K] (j : K) : Prop := j ∈ ssJSet p K

end ModularCurve
