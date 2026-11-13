/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedWideDual
import Code.FrontierD.FKRectCrossingAlgebra



open Set

namespace StatMech.FrontierD

noncomputable section



theorem fkRectDevelopedSquare_dualHorizontalCompl_subset_vertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height) :
    fkRectDualEvent R
        (fkRectDevelopedSquareHorizontalCrossingEvent R n)ᶜ ⊆
      fkRectDevelopedSquareVerticalCrossingEvent R n := by
  rintro eta ⟨omega, hno, rfl⟩
  exact fkRectDevelopedSquare_faceDualVertical_imp_dualVertical
    R n hn hwidth hheight omega
      (fkRectDevelopedSquare_compl_subset_faceDualVertical
        R n hn hno)




theorem fkRectCritical_developedSquareVerticalMass_ge_one_div_one_add_q
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (1 + q) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  let H := fkRectDevelopedSquareHorizontalCrossingEvent R n
  let V := fkRectDevelopedSquareVerticalCrossingEvent R n
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_le_q_mul_dualEvent R hq Hᶜ
  have hmono := fkRectCriticalEventMass_mono R hq0
    (fkRectDevelopedSquare_dualHorizontalCompl_subset_vertical
      R n hn hwidth hheight)
  rw [fkRectCriticalEventMass_compl R hq0 H] at hdual
  have hlinear : 1 - fkRectCriticalEventMass R q H ≤
      q * fkRectCriticalEventMass R q V :=
    hdual.trans (mul_le_mul_of_nonneg_left hmono hq0.le)
  have hmassEq : fkRectCriticalEventMass R q H =
      fkRectCriticalEventMass R q V := by
    exact fkRectCritical_developedSquareHorizontalMass_eq_verticalMass
      R n q
  rw [hmassEq] at hlinear
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith




theorem fkRectCritical_threeByOneHorizontal_sq_div_one_add_q_sq_le_vertical
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) ^ 2 / (1 + q ^ 2) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) := by
  let H := fkRectDevelopedRectangleHorizontalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  let V := fkRectDevelopedRectangleVerticalCrossingEvent
    R n 0 (3 * (n : Int)) 0 n
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hH0 : 0 ≤ fkRectCriticalEventMass R q H :=
    fkRectCriticalEventMass_nonneg R hq0 H
  have hH1 : fkRectCriticalEventMass R q H ≤ 1 := by
    have hmass := fkRectCriticalEventMass_mono R hq0
      (show H ⊆ Set.univ from Set.subset_univ H)
    rw [fkRectCriticalEventMass_univ R hq0] at hmass
    exact hmass
  have hHsq : fkRectCriticalEventMass R q H ^ 2 ≤ 1 := by
    nlinarith
  have hwide : 1 / (1 + q) ≤ fkRectCriticalEventMass R q V := by
    have hsquare :=
      fkRectCritical_developedSquareVerticalMass_ge_one_div_one_add_q
        R n hn (by omega) (by omega) hq
    exact hsquare.trans
      (fkRectCritical_developedSquareVerticalMass_le_threeByOneVerticalMass
        R n hq0)
  have hdenSq : 0 < 1 + q ^ 2 := by positivity
  have hden : 0 < 1 + q := by linarith
  have hconst : 1 / (1 + q ^ 2) ≤ 1 / (1 + q) := by
    rw [div_le_div_iff₀ hdenSq hden]
    nlinarith
  dsimp only [H, V] at hHsq hwide ⊢
  calc
    _ ≤ 1 / (1 + q ^ 2) := by
      exact div_le_div_of_nonneg_right hHsq hdenSq.le
    _ ≤ 1 / (1 + q) := hconst
    _ ≤ _ := hwide



theorem fkRectCritical_threeByOneVerticalMass_ge_one_div_eight_mul_pow_six
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (8 * q ^ 6) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) := by
  apply crossing_vertical_ge_one_div_eight_mul_pow_six hq
    (fkRectCriticalEventMass_nonneg R (zero_lt_one.trans_le hq) _)
    (fkRectCritical_one_le_threeByOneVertical_add_q_sq_mul_horizontal
      R n hn hwidth hheight hq)
  exact fkRectCritical_threeByOneHorizontal_sq_div_one_add_q_sq_le_vertical
    R n hn hwidth hheight hq

end

end StatMech.FrontierD
