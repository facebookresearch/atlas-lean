/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedTranslation
import Code.FrontierD.FKRectDevelopedWideQuadratic



namespace StatMech.FrontierD

noncomputable section




theorem fkRectCritical_developedThreeByOne_horizontalMass_ge_of_twoByOne
    (R : FKRectTorus) (n : Nat) {q hardFloor squareFloor : Real}
    (hn : 0 < n) (hq : 1 <= q)
    (hhard : 0 <= hardFloor) (hsquare : 0 <= squareFloor)
    (hleft : hardFloor <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (2 * (n : Int)) 0 n))
    (hmiddle : squareFloor <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n n (2 * (n : Int)) 0 n))
    (hright : hardFloor <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n n (3 * (n : Int)) 0 n)) :
    hardFloor * squareFloor * hardFloor <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hleft0 := fkRectCriticalEventMass_nonneg R hq0
    (fkRectDevelopedRectangleHorizontalCrossingEvent
      R n 0 (2 * (n : Int)) 0 n)
  have hmiddle0 := fkRectCriticalEventMass_nonneg R hq0
    (fkRectDevelopedRectangleVerticalCrossingEvent
      R n n (2 * (n : Int)) 0 n)
  have hproduct : hardFloor * squareFloor * hardFloor <=
      fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (2 * (n : Int)) 0 n) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n n (2 * (n : Int)) 0 n) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n n (3 * (n : Int)) 0 n) := by
    exact mul_le_mul
      (mul_le_mul hleft hmiddle hsquare hleft0)
      hright hhard (mul_nonneg hleft0 hmiddle0)
  exact hproduct.trans
    (fkRectCritical_developedThreeByOne_horizontalMass_ge R n hn hq)



theorem fkRectCritical_developedMiddleSquareVerticalMass_ge_of_even
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n) (hnEven : Even n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    1 / (1 + q) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n n (2 * (n : Int)) 0 n) := by
  obtain ⟨shift, hshift⟩ := hnEven
  have hshiftInt : (n : Int) = (shift : Int) + shift := by
    exact_mod_cast hshift
  have hseed :=
    fkRectCritical_developedSquareVerticalMass_ge_one_div_one_add_q
      R n hn hwidth hheight hq
  have htranslate :=
    fkRectCritical_verticalCrossingMass_le_checkerboardTranslate
      R n (shift : Int) shift (zero_lt_one.trans_le hq) 0 n 0 n
  have hseed' : 1 / (1 + q) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 n) := by
    simpa only [fkRectDevelopedSquareVerticalCrossingEvent,
      fkRectDevelopedRectangleVerticalCrossingEvent] using hseed
  apply hseed'.trans
  have hx0 : (0 : Int) + ((shift : Int) + shift) = n := by omega
  have hx1 : (n : Int) + ((shift : Int) + shift) = 2 * n := by omega
  have hy0 : (0 : Int) + ((shift : Int) - shift) = 0 := by omega
  have hy1 : (n : Int) + ((shift : Int) - shift) = n := by omega
  simpa only [hx0, hx1, hy0, hy1] using htranslate



theorem fkRectCritical_developedThreeByOne_horizontalMass_ge_of_even_twoByOne
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n) (hnEven : Even n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q hardFloor : Real} (hq : 1 <= q) (hhard : 0 <= hardFloor)
    (hleft : hardFloor <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (2 * (n : Int)) 0 n))
    (hright : hardFloor <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n n (3 * (n : Int)) 0 n)) :
    hardFloor ^ 2 / (1 + q) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) := by
  have hsquare : 0 <= 1 / (1 + q) := by positivity
  have h := fkRectCritical_developedThreeByOne_horizontalMass_ge_of_twoByOne
    R n (by omega) hq hhard hsquare hleft
      (fkRectCritical_developedMiddleSquareVerticalMass_ge_of_even
        R n hn hnEven hwidth hheight hq)
      hright
  convert h using 1 <;> ring

end

end StatMech.FrontierD
