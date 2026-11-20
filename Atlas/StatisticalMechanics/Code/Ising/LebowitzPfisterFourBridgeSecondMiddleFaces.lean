/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeProductBounds








namespace StatMech.Ising

noncomputable section



def fourBridgeSecondMiddleNumerator (a b c d : Real) : Real :=
  a ^ 3 * b - 3 * a ^ 3 * d - 15 * a ^ 3 +
    3 * a ^ 2 * b * c - 21 * a ^ 2 * c - a * b ^ 3 +
    7 * a * b ^ 2 + 10 * a * b * d + 35 * a * b -
    9 * a * c ^ 2 + 39 * a * d + 15 * a + b ^ 2 * c -
    b * c + 9 * c * d - 15 * c




theorem fourBridge_bernsteinTwo_nonpos_of_enclosingFaces
    {a b c d L U : Real}
    (ha0 : 0 <= a) (hLU : L <= U) (hLc : L <= c) (hcU : c <= U)
    (hL : 0 <= fourBridgeSecondMiddleNumerator a b L d)
    (hU : 0 <= fourBridgeSecondMiddleNumerator a b U d) :
    fourBridgeVarianceSkewBernsteinCoeff a b c d 2 <= 0 := by
  have hN : 0 <= fourBridgeSecondMiddleNumerator a b c d := by
    by_cases h : L = U
    · have hc : c = L := by linarith
      simpa [hc] using hL
    · have hLU' : 0 < U - L := sub_pos.mpr (lt_of_le_of_ne hLU h)
      have h1 : 0 <= U - c := sub_nonneg.mpr hcU
      have h2 : 0 <= c - L := sub_nonneg.mpr hLc
      have hpos : 0 <=
          (U - c) * fourBridgeSecondMiddleNumerator a b L d +
            (c - L) * fourBridgeSecondMiddleNumerator a b U d +
            9 * a * (c - L) * (U - c) * (U - L) := by positivity
      have hid :
          (U - L) * fourBridgeSecondMiddleNumerator a b c d =
            (U - c) * fourBridgeSecondMiddleNumerator a b L d +
              (c - L) * fourBridgeSecondMiddleNumerator a b U d +
              9 * a * (c - L) * (U - c) * (U - L) := by
        unfold fourBridgeSecondMiddleNumerator
        ring
      rw [<- hid] at hpos
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hpos) hLU'
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  change -(fourBridgeSecondMiddleNumerator a b c d) / 15 <= 0
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hN) (by norm_num)



theorem fourBridge_bernsteinTwo_nonpos_at_productFace_of_le_two
    {a b d : Real}
    (ha0 : 0 <= a) (ha2 : a <= 2)
    (hb0 : 0 <= b) (hb6 : b <= 6)
    (hd0 : 0 <= d) (hd1 : d <= 1)
    (hp0 : a * (1 + d) <= b + d + 1) :
    fourBridgeVarianceSkewBernsteinCoeff a b (a * d) d 2 <= 0 := by
  let K := b * (3 * d + 1) - (9 * d ^ 2 + 24 * d + 15)
  let H := a ^ 2 * K - b ^ 3 + b ^ 2 * d + 7 * b ^ 2 +
    9 * b * d + 35 * b + 9 * d ^ 2 + 24 * d + 15
  have hcoef : 0 <= 3 * d + 1 := by positivity
  have hK : K <= 0 := by
    have hm := mul_nonneg (sub_nonneg.mpr hb6) hcoef
    dsimp [K]
    nlinarith [sq_nonneg d]
  have hN :
      a ^ 3 * b - 3 * a ^ 3 * d - 15 * a ^ 3 +
          3 * a ^ 2 * b * (a * d) - 21 * a ^ 2 * (a * d) -
          a * b ^ 3 + 7 * a * b ^ 2 + 10 * a * b * d +
          35 * a * b - 9 * a * (a * d) ^ 2 + 39 * a * d +
          15 * a + b ^ 2 * (a * d) - b * (a * d) +
          9 * (a * d) * d - 15 * (a * d) = a * H := by
    dsimp [H, K]
    ring
  have hH : 0 <= H := by
    by_cases hb : b <= d + 1
    · have hleft0 : 0 <= a * (1 + d) := mul_nonneg ha0 (by positivity)
      have hright0 : 0 <= b + d + 1 := by positivity
      have hsq := mul_self_le_mul_self hleft0 hp0
      have hdiff : 0 <= (b + d + 1) ^ 2 - a ^ 2 * (1 + d) ^ 2 := by
        nlinarith
      have hKdiff : K * ((b + d + 1) ^ 2 - a ^ 2 * (1 + d) ^ 2) <= 0 :=
        mul_nonpos_of_nonpos_of_nonneg hK hdiff
      have hlast : b * d - 6 * d - 6 <= 0 := by
        have hm := mul_nonneg (sub_nonneg.mpr hb6) hd0
        nlinarith
      have hprod : 0 <=
          -b * (d - 1) * (b - d - 1) * (b * d - 6 * d - 6) := by
        have h1 : 0 <= -b * (d - 1) :=
          mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hb0)
            (sub_nonpos.mpr hd1)
        have h2 : 0 <= (b - d - 1) * (b * d - 6 * d - 6) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) hlast
        nlinarith [mul_nonneg h1 h2]
      have hid :
          (1 + d) ^ 2 * H =
            -b * (d - 1) * (b - d - 1) * (b * d - 6 * d - 6) -
              K * ((b + d + 1) ^ 2 - a ^ 2 * (1 + d) ^ 2) := by
        dsimp [H, K]
        ring
      have hden : 0 < (1 + d) ^ 2 := sq_pos_of_pos (by linarith)
      nlinarith
    · have hb' : d + 1 <= b := le_of_not_ge hb
      have haSq : a ^ 2 <= 4 := by nlinarith
      have hKmul : 4 * K <= a ^ 2 * K := by
        exact mul_le_mul_of_nonpos_right haSq hK
      have hbquad : b * (b - 6) <= 0 :=
        mul_nonpos_of_nonneg_of_nonpos hb0 (sub_nonpos.mpr hb6)
      have hQ : b ^ 2 - 6 * b - 27 * d - 45 <= 0 := by nlinarith
      have hprod : 0 <=
          -(b - d - 1) * (b ^ 2 - 6 * b - 27 * d - 45) := by
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hQ
      have hid :
          4 * K - b ^ 3 + b ^ 2 * d + 7 * b ^ 2 +
              9 * b * d + 35 * b + 9 * d ^ 2 + 24 * d + 15 =
            -(b - d - 1) * (b ^ 2 - 6 * b - 27 * d - 45) := by
        dsimp [K]
        ring
      dsimp [H]
      nlinarith
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  rw [show
      a ^ 3 * b - 3 * a ^ 3 * d - 15 * a ^ 3 +
          3 * a ^ 2 * b * (a * d) - 21 * a ^ 2 * (a * d) -
          a * b ^ 3 + 7 * a * b ^ 2 + 10 * a * b * d +
          35 * a * b - 9 * a * (a * d) ^ 2 + 39 * a * d +
          15 * a + b ^ 2 * (a * d) - b * (a * d) +
          9 * (a * d) * d - 15 * (a * d) = a * H from hN]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg ha0 hH)) (by norm_num)


theorem fourBridgeSecondMiddleNumerator_productFace_nonneg_of_le_two
    {a b d : Real}
    (ha0 : 0 <= a) (ha2 : a <= 2)
    (hb0 : 0 <= b) (hb6 : b <= 6)
    (hd0 : 0 <= d) (hd1 : d <= 1)
    (hp0 : a * (1 + d) <= b + d + 1) :
    0 <= fourBridgeSecondMiddleNumerator a b (a * d) d := by
  have h := fourBridge_bernsteinTwo_nonpos_at_productFace_of_le_two
    ha0 ha2 hb0 hb6 hd0 hd1 hp0
  simp only [fourBridgeVarianceSkewBernsteinCoeff] at h
  unfold fourBridgeSecondMiddleNumerator
  nlinarith



theorem fourBridge_bernsteinTwo_nonpos_at_rankFace_of_two_le
    {a b d : Real}
    (ha2 : 2 <= a) (ha4 : a <= 4)
    (hb0 : 0 <= b) (hb6 : b <= 6)
    (hd0 : 0 <= d) (hd1 : d <= 1)
    (hp0 : 2 * a + d <= b + 3)
    (hpair : 3 * a <= 6 + b) :
    fourBridgeVarianceSkewBernsteinCoeff a b (a + 2 * d - 2) d 2 <= 0 := by
  let N := 4 * a ^ 3 * b - 3 * a ^ 3 * d - 45 * a ^ 3 +
    6 * a ^ 2 * b * d - 6 * a ^ 2 * b - 78 * a ^ 2 * d +
    78 * a ^ 2 - a * b ^ 3 + 8 * a * b ^ 2 + 10 * a * b * d +
    34 * a * b - 36 * a * d ^ 2 + 120 * a * d - 36 * a +
    2 * b ^ 2 * d - 2 * b ^ 2 - 2 * b * d + 2 * b +
    18 * d ^ 2 - 48 * d + 30
  have ha0 : 0 <= a := by linarith
  have hb11 : 0 <= 11 - b := by linarith
  have hb14 : 0 <= 14 - b := by linarith
  have hdterm : 0 <= 2 * (d - 1) * (d - 4) := by
    exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by nlinarith)
  have hN : 0 <= N := by
    by_cases ha : a <= d + 3
    · let B := 2 * a + d - 3
      let Q := -2 * a ^ 2 * b + 2 * a ^ 2 * d + 22 * a ^ 2 -
        a * b ^ 2 - a * b * d + 11 * a * b - a * d ^ 2 +
        28 * a * d - 3 * a + 2 * b * d - 2 * b +
        2 * d ^ 2 - 10 * d + 8
      have hQ : 0 <= Q := by
        have h1 : 0 <= 2 * a ^ 2 * (11 - b) := by positivity
        have h2 : 0 <= a * b * (11 - b) := by positivity
        have h28 : 0 <= 28 - b := by linarith
        have h3 : 0 <= a * d * (28 - b) := by positivity
        have h4 : -12 <= 2 * b * (d - 1) := by
          have hm := mul_nonneg (sub_nonneg.mpr hb6) (sub_nonneg.mpr hd1)
          nlinarith
        have hdSq : d ^ 2 <= 1 := by nlinarith
        have haSq : 4 * a <= 10 * a ^ 2 := by nlinarith [sq_nonneg a]
        dsimp [Q]
        nlinarith
      have hdiff : 0 <= b - B := by dsimp [B]; linarith
      have hmul := mul_nonneg hdiff hQ
      have hboundary : 0 <=
          (a - 2) * (d - 1) * (a - d - 3) * (a + d - 1) := by
        have h23 : 0 <= (d - 1) * (a - d - 3) :=
          mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hd1) (by linarith)
        have hfirst := mul_nonneg (sub_nonneg.mpr ha2) h23
        have hlast := mul_nonneg hfirst (by linarith : 0 <= a + d - 1)
        nlinarith
      have hidDiff :
          N - (a - 2) * (d - 1) * (a - d - 3) * (a + d - 1) =
            (b - B) * Q := by
        dsimp [N, B, Q]
        ring
      nlinarith
    · have ha' : d + 3 <= a := le_of_not_ge ha
      let B := 3 * a - 6
      let Q := -5 * a ^ 3 - 3 * a ^ 2 * b + 6 * a ^ 2 * d +
        54 * a ^ 2 - a * b ^ 2 + 14 * a * b + 16 * a * d -
        56 * a + 2 * b * d - 2 * b - 14 * d + 14
      have ha3 : 3 <= a := by linarith
      have hQ : 0 <= Q := by
        have h18 : 0 <= 18 - b := by linarith
        have h1 : 0 <= 3 * a ^ 2 * (18 - b) := by positivity
        have h2 : 0 <= a * b * (14 - b) := by positivity
        have h3 : -12 <= 2 * b * (d - 1) := by
          have hm := mul_nonneg (sub_nonneg.mpr hb6) (sub_nonneg.mpr hd1)
          nlinarith
        have hbracket : 7 <= -5 * a ^ 2 + 36 * a - 56 := by
          have hm : (a - 3) * (5 * a - 21) <= 0 :=
            mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha3) (by linarith)
          nlinarith
        have hamul := mul_le_mul_of_nonneg_left hbracket ha0
        dsimp [Q]
        nlinarith
      have hdiff : 0 <= b - B := by dsimp [B]; linarith
      have hmul := mul_nonneg hdiff hQ
      let F := 5 * a ^ 3 - 34 * a ^ 2 - 12 * a * d +
        36 * a + 6 * d - 6
      have hF : F <= 0 := by
        have haCube : 5 * a ^ 3 <= 20 * a ^ 2 := by
          have hm := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha4)
          nlinarith
        have haSq : 3 * a <= a ^ 2 := by nlinarith
        have hdcoef : d * (6 - 12 * a) <= 0 :=
          mul_nonpos_of_nonneg_of_nonpos hd0 (by nlinarith)
        dsimp [F]
        nlinarith
      have hboundary : 0 <= -3 * (a - d - 3) * F := by
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)) hF
      have hidDiff :
          N - (-3 * (a - d - 3) * F) = (b - B) * Q := by
        dsimp [N, B, Q, F]
        ring
      nlinarith
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  have hid :
      a ^ 3 * b - 3 * a ^ 3 * d - 15 * a ^ 3 +
          3 * a ^ 2 * b * (a + 2 * d - 2) -
          21 * a ^ 2 * (a + 2 * d - 2) - a * b ^ 3 +
          7 * a * b ^ 2 + 10 * a * b * d + 35 * a * b -
          9 * a * (a + 2 * d - 2) ^ 2 + 39 * a * d + 15 * a +
          b ^ 2 * (a + 2 * d - 2) - b * (a + 2 * d - 2) +
          9 * (a + 2 * d - 2) * d - 15 * (a + 2 * d - 2) = N := by
    dsimp [N]
    ring
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hN) (by norm_num)


theorem fourBridgeSecondMiddleNumerator_rankFace_nonneg_of_two_le
    {a b d : Real}
    (ha2 : 2 <= a) (ha4 : a <= 4)
    (hb0 : 0 <= b) (hb6 : b <= 6)
    (hd0 : 0 <= d) (hd1 : d <= 1)
    (hp0 : 2 * a + d <= b + 3)
    (hpair : 3 * a <= 6 + b) :
    0 <= fourBridgeSecondMiddleNumerator a b (a + 2 * d - 2) d := by
  have h := fourBridge_bernsteinTwo_nonpos_at_rankFace_of_two_le
    ha2 ha4 hb0 hb6 hd0 hd1 hp0 hpair
  simp only [fourBridgeVarianceSkewBernsteinCoeff] at h
  unfold fourBridgeSecondMiddleNumerator
  nlinarith

end

end StatMech.Ising
