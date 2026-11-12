/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeSecondMiddleHighRank
import Code.Ising.LebowitzPfisterFourBridgeReduction










namespace StatMech.Ising

noncomputable section


private theorem quadratic_nonpos_of_enclosing
    {A B C x L U : Real}
    (hA : 0 <= A) (hLU : L <= U) (hLx : L <= x) (hxU : x <= U)
    (hL : A * L ^ 2 + B * L + C <= 0)
    (hU : A * U ^ 2 + B * U + C <= 0) :
    A * x ^ 2 + B * x + C <= 0 := by
  by_cases h : L = U
  · have hx : x = L := by linarith
    simpa [hx] using hL
  · have hgap : 0 < U - L := sub_pos.mpr (lt_of_le_of_ne hLU h)
    have hleft : 0 <= U - x := sub_nonneg.mpr hxU
    have hright : 0 <= x - L := sub_nonneg.mpr hLx
    have htermL : (U - x) * (A * L ^ 2 + B * L + C) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hleft hL
    have htermU : (x - L) * (A * U ^ 2 + B * U + C) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hright hU
    have hcorr : 0 <= A * (x - L) * (U - x) * (U - L) := by
      positivity
    have hid :
        (U - L) * (A * x ^ 2 + B * x + C) =
          (U - x) * (A * L ^ 2 + B * L + C) +
            (x - L) * (A * U ^ 2 + B * U + C) -
              A * (x - L) * (U - x) * (U - L) := by
      ring
    have hmul : (U - L) * (A * x ^ 2 + B * x + C) <= 0 := by
      rw [hid]
      linarith
    exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hmul) hgap



theorem fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_le_one
    {a b d : Real}
    (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hd0 : 0 <= d) :
    0 <= fourBridgeSecondMiddleNumerator a b
      ((a + 3 * a * b - a ^ 3) / 3) d := by
  let P := 3 * a ^ 6 - 15 * a ^ 4 * b - 27 * a ^ 4 +
    19 * a ^ 2 * b ^ 2 + 74 * a ^ 2 * b + 18 * a ^ 2 * d +
    54 * a ^ 2 - 19 * b ^ 2 - 57 * b * d - 59 * b - 126 * d - 30
  have haSq : a ^ 2 <= 1 := by nlinarith [sq_nonneg a]
  have hdcoef : 18 * a ^ 2 - 57 * b - 126 <= 0 := by nlinarith
  have hdterm : d * (18 * a ^ 2 - 57 * b - 126) <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hd0 hdcoef
  have hQ : 0 <=
      3 * a ^ 4 - 15 * a ^ 2 * b - 24 * a ^ 2 +
        19 * b ^ 2 + 59 * b + 30 := by
    have hab : a ^ 2 * b <= b := by nlinarith
    nlinarith [sq_nonneg b, sq_nonneg (a ^ 2)]
  have hbase :
      3 * a ^ 6 - 15 * a ^ 4 * b - 27 * a ^ 4 +
          19 * a ^ 2 * b ^ 2 + 74 * a ^ 2 * b + 54 * a ^ 2 -
          19 * b ^ 2 - 59 * b - 30 <= 0 := by
    have hid :
        3 * a ^ 6 - 15 * a ^ 4 * b - 27 * a ^ 4 +
            19 * a ^ 2 * b ^ 2 + 74 * a ^ 2 * b + 54 * a ^ 2 -
            19 * b ^ 2 - 59 * b - 30 =
          (a - 1) * (a + 1) *
            (3 * a ^ 4 - 15 * a ^ 2 * b - 24 * a ^ 2 +
              19 * b ^ 2 + 59 * b + 30) := by
      ring
    rw [hid]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha1) (by linarith)) hQ
  have hP : P <= 0 := by
    dsimp [P]
    nlinarith
  have hid :
      fourBridgeSecondMiddleNumerator a b
          ((a + 3 * a * b - a ^ 3) / 3) d = -a * P / 3 := by
    dsimp [P]
    unfold fourBridgeSecondMiddleNumerator
    ring
  rw [hid]
  have hm : 0 <= a * (-P) := mul_nonneg ha0 (neg_nonneg.mpr hP)
  nlinarith



theorem fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_one_le_two
    {a b d : Real}
    (ha1 : 1 <= a) (ha2 : a <= 2)
    (hd0 : 0 <= d)
    (hprod : a * d <= (a + 3 * a * b - a ^ 3) / 3)
    (hrank0 : (a + 3 * a * b - a ^ 3) / 3 <= 1 - a + b + d) :
    0 <= fourBridgeSecondMiddleNumerator a b
      ((a + 3 * a * b - a ^ 3) / 3) d := by
  by_cases ha : a = 1
  · subst a
    have hP :
        3 * (1 : Real) ^ 6 - 15 * (1 : Real) ^ 4 * b - 27 * (1 : Real) ^ 4 +
            19 * (1 : Real) ^ 2 * b ^ 2 + 74 * (1 : Real) ^ 2 * b +
            18 * (1 : Real) ^ 2 * d + 54 * (1 : Real) ^ 2 -
            19 * b ^ 2 - 57 * b * d - 59 * b - 126 * d - 30 <= 0 := by
      nlinarith [mul_nonneg hd0 (sq_nonneg b)]
    unfold fourBridgeSecondMiddleNumerator
    nlinarith
  · by_cases haTwo : a = 2
    · subst a
      have hb : b = d + 1 := by
        field_simp at hprod hrank0
        nlinarith
      rw [hb]
      unfold fourBridgeSecondMiddleNumerator
      ring_nf
      positivity
    · have haPos : 0 < a - 1 := sub_pos.mpr (lt_of_le_of_ne ha1 (Ne.symm ha))
      have haTwoLt : a < 2 := lt_of_le_of_ne ha2 haTwo
      let L := (a ^ 2 + 3 * d - 1) / 3
      let U := (a ^ 3 - 4 * a + 3 * d + 3) / (3 * (a - 1))
      let A := 19 * (a ^ 2 - 1)
      let B := -15 * a ^ 4 + 74 * a ^ 2 - 57 * d - 59
      let C := 3 * a ^ 6 - 27 * a ^ 4 + 18 * a ^ 2 * d +
        54 * a ^ 2 - 126 * d - 30
      have hLb : L <= b := by
        dsimp [L]
        have hprod' : a * d <= a * ((1 + 3 * b - a ^ 2) / 3) := by
          convert hprod using 1
          ring
        have hamul := le_of_mul_le_mul_left hprod' (by linarith : 0 < a)
        nlinarith
      have hbU : b <= U := by
        dsimp [U]
        have hden : 0 < 3 * (a - 1) := by positivity
        apply (le_div_iff₀ hden).2
        field_simp at hrank0
        nlinarith
      have hLU : L <= U := hLb.trans hbU
      have hAL : 0 <= A := by dsimp [A]; nlinarith [sq_nonneg a]
      have hfeas : a <= 1 + 3 * d := by
        have h := hrank0
        have hp := hprod
        field_simp at h hp
        have hS : 0 <= 1 + 3 * b - a ^ 2 - 3 * d := by nlinarith
        have hR : 0 <= a ^ 3 - 3 * a * b - 4 * a + 3 * b + 3 * d + 3 := by
          nlinarith
        have hmul := mul_nonneg haPos.le hS
        have hid :
            (a ^ 3 - 3 * a * b - 4 * a + 3 * b + 3 * d + 3) +
                (a - 1) * (1 + 3 * b - a ^ 2 - 3 * d) =
              (a - 2) * (a - 3 * d - 1) := by ring
        have hsum := add_nonneg hR hmul
        rw [hid] at hsum
        have hprod0 : 0 <= (a - 2) * (a - 3 * d - 1) := hsum
        exact le_of_not_gt fun hbad =>
          (not_lt_of_ge hprod0
            (mul_neg_of_neg_of_pos (sub_neg.mpr haTwoLt) (by linarith)))
      let x := a - 1
      let e := d - x / 3
      have hx0 : 0 <= x := by dsimp [x]; linarith
      have hx1 : x <= 1 := by dsimp [x]; linarith
      have he0 : 0 <= e := by dsimp [e, x]; linarith
      have hxSq : x ^ 2 <= 1 := by nlinarith [sq_nonneg x]
      have hQL : 0 <=
          a ^ 4 - 21 * a ^ 2 * d - 29 * a ^ 2 +
            171 * d ^ 2 + 345 * d + 28 := by
        have hbracket : 0 <= x ^ 3 - 3 * x ^ 2 - 18 * x + 54 := by
          have hxCube0 : 0 <= x ^ 3 := mul_nonneg (sq_nonneg x) hx0
          nlinarith
        have hecoef : 0 <= -21 * x ^ 2 + 72 * x + 324 := by nlinarith
        have hid :
            a ^ 4 - 21 * a ^ 2 * d - 29 * a ^ 2 +
                171 * d ^ 2 + 345 * d + 28 =
              171 * e ^ 2 + e * (-21 * x ^ 2 + 72 * x + 324) +
                x * (x ^ 3 - 3 * x ^ 2 - 18 * x + 54) := by
          dsimp [x, e]
          ring
        rw [hid]
        positivity
      have hPL : A * L ^ 2 + B * L + C <= 0 := by
        have hid :
            A * L ^ 2 + B * L + C =
              (a - 2) * (a + 2) *
                (a ^ 4 - 21 * a ^ 2 * d - 29 * a ^ 2 +
                  171 * d ^ 2 + 345 * d + 28) / 9 := by
          dsimp [A, B, C, L]
          ring
        rw [hid]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha2) (by linarith)) hQL)
          (by norm_num)
      have hQU : 0 <=
          a ^ 6 - 6 * a ^ 5 - 5 * a ^ 4 - 21 * a ^ 3 * d +
            60 * a ^ 3 + 63 * a ^ 2 * d - 41 * a ^ 2 +
            174 * a * d - 54 * a + 171 * d ^ 2 - 216 * d + 45 := by
        have h1 : 0 <= x ^ 4 - 27 * x ^ 2 + 162 := by nlinarith
        have h2 : 0 <= 351 - 21 * x ^ 2 := by nlinarith
        have hid :
            a ^ 6 - 6 * a ^ 5 - 5 * a ^ 4 - 21 * a ^ 3 * d +
                60 * a ^ 3 + 63 * a ^ 2 * d - 41 * a ^ 2 +
                174 * a * d - 54 * a + 171 * d ^ 2 - 216 * d + 45 =
              171 * e ^ 2 + e * x * (351 - 21 * x ^ 2) +
                x ^ 2 * (x ^ 4 - 27 * x ^ 2 + 162) := by
          dsimp [x, e]
          ring
        rw [hid]
        positivity
      have hPU : A * U ^ 2 + B * U + C <= 0 := by
        have hden0 : 0 < (3 * (a - 1)) ^ 2 := sq_pos_of_pos (by positivity)
        have hid :
            (3 * (a - 1)) ^ 2 * (A * U ^ 2 + B * U + C) =
              (a - 2) * (a - 1) *
                (a ^ 6 - 6 * a ^ 5 - 5 * a ^ 4 - 21 * a ^ 3 * d +
                  60 * a ^ 3 + 63 * a ^ 2 * d - 41 * a ^ 2 +
                  174 * a * d - 54 * a + 171 * d ^ 2 - 216 * d + 45) := by
          dsimp [A, B, C, U]
          field_simp
          ring
        have hrhs : (a - 2) * (a - 1) *
              (a ^ 6 - 6 * a ^ 5 - 5 * a ^ 4 - 21 * a ^ 3 * d +
                60 * a ^ 3 + 63 * a ^ 2 * d - 41 * a ^ 2 +
                174 * a * d - 54 * a + 171 * d ^ 2 - 216 * d + 45) <= 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha2) haPos.le) hQU
        have hmulNon :
            (3 * (a - 1)) ^ 2 * (A * U ^ 2 + B * U + C) <= 0 := by
          rw [hid]
          exact hrhs
        exact nonpos_of_mul_nonpos_left
          (by simpa [mul_comm] using hmulNon) hden0
      have hP : A * b ^ 2 + B * b + C <= 0 :=
        quadratic_nonpos_of_enclosing hAL hLU hLb hbU hPL hPU
      have hidP :
          A * b ^ 2 + B * b + C =
            3 * a ^ 6 - 15 * a ^ 4 * b - 27 * a ^ 4 +
              19 * a ^ 2 * b ^ 2 + 74 * a ^ 2 * b + 18 * a ^ 2 * d +
              54 * a ^ 2 - 19 * b ^ 2 - 57 * b * d - 59 * b -
              126 * d - 30 := by
        dsimp [A, B, C]
        ring
      have hidN :
          fourBridgeSecondMiddleNumerator a b
              ((a + 3 * a * b - a ^ 3) / 3) d =
            -a * (A * b ^ 2 + B * b + C) / 3 := by
        rw [hidP]
        unfold fourBridgeSecondMiddleNumerator
        ring
      rw [hidN]
      have hm : 0 <= a * (-(A * b ^ 2 + B * b + C)) :=
        mul_nonneg (by linarith) (neg_nonneg.mpr hP)
      nlinarith

set_option maxHeartbeats 2000000 in



theorem fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_one_le_two
    {a b d : Real}
    (ha1 : 1 <= a) (ha2 : a <= 2)
    (hd0 : 0 <= d) (hd1 : d <= 1)
    (hprod : a * d <= 1 - a + b + d)
    (hrank3 : 1 - a + b + d <= 2 + a - 2 * d) :
    0 <= fourBridgeSecondMiddleNumerator a b (1 - a + b + d) d := by
  let x := a - 1
  let y := b - x * (1 + d)
  have hx0 : 0 <= x := by dsimp [x]; linarith
  have hx1 : x <= 1 := by dsimp [x]; linarith
  have hy0 : 0 <= y := by dsimp [x, y] at *; nlinarith
  have hyU : y <= (3 + x) * (1 - d) := by
    dsimp [x, y] at *
    nlinarith
  by_cases hd : d = 1
  · subst d
    have hy : y = 0 := by
      have : y <= 0 := by simpa using hyU
      linarith
    have hb : b = x * 2 := by dsimp [y] at hy; linarith
    dsimp [x] at hb
    rw [hb]
    unfold fourBridgeSecondMiddleNumerator
    ring_nf
    positivity
  · have hdlt : d < 1 := lt_of_le_of_ne hd1 hd
    let D := (3 + x) * (1 - d)
    let t := y / D
    have hD : 0 < D := by dsimp [D]; positivity
    have ht0 : 0 <= t := div_nonneg hy0 hD.le
    have ht1 : t <= 1 := (div_le_one hD).2 (by simpa [D] using hyU)
    have hyparam : y = (3 + x) * (1 - d) * t := by
      dsimp [t, D]
      field_simp
    have hbparam : b = x * (1 + d) + (3 + x) * (1 - d) * t := by
      dsimp [y] at hyparam
      linarith
    let R1 := -9 * d ^ 2 * x ^ 3 - d ^ 2 * x ^ 2 + 6 * d ^ 2 * x +
      3 * d * x ^ 4 - 9 * d * x ^ 3 + 24 * d * x ^ 2 +
      21 * d * x + 9 * d + x ^ 4 - 15 * x ^ 3 + 12 * x ^ 2 + 54 * x
    let R2 := 27 * d ^ 2 * x ^ 2 + 6 * d ^ 2 * x - 9 * d ^ 2 -
      21 * d * x ^ 3 + 7 * d * x ^ 2 + 3 * d * x + 27 * d +
      2 * x ^ 4 - 9 * x ^ 3 + 42 * x ^ 2 + 117 * x
    have hbase1 : 0 <= x * (x ^ 3 - 15 * x ^ 2 + 12 * x + 54) := by
      have hbr : 0 <= x ^ 3 - 15 * x ^ 2 + 12 * x + 54 := by
        have hxCube0 := mul_nonneg (sq_nonneg x) hx0
        have hxSq : x ^ 2 <= 1 := by nlinarith [sq_nonneg x]
        nlinarith
      positivity
    have hmid1 : 0 <= 3 * x ^ 4 - 18 * x ^ 3 + 23 * x ^ 2 +
        21 * x + 9 := by
      have hxCubeLe : x ^ 3 <= x := by
        have := mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg x] : x ^ 2 <= 1) hx0
        simpa [pow_succ, mul_assoc] using this
      nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
    have hR1 : 0 <= R1 := by
      have hid : R1 =
          x * (x ^ 3 - 15 * x ^ 2 + 12 * x + 54) +
            d * (3 * x ^ 4 - 18 * x ^ 3 + 23 * x ^ 2 + 21 * x + 9) +
            6 * d ^ 2 * x + 9 * d * x ^ 3 * (1 - d) +
            d * x ^ 2 * (1 - d) := by
        dsimp [R1]
        ring
      rw [hid]
      positivity
    have hbase2 : 0 <= x * (2 * x ^ 3 - 9 * x ^ 2 + 42 * x + 117) := by
      have hbr : 0 <= 2 * x ^ 3 - 9 * x ^ 2 + 42 * x + 117 := by
        have hxSq : x ^ 2 <= 1 := by nlinarith [sq_nonneg x]
        have hxCube0 := mul_nonneg (sq_nonneg x) hx0
        nlinarith
      positivity
    have hmid2 : 0 <= -21 * x ^ 3 + 7 * x ^ 2 + 3 * x + 18 := by
      have hxCubeLe : x ^ 3 <= x := by
        have := mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg x] : x ^ 2 <= 1) hx0
        simpa [pow_succ, mul_assoc] using this
      nlinarith [sq_nonneg x]
    have hR2 : 0 <= R2 := by
      have hid : R2 =
          x * (2 * x ^ 3 - 9 * x ^ 2 + 42 * x + 117) +
            d * (-21 * x ^ 3 + 7 * x ^ 2 + 3 * x + 18) +
            27 * d ^ 2 * x ^ 2 + 6 * d ^ 2 * x + 9 * d * (1 - d) := by
        dsimp [R2]
        ring
      rw [hid]
      positivity
    have hQ3 : -9 * d * x - 3 * d + 3 * x ^ 2 - 7 * x <= 0 := by
      have hdx : 0 <= d * (9 * x + 3) := by positivity
      have hxterm : 0 <= x * (7 - 3 * x) :=
        mul_nonneg hx0 (by linarith)
      nlinarith
    let A0 := -x * (d - 1) * (d + 1) * (x - 1) * (x + 1) * (d * x - 6)
    let A1 := -(d - 1) * R1 / 3
    let A2 := -(d - 1) * R2 / 3
    let A3 := 3 * (d - 1) * (-d + x + 2) *
      (-9 * d * x - 3 * d + 3 * x ^ 2 - 7 * x)
    have hA0 : 0 <= A0 := by
      have hfirst : 0 <= -x * (d - 1) := by
        have := mul_nonneg hx0 (sub_nonneg.mpr hd1)
        nlinarith
      have hdx : d * x <= 1 := by
        have := mul_le_mul hd1 hx1 hx0 (by norm_num : (0 : Real) <= 1)
        nlinarith
      have hlast : 0 <= (x - 1) * (d * x - 6) :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx1)
          (by linarith)
      dsimp [A0]
      have := mul_nonneg (mul_nonneg hfirst (by linarith : 0 <= d + 1))
        (mul_nonneg (by linarith : 0 <= x + 1) hlast)
      nlinarith
    have hA1 : 0 <= A1 := by
      dsimp [A1]
      exact div_nonneg
        (mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr hd1)) hR1) (by norm_num)
    have hA2 : 0 <= A2 := by
      dsimp [A2]
      exact div_nonneg
        (mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr hd1)) hR2) (by norm_num)
    have hA3 : 0 <= A3 := by
      have hm : 0 <= (d - 1) *
          (-9 * d * x - 3 * d + 3 * x ^ 2 - 7 * x) :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hd1) hQ3
      dsimp [A3]
      have hlin : 0 <= -d + x + 2 := by linarith
      nlinarith [mul_nonneg hlin hm]
    have hid :
        fourBridgeSecondMiddleNumerator a b (1 - a + b + d) d =
          A0 * (1 - t) ^ 3 + 3 * A1 * t * (1 - t) ^ 2 +
            3 * A2 * t ^ 2 * (1 - t) + A3 * t ^ 3 := by
      rw [hbparam]
      dsimp [x, R1, R2, A0, A1, A2, A3]
      unfold fourBridgeSecondMiddleNumerator
      ring
    rw [hid]
    positivity

set_option maxHeartbeats 2000000 in



theorem fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_one_le_two
    {a b d : Real}
    (ha1 : 1 <= a) (ha2 : a <= 2)
    (hd1 : d <= 1)
    (hrank0 : 2 + a - 2 * d <= 1 - a + b + d)
    (hp2 : b <= 3 + 3 * d) :
    0 <= fourBridgeSecondMiddleNumerator a b (2 + a - 2 * d) d := by
  let x := a - 1
  let q := 3 * d - x
  let y := b - (3 + 2 * x - 3 * d)
  have hx0 : 0 <= x := by dsimp [x]; linarith
  have hx1 : x <= 1 := by dsimp [x]; linarith
  have hy0 : 0 <= y := by dsimp [x, y] at *; linarith
  have hyU : y <= 2 * q := by dsimp [q, y]; linarith
  have hq0 : 0 <= q := by linarith
  have hqU : q <= 3 - x := by dsimp [q]; linarith
  by_cases hq : q = 0
  · have hy : y = 0 := by linarith
    have hdEq : d = x / 3 := by
      dsimp [q] at hq
      linarith
    have hbEq : b = 3 + x := by
      dsimp [y] at hy
      rw [hdEq] at hy
      linarith
    rw [hdEq, hbEq]
    have hid :
        fourBridgeSecondMiddleNumerator a (3 + x)
            (2 + a - 2 * (x / 3)) (x / 3) =
          -(2 * x + 6) * (x - 3) * (8 * x) / 3 := by
      dsimp [x]
      unfold fourBridgeSecondMiddleNumerator
      ring
    rw [hid]
    have hm : 0 <= (2 * x + 6) * (3 - x) * (8 * x) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith))
        (mul_nonneg (by norm_num) hx0)
    nlinarith
  · have hqPos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    let t := y / (2 * q)
    have ht0 : 0 <= t := div_nonneg hy0 (by positivity)
    have ht1 : t <= 1 := (div_le_one (by positivity : 0 < 2 * q)).2 hyU
    have hyparam : y = 2 * q * t := by
      dsimp [t]
      field_simp
    have hdparam : d = (q + x) / 3 := by dsimp [q]; linarith
    have hbparam : b = 3 + 2 * x - 3 * d + 2 * q * t := by
      dsimp [y] at hyparam
      linarith
    let R0 := 48 * x ^ 3 - 432 * x
    let S1 := 9 * q ^ 2 * x + 7 * q ^ 2 - 15 * q * x ^ 2 +
      16 * q * x + 51 * q + 24 * x ^ 3 - 36 * x ^ 2 - 420 * x - 504
    let S2 := -9 * q ^ 2 * x - 11 * q ^ 2 - 3 * q * x ^ 2 +
      28 * q * x + 63 * q + 30 * x ^ 3 - 102 * x ^ 2 - 894 * x - 954
    let R1 := R0 + q * S1
    let R2 := R0 + q * S2
    let R3 := 3 * q ^ 2 * x + 5 * q ^ 2 + 3 * q * x ^ 2 -
      24 * q * x - 39 * q + 4 * x ^ 2 - 12 * x
    have hR0 : R0 <= 0 := by
      have hxSq : x ^ 2 <= 1 := by nlinarith [sq_nonneg x]
      dsimp [R0]
      nlinarith [mul_nonneg (sq_nonneg x) hx0]
    have hqSq : q ^ 2 <= (3 - x) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hq0 hqU
    have hS1 : S1 <= 0 := by
      have hc1 : 0 <= 9 * x + 7 := by positivity
      have hc2 : 0 <= 16 * x + 51 := by positivity
      have h1 := mul_le_mul_of_nonneg_right hqSq hc1
      have h2 := mul_le_mul_of_nonneg_right hqU hc2
      have hE :
          (3 - x) ^ 2 * (9 * x + 7) + (3 - x) * (16 * x + 51) +
              24 * x ^ 3 - 420 * x - 504 <= 0 := by
        have hid :
            (3 - x) ^ 2 * (9 * x + 7) + (3 - x) * (16 * x + 51) +
                24 * x ^ 3 - 420 * x - 504 =
              3 * (x + 1) * (11 * x ^ 2 - 32 * x - 96) := by ring
        rw [hid]
        have hbr : 11 * x ^ 2 - 32 * x - 96 <= 0 := by
          nlinarith [sq_nonneg x]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hbr
      dsimp [S1]
      nlinarith [mul_nonneg hq0 hx0, mul_nonneg hq0 (sq_nonneg x)]
    have hS2 : S2 <= 0 := by
      have hc : 0 <= 28 * x + 63 := by positivity
      have h1 := mul_le_mul_of_nonneg_right hqU hc
      have hE :
          (3 - x) * (28 * x + 63) + 30 * x ^ 3 - 894 * x - 954 <= 0 := by
        have hxCube : x ^ 3 <= 1 := by
          have hxSq : x ^ 2 <= 1 := by nlinarith [sq_nonneg x]
          have := mul_le_mul hxSq hx1 hx0 (by norm_num : (0 : Real) <= 1)
          nlinarith
        nlinarith [sq_nonneg x]
      dsimp [S2]
      nlinarith [mul_nonneg hq0 hx0, mul_nonneg hq0 (sq_nonneg x),
        mul_nonneg (sq_nonneg q) hx0]
    have hR1 : R1 <= 0 := by
      dsimp [R1]
      exact add_nonpos hR0 (mul_nonpos_of_nonneg_of_nonpos hq0 hS1)
    have hR2 : R2 <= 0 := by
      dsimp [R2]
      exact add_nonpos hR0 (mul_nonpos_of_nonneg_of_nonpos hq0 hS2)
    have hR3 : R3 <= 0 := by
      let S3 := (3 * x + 5) * q + 3 * x ^ 2 - 24 * x - 39
      have hcoef : 0 <= 3 * x + 5 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hqU hcoef
      have hS3 : S3 <= 0 := by
        have hid :
            (3 * x + 5) * (3 - x) + 3 * x ^ 2 - 24 * x - 39 =
              -4 * (5 * x + 6) := by ring
        dsimp [S3]
        nlinarith
      have hbase : 4 * x ^ 2 - 12 * x <= 0 := by
        have hxSq : x ^ 2 <= x := by nlinarith [sq_nonneg x]
        nlinarith
      have hid : R3 = 4 * x ^ 2 - 12 * x + q * S3 := by
        dsimp [R3, S3]
        ring
      rw [hid]
      exact add_nonpos hbase (mul_nonpos_of_nonneg_of_nonpos hq0 hS3)
    let A0 := -(-q + 2 * x + 6) * (q + x - 3) *
      (3 * q * x + q + 8 * x) / 3
    let A1 := -R1 / 9
    let A2 := -R2 / 9
    let A3 := -(q + 4 * x + 12) * R3 / 3
    have hA0 : 0 <= A0 := by
      have hfirst : 0 <= -q + 2 * x + 6 := by linarith
      have hsecond : q + x - 3 <= 0 := by linarith
      have hthird : 0 <= 3 * q * x + q + 8 * x := by positivity
      dsimp [A0]
      have hm := mul_nonneg
        (mul_nonneg hfirst (neg_nonneg.mpr hsecond)) hthird
      nlinarith
    have hA1 : 0 <= A1 := by
      dsimp [A1]
      exact div_nonneg (neg_nonneg.mpr hR1) (by norm_num)
    have hA2 : 0 <= A2 := by
      dsimp [A2]
      exact div_nonneg (neg_nonneg.mpr hR2) (by norm_num)
    have hA3 : 0 <= A3 := by
      dsimp [A3]
      have hm : 0 <= (q + 4 * x + 12) * (-R3) :=
        mul_nonneg (by positivity) (neg_nonneg.mpr hR3)
      nlinarith
    have hid :
        fourBridgeSecondMiddleNumerator a b (2 + a - 2 * d) d =
          A0 * (1 - t) ^ 3 + 3 * A1 * t * (1 - t) ^ 2 +
            3 * A2 * t ^ 2 * (1 - t) + A3 * t ^ 3 := by
      rw [hbparam, hdparam]
      dsimp [x, R0, S1, S2, R1, R2, R3, A0, A1, A2, A3]
      unfold fourBridgeSecondMiddleNumerator
      ring
    rw [hid]
    positivity

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_oneCoeff_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha2 : fourBridgeOneCoeff G J hf w x y z <= 2) :
    fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 2 <= 0 := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  let p := fourBridgeRankMass a b c d
  let L := a * d
  let UG := (a + 3 * a * b - a ^ 3) / 3
  let U0 := 1 - a + b + d
  let U3 := 2 + a - 2 * d
  have ha0 : 0 <= a := by dsimp [a, fourBridgeOneCoeff]; positivity
  have hb0 : 0 <= b := by dsimp [b, fourBridgeTwoCoeff]; positivity
  have hd0 : 0 <= d := by dsimp [d, fourBridgeFourCoeff]; positivity
  have hpi (i : Fin 5) : 0 <= p i := by
    exact fourBridgeRankMass_nonneg G J hf w x y z i
  have hsum : p 0 + p 1 + p 2 + p 3 + p 4 = 1 :=
    fourBridgeRankMass_sum a b c d
  have hb6 : b <= 6 := by
    have hb := fourBridge_rankMass_recover_two a b c d
    dsimp only [p] at hsum hpi
    linarith [hpi 0, hpi 1, hpi 2, hpi 3, hpi 4]
  have hd1 : d <= 1 := by
    have hd := fourBridge_rankMass_recover_four a b c d
    dsimp only [p] at hsum hpi
    linarith [hpi 0, hpi 1, hpi 2, hpi 3, hpi 4]
  have hLc : L <= c := by
    dsimp only [L, a, c, d]
    exact fourBridgeOneCoeff_mul_fourCoeff_le_threeCoeff
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  have hcU0 : c <= U0 := by
    have h0 := hpi 0
    dsimp [p, U0, fourBridgeRankMass] at h0 ⊢
    linarith
  have hcU3 : c <= U3 := by
    have h3 := hpi 3
    dsimp [p, U3, fourBridgeRankMass] at h3 ⊢
    linarith
  have hcUG : c <= UG := by
    have hzero :=
      LowFaceCertificate.fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos
        G J hf hJ hhf hwx hwy hwz hxy hxz hyz
    have hzero' : fourBridgeVarianceSkewBernsteinCoeff a b c d 0 <= 0 := by
      simpa [a, b, c, d] using hzero
    have hid := fourBridgeVarianceSkewBernsteinCoeff_zero_eq_thirdCumulant a b c d
    dsimp [UG]
    simp only [fourBridgeVarianceSkewBernsteinCoeff] at hzero'
    nlinarith
  have hp0 : a * (1 + d) <= b + d + 1 := by
    dsimp [L, U0] at hLc hcU0 ⊢
    linarith
  have hL : 0 <= fourBridgeSecondMiddleNumerator a b L d := by
    dsimp only [L]
    exact fourBridgeSecondMiddleNumerator_productFace_nonneg_of_le_two
      ha0 ha2 hb0 hb6 hd0 hd1 hp0
  by_cases ha1 : a <= 1
  · have hU : 0 <= fourBridgeSecondMiddleNumerator a b UG d := by
      dsimp only [UG]
      exact fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_le_one
        ha0 ha1 hb0 hd0
    apply fourBridge_bernsteinTwo_nonpos_of_enclosingFaces
      (a := a) (b := b) (c := c) (d := d) (L := L) (U := UG)
    · exact ha0
    · exact hLc.trans hcUG
    · exact hLc
    · exact hcUG
    · exact hL
    · exact hU
  · have ha1' : 1 <= a := le_of_not_ge ha1
    rcases le_total UG U0 with hG0 | h0G
    · have hU : 0 <= fourBridgeSecondMiddleNumerator a b UG d := by
        dsimp only [UG]
        apply fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_one_le_two
          ha1' ha2 hd0
        · dsimp only [L, UG] at hLc hcUG ⊢
          exact hLc.trans hcUG
        · exact hG0
      apply fourBridge_bernsteinTwo_nonpos_of_enclosingFaces
        (a := a) (b := b) (c := c) (d := d) (L := L) (U := UG)
      · exact ha0
      · exact hLc.trans hcUG
      · exact hLc
      · exact hcUG
      · exact hL
      · exact hU
    · rcases le_total U0 U3 with h03 | h30
      · have hU : 0 <= fourBridgeSecondMiddleNumerator a b U0 d := by
          dsimp only [U0]
          apply fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_one_le_two
            ha1' ha2 hd0 hd1
          · dsimp only [L, U0] at hLc hcU0 ⊢
            exact hLc.trans hcU0
          · exact h03
        apply fourBridge_bernsteinTwo_nonpos_of_enclosingFaces
          (a := a) (b := b) (c := c) (d := d) (L := L) (U := U0)
        · exact ha0
        · exact hLc.trans hcU0
        · exact hLc
        · exact hcU0
        · exact hL
        · exact hU
      · have hp2 : b <= 3 + 3 * d := by
          have h2 := hpi 2
          dsimp [p, fourBridgeRankMass] at h2
          linarith
        have hU : 0 <= fourBridgeSecondMiddleNumerator a b U3 d := by
          dsimp only [U3]
          exact fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_one_le_two
            ha1' ha2 hd1 h30 hp2
        apply fourBridge_bernsteinTwo_nonpos_of_enclosingFaces
          (a := a) (b := b) (c := c) (d := d) (L := L) (U := U3)
        · exact ha0
        · exact hLc.trans hcU3
        · exact hLc
        · exact hcU3
        · exact hL
        · exact hU



theorem fourBridgeVarianceSkewBernsteinCoeff_two_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 2 <= 0 := by
  rcases le_total (fourBridgeOneCoeff G J hf w x y z) 2 with ha2 | ha2
  · exact fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_oneCoeff_le_two
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz ha2
  · exact fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_two_le_oneCoeff
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz ha2



theorem fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_three_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hthree : fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 3 <= 0)
    (hfour : fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 4 <= 0) :
    forall i, fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) i <= 0 := by
  apply fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle
    G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  · exact fourBridgeVarianceSkewBernsteinCoeff_one_nonpos
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  · exact fourBridgeVarianceSkewBernsteinCoeff_two_nonpos
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  · exact hthree
  · exact hfour

end

end StatMech.Ising
