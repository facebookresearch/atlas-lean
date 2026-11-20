/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterThreeBridgeActual








open Finset SimpleGraph
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem threeBridge_sum_mul_sum_le_two_add_three
    {u₁ u₂ u₃ v₁₂ v₁₃ v₂₃ c : Real}
    (hu₁ : 0 <= u₁) (hu₂ : 0 <= u₂) (hu₃ : 0 <= u₃)
    (hv₁₂ : v₁₂ <= 1) (hv₁₃ : v₁₃ <= 1) (hv₂₃ : v₂₃ <= 1)
    (hop₁ : u₁ * v₂₃ <= c) (hop₂ : u₂ * v₁₃ <= c)
    (hop₃ : u₃ * v₁₂ <= c) :
    (u₁ + u₂ + u₃) * (v₁₂ + v₁₃ + v₂₃) <=
      2 * (u₁ + u₂ + u₃) + 3 * c := by
  have h₁₁ : u₁ * v₁₂ <= u₁ := by
    simpa using mul_le_mul_of_nonneg_left hv₁₂ hu₁
  have h₁₂ : u₁ * v₁₃ <= u₁ := by
    simpa using mul_le_mul_of_nonneg_left hv₁₃ hu₁
  have h₂₁ : u₂ * v₁₂ <= u₂ := by
    simpa using mul_le_mul_of_nonneg_left hv₁₂ hu₂
  have h₂₂ : u₂ * v₂₃ <= u₂ := by
    simpa using mul_le_mul_of_nonneg_left hv₂₃ hu₂
  have h₃₁ : u₃ * v₁₃ <= u₃ := by
    simpa using mul_le_mul_of_nonneg_left hv₁₃ hu₃
  have h₃₂ : u₃ * v₂₃ <= u₃ := by
    simpa using mul_le_mul_of_nonneg_left hv₂₃ hu₃
  nlinarith




theorem threeBridge_ghsSquare_le_firstBound
    {x y z p q s : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (hp : x * y <= p) (hq : x * z <= q) (hs : y * z <= s) :
    3 * (x * s + y * q + z * p - 2 * x * y * z) ^ 2 <=
      (x ^ 2 + y ^ 2 + z ^ 2) +
        3 * (x ^ 2 + y ^ 2 + z ^ 2) * (p ^ 2 + q ^ 2 + s ^ 2) -
        (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
  let P := p - x * y
  let Q := q - x * z
  let R := s - y * z
  have hP : 0 <= P := by dsimp [P]; linarith
  have hQ : 0 <= Q := by dsimp [Q]; linarith
  have hR : 0 <= R := by dsimp [R]; linarith
  have hx : 0 <= x ^ 2 * (1 - x ^ 4) := by
    have : x ^ 2 <= 1 := by nlinarith
    exact mul_nonneg (sq_nonneg x) (by nlinarith [sq_nonneg (x ^ 2)])
  have hy : 0 <= y ^ 2 * (1 - y ^ 4) := by
    have : y ^ 2 <= 1 := by nlinarith
    exact mul_nonneg (sq_nonneg y) (by nlinarith [sq_nonneg (y ^ 2)])
  have hz : 0 <= z ^ 2 * (1 - z ^ 4) := by
    have : z ^ 2 <= 1 := by nlinarith
    exact mul_nonneg (sq_nonneg z) (by nlinarith [sq_nonneg (z ^ 2)])
  have hnonneg : 0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      3 * ((x * P - z * R) ^ 2 + (y * P - z * Q) ^ 2 +
        (x * Q - y * R) ^ 2) +
      6 * P * x * y * (x ^ 2 + y ^ 2) +
      6 * Q * x * z * (x ^ 2 + z ^ 2) +
      6 * R * y * z * (y ^ 2 + z ^ 2) := by positivity
  have hid :
      (x ^ 2 + y ^ 2 + z ^ 2) +
          3 * (x ^ 2 + y ^ 2 + z ^ 2) * (p ^ 2 + q ^ 2 + s ^ 2) -
          (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 -
          3 * (x * s + y * q + z * p - 2 * x * y * z) ^ 2 =
        x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
          z ^ 2 * (1 - z ^ 4) +
        3 * ((x * P - z * R) ^ 2 + (y * P - z * Q) ^ 2 +
          (x * Q - y * R) ^ 2) +
        6 * P * x * y * (x ^ 2 + y ^ 2) +
        6 * Q * x * z * (x ^ 2 + z ^ 2) +
        6 * R * y * z * (y ^ 2 + z ^ 2) := by
    dsimp [P, Q, R]
    ring
  linarith



theorem threeBridge_bernsteinOne_nonpos_of_bounds
    {a b c : Real} (ha0 : 0 <= a) (hb0 : 0 <= b)
    (hzero : a ^ 3 - 3 * a * b - a + 3 * c <= 0)
    (hdis : 0 <= 1 - a + b - c) (hpair : 2 * a <= 3 + b) :
    (2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b - 2 * a +
      b * c + 3 * c) / 2 <= 0 := by
  by_cases ha : a <= 1
  · have hsquare : a ^ 2 <= 1 := by nlinarith
    have hlast : 2 * a ^ 2 - 5 * b - 3 <= 0 := by nlinarith
    have htrip : a * (a - 1) * (a + 1) <= 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha0 (by linarith)) (by linarith)
    have hprod : 0 <=
        a * (a - 1) * (a + 1) * (2 * a ^ 2 - 5 * b - 3) := by
      exact mul_nonneg_of_nonpos_of_nonpos htrip hlast
    have hfactor : 0 <= 2 * a ^ 2 + b + 3 := by positivity
    have hmul := mul_nonpos_of_nonneg_of_nonpos hfactor hzero
    have hid :
        3 * (2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b -
            2 * a + b * c + 3 * c) =
          (2 * a ^ 2 + b + 3) *
              (a ^ 3 - 3 * a * b - a + 3 * c) -
            a * (a - 1) * (a + 1) *
              (2 * a ^ 2 - 5 * b - 3) := by ring
    have hnum :
        2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b -
          2 * a + b * c + 3 * c <= 0 := by nlinarith [hid]
    exact div_nonpos_of_nonpos_of_nonneg hnum (by norm_num)
  · have ha1 : 1 <= a := le_of_not_ge ha
    have hlast : 2 * a - b - 3 <= 0 := by linarith
    have hfirst :
        (a - 1) * (b + 1) * (2 * a - b - 3) <= 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (sub_nonneg.mpr ha1) (by positivity)) hlast
    have hfactor : 0 <= 2 * a ^ 2 + b + 3 := by positivity
    have hmul := mul_nonneg hfactor hdis
    have hid :
        2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b -
            2 * a + b * c + 3 * c =
          (a - 1) * (b + 1) * (2 * a - b - 3) -
            (2 * a ^ 2 + b + 3) * (1 - a + b - c) := by ring
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)



theorem threeBridge_two_sqsum_le_three_add_pairSqsum
    {x y z p q s : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (hp : x * y <= p) (hq : x * z <= q) (hs : y * z <= s) :
    2 * (x ^ 2 + y ^ 2 + z ^ 2) <=
      3 + (p ^ 2 + q ^ 2 + s ^ 2) := by
  have hxy : x ^ 2 * y ^ 2 <= p ^ 2 := by
    have := mul_self_le_mul_self (mul_nonneg hx0 hy0) hp
    nlinarith
  have hxz : x ^ 2 * z ^ 2 <= q ^ 2 := by
    have := mul_self_le_mul_self (mul_nonneg hx0 hz0) hq
    nlinarith
  have hyz : y ^ 2 * z ^ 2 <= s ^ 2 := by
    have := mul_self_le_mul_self (mul_nonneg hy0 hz0) hs
    nlinarith
  have hxSq : x ^ 2 <= 1 := by nlinarith
  have hySq : y ^ 2 <= 1 := by nlinarith
  have hzSq : z ^ 2 <= 1 := by nlinarith
  have hxyUnit : x ^ 2 + y ^ 2 <= 1 + x ^ 2 * y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxSq) (sub_nonneg.mpr hySq)]
  have hxzUnit : x ^ 2 + z ^ 2 <= 1 + x ^ 2 * z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxSq) (sub_nonneg.mpr hzSq)]
  have hyzUnit : y ^ 2 + z ^ 2 <= 1 + y ^ 2 * z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hySq) (sub_nonneg.mpr hzSq)]
  nlinarith



theorem threeBridge_bernsteinTwo_nonpos_of_bounds
    {a b c : Real} (ha0 : 0 <= a) (hb0 : 0 <= b) (hc0 : 0 <= c)
    (hb3 : b <= 3) (hc1 : c <= 1)
    (hzero : a ^ 3 - 3 * a * b - a + 3 * c <= 0)
    (hdis : 0 <= 1 - a + b - c) (hpair : 2 * a <= 3 + b) :
    -(a ^ 3 * b - 6 * a ^ 3 + 3 * a ^ 2 * b * c - 13 * a ^ 2 * c -
      a * b ^ 3 + 3 * a * b ^ 2 + 12 * a * b - 9 * a * c ^ 2 +
      6 * a + b ^ 2 * c + 3 * b * c) / 6 <= 0 := by
  let N : Real -> Real := fun t =>
    a ^ 3 * b - 6 * a ^ 3 + 3 * a ^ 2 * b * t - 13 * a ^ 2 * t -
      a * b ^ 3 + 3 * a * b ^ 2 + 12 * a * b - 9 * a * t ^ 2 +
      6 * a + b ^ 2 * t + 3 * b * t
  have hac : a <= b + 1 := by linarith
  have hN0 : 0 <= N 0 := by
    by_cases ha : a = 0
    · simp [N, ha]
    have hap : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    have hbase : a * (a ^ 2 - 3 * b - 1) <= 0 := by nlinarith
    have haSq : a ^ 2 <= 3 * b + 1 := by
      have := nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hbase) hap
      linarith
    let L := a ^ 2 * b - 6 * a ^ 2 - b ^ 3 + 3 * b ^ 2 + 12 * b + 6
    have hL : 0 <= L := by
      by_cases hb : b <= 1
      · have haSq' : a ^ 2 <= (b + 1) ^ 2 := by nlinarith
        have hcoef : b - 6 <= 0 := by linarith
        have hprod : 0 <= (b - 6) * (a ^ 2 - (b + 1) ^ 2) :=
          mul_nonneg_of_nonpos_of_nonpos hcoef (sub_nonpos.mpr haSq')
        have hend : 0 <= -b * (b - 1) :=
          mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hb0) (sub_nonpos.mpr hb)
        dsimp [L]
        nlinarith [show
          a ^ 2 * b - 6 * a ^ 2 - b ^ 3 + 3 * b ^ 2 + 12 * b + 6 =
            -b * (b - 1) + (b - 6) * (a ^ 2 - (b + 1) ^ 2) by ring]
      · have hb1 : 1 <= b := le_of_not_ge hb
        have hcoef : b - 6 <= 0 := by linarith
        have hprod : 0 <= (b - 6) * (a ^ 2 - (3 * b + 1)) :=
          mul_nonneg_of_nonpos_of_nonpos hcoef (sub_nonpos.mpr haSq)
        have hend : 0 <= -b * (b - 5) * (b - 1) := by
          exact mul_nonneg
            (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hb0) (by linarith))
            (sub_nonneg.mpr hb1)
        dsimp [L]
        nlinarith [show
          a ^ 2 * b - 6 * a ^ 2 - b ^ 3 + 3 * b ^ 2 + 12 * b + 6 =
            -b * (b - 5) * (b - 1) +
              (b - 6) * (a ^ 2 - (3 * b + 1)) by ring]
    have : N 0 = a * L := by dsimp [N, L]; ring
    rw [this]
    exact mul_nonneg ha0 hL
  have concavity (U : Real) (hU0 : 0 <= U) (hcU : c <= U)
      (hNU : 0 <= N U) : 0 <= N c := by
    by_cases hU : U = 0
    · have hc : c = 0 := le_antisymm (by simpa [hU] using hcU) hc0
      simpa [hc] using hN0
    have hUp : 0 < U := lt_of_le_of_ne hU0 (Ne.symm hU)
    have hcomb : 0 <= (U - c) * N 0 + c * N U +
        9 * a * c * (U - c) * U := by positivity
    have hid : U * N c = (U - c) * N 0 + c * N U +
        9 * a * c * (U - c) * U := by dsimp [N]; ring
    rw [← hid] at hcomb
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hcomb) hUp
  have hNc : 0 <= N c := by
    by_cases ha : a <= 1
    · let U := (a + 3 * a * b - a ^ 3) / 3
      have hcU : c <= U := by dsimp [U]; nlinarith
      have hU0 : 0 <= U := hc0.trans hcU
      let H := 3 * a ^ 4 - 15 * a ^ 2 * b - 16 * a ^ 2 +
        19 * b ^ 2 + 39 * b + 18
      have hH : 0 <= H := by
        have haSq : a ^ 2 <= 1 := by nlinarith
        have hfac1 : a ^ 2 - 1 <= 0 := sub_nonpos.mpr haSq
        have hfac2 : 3 * a ^ 2 - 15 * b - 13 <= 0 := by nlinarith
        have hp : 0 <= (a ^ 2 - 1) * (3 * a ^ 2 - 15 * b - 13) :=
          mul_nonneg_of_nonpos_of_nonpos hfac1 hfac2
        dsimp [H]
        nlinarith [show
          3 * a ^ 4 - 15 * a ^ 2 * b - 16 * a ^ 2 +
              19 * b ^ 2 + 39 * b + 18 =
            19 * b ^ 2 + 24 * b + 5 +
              (a ^ 2 - 1) * (3 * a ^ 2 - 15 * b - 13) by ring]
      have hNU : 0 <= N U := by
        have hpref : 0 <= -a * (a - 1) * (a + 1) := by
          exact mul_nonneg
            (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha0)
              (sub_nonpos.mpr ha)) (by linarith)
        have hid : 3 * N U = -a * (a - 1) * (a + 1) * H := by
          dsimp [N, U, H]
          ring
        nlinarith [mul_nonneg hpref hH]
      exact concavity U hU0 hcU hNU
    · have ha1 : 1 <= a := le_of_not_ge ha
      by_cases hab : a <= b
      ·
        let H := a ^ 2 * b - 6 * a ^ 2 + a * b ^ 2 - 3 * a * b -
          13 * a - b - 3
        have hbSq : b ^ 2 <= 3 * b := by nlinarith
        have hA2B : a ^ 2 * b <= 3 * a ^ 2 := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hb3 (sq_nonneg a)
        have hAB2 : a * b ^ 2 <= 3 * a * b := by
          nlinarith [mul_le_mul_of_nonneg_left hbSq ha0]
        have hH : H <= 0 := by dsimp [H]; nlinarith
        have hNU : 0 <= N 1 := by
          have hid : N 1 = (a - b) * H := by dsimp [N, H]; ring
          rw [hid]
          exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab) hH
        exact concavity 1 (by norm_num) hc1 hNU
      · have hba : b <= a := le_of_not_ge hab
        let U := 1 - a + b
        have hcU : c <= U := by dsimp [U]; linarith
        have hU0 : 0 <= U := hc0.trans hcU
        have hlast : 2 * a - b - 3 <= 0 := by linarith
        have hNU : 0 <= N U := by
          have hid : N U =
              -(a - 1) * (a - b) * (b + 1) * (2 * a - b - 3) := by
            dsimp [N, U]
            ring
          rw [hid]
          have hfirst : -(a - 1) * (a - b) * (b + 1) <= 0 := by
            exact mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr (sub_nonneg.mpr ha1)) (sub_nonneg.mpr hba))
              (by positivity)
          exact mul_nonneg_of_nonpos_of_nonpos hfirst hlast
        exact concavity U hU0 hcU hNU
  change -(N c) / 6 <= 0
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hNc) (by norm_num)



theorem threeBridge_pairTriangle_core
    {X Y Z : Real} (hX0 : 0 <= X) (hY0 : 0 <= Y) (hZ0 : 0 <= Z)
    (hXY : X * Y <= Z) (hXZ : X * Z <= Y) (hYZ : Y * Z <= X) :
    (X + Y + Z - 1) * (X * Y + X * Z + Y * Z) <=
      (X + Y + Z + 3) * (X * Y * Z) := by
  by_cases hX : X = 0
  · have hYZ0 : Y * Z = 0 := le_antisymm (by simpa [hX] using hYZ)
      (mul_nonneg hY0 hZ0)
    rcases mul_eq_zero.mp hYZ0 with hY | hZ
    · simp [hX, hY]
    · simp [hX, hZ]
  by_cases hY : Y = 0
  · have hXZ0 : X * Z = 0 := le_antisymm (by simpa [hY] using hXZ)
      (mul_nonneg hX0 hZ0)
    rcases mul_eq_zero.mp hXZ0 with hX' | hZ
    · exact (hX hX').elim
    · simp [hY, hZ]
  by_cases hZ : Z = 0
  · have hXY0 : X * Y = 0 := le_antisymm (by simpa [hZ] using hXY)
      (mul_nonneg hX0 hY0)
    rcases mul_eq_zero.mp hXY0 with hX' | hY'
    · exact (hX hX').elim
    · exact (hY hY').elim
  have hXp : 0 < X := lt_of_le_of_ne hX0 (Ne.symm hX)
  have hYp : 0 < Y := lt_of_le_of_ne hY0 (Ne.symm hY)
  have hZp : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZ)
  let u := Real.sqrt (X * Y / Z)
  let v := Real.sqrt (X * Z / Y)
  let w := Real.sqrt (Y * Z / X)
  have hu0 : 0 <= u := Real.sqrt_nonneg _
  have hv0 : 0 <= v := Real.sqrt_nonneg _
  have hw0 : 0 <= w := Real.sqrt_nonneg _
  have huSq : u ^ 2 = X * Y / Z := by
    exact Real.sq_sqrt (div_nonneg (mul_nonneg hX0 hY0) hZ0)
  have hvSq : v ^ 2 = X * Z / Y := by
    exact Real.sq_sqrt (div_nonneg (mul_nonneg hX0 hZ0) hY0)
  have hwSq : w ^ 2 = Y * Z / X := by
    exact Real.sq_sqrt (div_nonneg (mul_nonneg hY0 hZ0) hX0)
  have hu1 : u <= 1 := by
    have hdiv : X * Y / Z <= 1 := (div_le_one hZp).2 hXY
    nlinarith
  have hv1 : v <= 1 := by
    have hdiv : X * Z / Y <= 1 := (div_le_one hYp).2 hXZ
    nlinarith
  have hw1 : w <= 1 := by
    have hdiv : Y * Z / X <= 1 := (div_le_one hXp).2 hYZ
    nlinarith
  have huvSq : (u * v) ^ 2 = X ^ 2 := by
    rw [mul_pow, huSq, hvSq]
    field_simp [hY, hZ]
  have huwSq : (u * w) ^ 2 = Y ^ 2 := by
    rw [mul_pow, huSq, hwSq]
    field_simp [hX, hZ]
  have hvwSq : (v * w) ^ 2 = Z ^ 2 := by
    rw [mul_pow, hvSq, hwSq]
    field_simp [hX, hY]
  have huv : u * v = X := by nlinarith [mul_nonneg hu0 hv0]
  have huw : u * w = Y := by nlinarith [mul_nonneg hu0 hw0]
  have hvw : v * w = Z := by nlinarith [mul_nonneg hv0 hw0]
  have hcube := threeBridge_cube_inequality hu0 hu1 hv0 hv1 hw0 hw1
  have huvw : u * v * w >= 0 := mul_nonneg (mul_nonneg hu0 hv0) hw0
  have hmul := mul_le_mul_of_nonneg_left hcube huvw
  have hsum : u * v * w * (u + v + w) =
      X * Y + X * Z + Y * Z := by
    rw [← huv, ← huw, ← hvw]
    ring
  have hprod : u * v * w * (u * v * w) = X * Y * Z := by
    rw [← huv, ← huw, ← hvw]
    ring
  calc
    (X + Y + Z - 1) * (X * Y + X * Z + Y * Z) =
        u * v * w *
          ((u * v + u * w + v * w - 1) * (u + v + w)) := by
      rw [← hsum, ← huv, ← huw, ← hvw]
      ring
    _ <= u * v * w *
          (u * v * w * (u * v + u * w + v * w + 3)) := hmul
    _ = (X + Y + Z + 3) * (X * Y * Z) := by
      rw [← hprod, ← huv, ← huw, ← hvw]
      ring



theorem threeBridge_sum_mul_sum_le_one_add_c
    {u₁ u₂ u₃ X Y Z c : Real}
    (hu₁0 : 0 <= u₁) (hu₂0 : 0 <= u₂) (hu₃0 : 0 <= u₃)
    (hX0 : 0 <= X) (hY0 : 0 <= Y) (hZ0 : 0 <= Z)
    (hX1 : X <= 1) (hY1 : Y <= 1) (hZ1 : Z <= 1) (hc0 : 0 <= c)
    (hXY : X * Y <= Z) (hXZ : X * Z <= Y) (hYZ : Y * Z <= X)
    (hop₁ : u₁ * Z <= c) (hop₂ : u₂ * Y <= c)
    (hop₃ : u₃ * X <= c) :
    (u₁ + u₂ + u₃) * (X + Y + Z) <=
      (u₁ + u₂ + u₃) + c * (X + Y + Z) + 3 * c := by
  let a := u₁ + u₂ + u₃
  let b := X + Y + Z
  by_cases hb : b <= 1
  · have ha0 : 0 <= a := by dsimp [a]; positivity
    have hab : a * b <= a := by
      simpa using mul_le_mul_of_nonneg_left hb ha0
    dsimp [a, b] at hab ⊢
    nlinarith [mul_nonneg hc0 (add_nonneg (add_nonneg hX0 hY0) hZ0)]
  have hbpos : 0 < b - 1 := sub_pos.mpr (lt_of_not_ge hb)
  have hXpos : 0 < X := by
    by_contra h
    have hXe : X = 0 := le_antisymm (le_of_not_gt h) hX0
    have hYZ0 : Y * Z = 0 := le_antisymm (by simpa [hXe] using hYZ)
      (mul_nonneg hY0 hZ0)
    rcases mul_eq_zero.mp hYZ0 with hYe | hZe
    · dsimp [b] at hb
      nlinarith
    · dsimp [b] at hb
      nlinarith
  have hYpos : 0 < Y := by
    by_contra h
    have hYe : Y = 0 := le_antisymm (le_of_not_gt h) hY0
    have hXZ0 : X * Z = 0 := le_antisymm (by simpa [hYe] using hXZ)
      (mul_nonneg hX0 hZ0)
    rcases mul_eq_zero.mp hXZ0 with hXe | hZe
    · dsimp [b] at hb
      nlinarith
    · dsimp [b] at hb
      nlinarith
  have hZpos : 0 < Z := by
    by_contra h
    have hZe : Z = 0 := le_antisymm (le_of_not_gt h) hZ0
    have hXY0 : X * Y = 0 := le_antisymm (by simpa [hZe] using hXY)
      (mul_nonneg hX0 hY0)
    rcases mul_eq_zero.mp hXY0 with hXe | hYe
    · dsimp [b] at hb
      nlinarith
    · dsimp [b] at hb
      nlinarith
  have hp : 0 < X * Y * Z := mul_pos (mul_pos hXpos hYpos) hZpos
  have h₁ := mul_le_mul_of_nonneg_left hop₁ (mul_nonneg hX0 hY0)
  have h₂ := mul_le_mul_of_nonneg_left hop₂ (mul_nonneg hX0 hZ0)
  have h₃ := mul_le_mul_of_nonneg_left hop₃ (mul_nonneg hY0 hZ0)
  have haprod : a * (X * Y * Z) <=
      c * (X * Y + X * Z + Y * Z) := by
    dsimp [a]
    nlinarith [h₁, h₂, h₃]
  have hleft := mul_le_mul_of_nonneg_right haprod hbpos.le
  have hcore := threeBridge_pairTriangle_core hX0 hY0 hZ0 hXY hXZ hYZ
  have hright := mul_le_mul_of_nonneg_left hcore hc0
  have hcancel : a * (b - 1) <= c * (b + 3) := by
    apply le_of_mul_le_mul_right _ hp
    calc
      a * (b - 1) * (X * Y * Z) =
          a * (X * Y * Z) * (b - 1) := by ring
      _ <= c * (X * Y + X * Z + Y * Z) * (b - 1) := hleft
      _ = c * ((X + Y + Z - 1) * (X * Y + X * Z + Y * Z)) := by
        dsimp [b]
        ring
      _ <= c * ((X + Y + Z + 3) * (X * Y * Z)) := hright
      _ = c * (b + 3) * (X * Y * Z) := by dsimp [b]; ring
  dsimp [a, b] at hcancel ⊢
  linarith



theorem threeBridge_singleton_mul_opposite_sq_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 *
        (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2 <=
      (expJ G.edgeFinset J hf
        (fun s => spin s x * (spin s y * spin s z))) ^ 2 := by
  have hsymm : ({x} : Finset V) ∆ {y, z} = {x, y, z} := by
    ext w
    by_cases hwx : w = x <;> by_cases hwy : w = y <;>
      by_cases hwz : w = z <;>
      simp [Finset.mem_symmDiff, hwx, hwy, hwz, hxy, hxy.symm,
        hxz, hxz.symm, hyz, hyz.symm]
  have hpair : spinProd ({y, z} : Finset V) =
      (fun s => spin s y * spin s z) := spinProd_pair y z hyz
  have htriple : spinProd ({x, y, z} : Finset V) =
      (fun s => spin s x * (spin s y * spin s z)) := by
    funext s
    simp [spinProd, hxy, hxz, hyz]
  have hgks := gks_second_J G.edgeFinset J hf
    (fun e _ => hJ e) hhf ({x} : Finset V) ({y, z} : Finset V)
  rw [spinProd_singleton, hpair, hsymm, htriple] at hgks
  have hx0 : 0 <= expJ G.edgeFinset J hf (fun s => spin s x) := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x} : Finset V)
    simpa [spinProd_singleton] using h
  have hyz0 : 0 <= expJ G.edgeFinset J hf
      (fun s => spin s y * spin s z) := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({y, z} : Finset V)
    simpa [hpair] using h
  have hsquare := mul_self_le_mul_self (mul_nonneg hx0 hyz0) hgks
  convert hsquare using 1 <;> ring



theorem threeBridge_pair_mul_pair_sq_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2 *
        (expJ G.edgeFinset J hf (fun s => spin s x * spin s z)) ^ 2 <=
      (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2 := by
  have hsymm : ({x, y} : Finset V) ∆ {x, z} = {y, z} := by
    ext w
    by_cases hwx : w = x <;> by_cases hwy : w = y <;>
      by_cases hwz : w = z <;>
      simp [Finset.mem_symmDiff, hwx, hwy, hwz, hxy, hxy.symm,
        hxz, hxz.symm, hyz, hyz.symm]
  have hxyfun := spinProd_pair x y hxy
  have hxzfun := spinProd_pair x z hxz
  have hyzfun := spinProd_pair y z hyz
  have hgks := gks_second_J G.edgeFinset J hf
    (fun e _ => hJ e) hhf ({x, y} : Finset V) ({x, z} : Finset V)
  rw [hxyfun, hxzfun, hsymm, hyzfun] at hgks
  have hxy0 : 0 <= expJ G.edgeFinset J hf
      (fun s => spin s x * spin s y) := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x, y} : Finset V)
    simpa [hxyfun] using h
  have hxz0 : 0 <= expJ G.edgeFinset J hf
      (fun s => spin s x * spin s z) := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x, z} : Finset V)
    simpa [hxzfun] using h
  have hsquare := mul_self_le_mul_self (mul_nonneg hxy0 hxz0) hgks
  convert hsquare using 1 <;> ring



theorem threeBridge_ab_le_two_a_add_three_c
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threeBridgeOneCoeff G J hf x y z *
        threeBridgeTwoCoeff G J hf x y z <=
      2 * threeBridgeOneCoeff G J hf x y z +
        3 * threeBridgeThreeCoeff G J hf x y z := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let mz := expJ G.edgeFinset J hf (fun s => spin s z)
  let qxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let qxz := expJ G.edgeFinset J hf (fun s => spin s x * spin s z)
  let qyz := expJ G.edgeFinset J hf (fun s => spin s y * spin s z)
  let r := expJ G.edgeFinset J hf
    (fun s => spin s x * (spin s y * spin s z))
  have hqxy1 : qxy ^ 2 <= 1 := by
    have h := expJ_monomial_le_one G.edgeFinset J hf
      (fun s => spin s x * spin s y) (fun s => by
        rcases spin_eq_pm s x with hx | hx <;>
          rcases spin_eq_pm s y with hy | hy <;> simp [hx, hy])
    have h0 : 0 <= qxy := by
      have h' := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({x, y} : Finset V)
      simpa [qxy, spinProd_pair x y hxy] using h'
    change qxy <= 1 at h
    nlinarith
  have hqxz1 : qxz ^ 2 <= 1 := by
    have h := expJ_monomial_le_one G.edgeFinset J hf
      (fun s => spin s x * spin s z) (fun s => by
        rcases spin_eq_pm s x with hx | hx <;>
          rcases spin_eq_pm s z with hz | hz <;> simp [hx, hz])
    have h0 : 0 <= qxz := by
      have h' := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({x, z} : Finset V)
      simpa [qxz, spinProd_pair x z hxz] using h'
    change qxz <= 1 at h
    nlinarith
  have hqyz1 : qyz ^ 2 <= 1 := by
    have h := expJ_monomial_le_one G.edgeFinset J hf
      (fun s => spin s y * spin s z) (fun s => by
        rcases spin_eq_pm s y with hy | hy <;>
          rcases spin_eq_pm s z with hz | hz <;> simp [hy, hz])
    have h0 : 0 <= qyz := by
      have h' := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({y, z} : Finset V)
      simpa [qyz, spinProd_pair y z hyz] using h'
    change qyz <= 1 at h
    nlinarith
  have hopx : mx ^ 2 * qyz ^ 2 <= r ^ 2 := by
    simpa [mx, qyz, r] using threeBridge_singleton_mul_opposite_sq_le
      G J hf hJ hhf hxy hxz hyz
  have hopy : my ^ 2 * qxz ^ 2 <= r ^ 2 := by
    simpa [my, qxz, r, mul_assoc, mul_left_comm, mul_comm] using
      threeBridge_singleton_mul_opposite_sq_le
        G J hf hJ hhf hxy.symm hyz hxz
  have hopz : mz ^ 2 * qxy ^ 2 <= r ^ 2 := by
    simpa [mz, qxy, r, mul_assoc, mul_left_comm, mul_comm] using
      threeBridge_singleton_mul_opposite_sq_le
        G J hf hJ hhf hxz.symm hyz.symm hxy
  have h := threeBridge_sum_mul_sum_le_two_add_three
    (sq_nonneg mx) (sq_nonneg my) (sq_nonneg mz)
    hqxy1 hqxz1 hqyz1 hopx hopy hopz
  simpa [threeBridgeOneCoeff, threeBridgeTwoCoeff,
    threeBridgeThreeCoeff, mx, my, mz, qxy, qxz, qyz, r] using h



theorem threeBridge_ab_le_a_add_bc_add_three_c
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threeBridgeOneCoeff G J hf x y z *
        threeBridgeTwoCoeff G J hf x y z <=
      threeBridgeOneCoeff G J hf x y z +
        threeBridgeThreeCoeff G J hf x y z *
          threeBridgeTwoCoeff G J hf x y z +
        3 * threeBridgeThreeCoeff G J hf x y z := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let mz := expJ G.edgeFinset J hf (fun s => spin s z)
  let qxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let qxz := expJ G.edgeFinset J hf (fun s => spin s x * spin s z)
  let qyz := expJ G.edgeFinset J hf (fun s => spin s y * spin s z)
  let r := expJ G.edgeFinset J hf
    (fun s => spin s x * (spin s y * spin s z))
  have pair_data (i j : V) (hij : i ≠ j) :
      0 <= (expJ G.edgeFinset J hf (fun s => spin s i * spin s j)) ^ 2 ∧
      (expJ G.edgeFinset J hf (fun s => spin s i * spin s j)) ^ 2 <= 1 := by
    constructor
    · exact sq_nonneg _
    · have h := expJ_monomial_le_one G.edgeFinset J hf
        (fun s => spin s i * spin s j) (fun s => by
          rcases spin_eq_pm s i with hi | hi <;>
            rcases spin_eq_pm s j with hj | hj <;> simp [hi, hj])
      have h0 : 0 <= expJ G.edgeFinset J hf
          (fun s => spin s i * spin s j) := by
        have h' := ghsvp_expJ_nonneg G.edgeFinset J hf
          (fun e _ => hJ e) hhf ({i, j} : Finset V)
        simpa [spinProd_pair i j hij] using h'
      nlinarith
  obtain ⟨hX0, hX1⟩ := pair_data x y hxy
  obtain ⟨hY0, hY1⟩ := pair_data x z hxz
  obtain ⟨hZ0, hZ1⟩ := pair_data y z hyz
  have hXY : qxy ^ 2 * qxz ^ 2 <= qyz ^ 2 := by
    simpa [qxy, qxz, qyz] using threeBridge_pair_mul_pair_sq_le
      G J hf hJ hhf hxy hxz hyz
  have hXZ : qxy ^ 2 * qyz ^ 2 <= qxz ^ 2 := by
    simpa [qxy, qxz, qyz, mul_comm] using threeBridge_pair_mul_pair_sq_le
      G J hf hJ hhf hxy.symm hyz hxz
  have hYZ : qxz ^ 2 * qyz ^ 2 <= qxy ^ 2 := by
    simpa [qxy, qxz, qyz, mul_comm] using threeBridge_pair_mul_pair_sq_le
      G J hf hJ hhf hxz.symm hyz.symm hxy
  have hopx : mx ^ 2 * qyz ^ 2 <= r ^ 2 := by
    simpa [mx, qyz, r] using threeBridge_singleton_mul_opposite_sq_le
      G J hf hJ hhf hxy hxz hyz
  have hopy : my ^ 2 * qxz ^ 2 <= r ^ 2 := by
    simpa [my, qxz, r, mul_assoc, mul_left_comm, mul_comm] using
      threeBridge_singleton_mul_opposite_sq_le
        G J hf hJ hhf hxy.symm hyz hxz
  have hopz : mz ^ 2 * qxy ^ 2 <= r ^ 2 := by
    simpa [mz, qxy, r, mul_assoc, mul_left_comm, mul_comm] using
      threeBridge_singleton_mul_opposite_sq_le
        G J hf hJ hhf hxz.symm hyz.symm hxy
  have h := threeBridge_sum_mul_sum_le_one_add_c
    (sq_nonneg mx) (sq_nonneg my) (sq_nonneg mz)
    hX0 hY0 hZ0 hX1 hY1 hZ1 (sq_nonneg r)
    hXY hXZ hYZ hopx hopy hopz
  simpa [threeBridgeOneCoeff, threeBridgeTwoCoeff,
    threeBridgeThreeCoeff, mx, my, mz, qxy, qxz, qyz, r,
    mul_assoc, mul_left_comm, mul_comm] using h



theorem threeBridgeVarianceSkewBernsteinCoeff_zero_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threeBridgeVarianceSkewBernsteinCoeff
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) 0 <= 0 := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let mz := expJ G.edgeFinset J hf (fun s => spin s z)
  let qxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let qxz := expJ G.edgeFinset J hf (fun s => spin s x * spin s z)
  let qyz := expJ G.edgeFinset J hf (fun s => spin s y * spin s z)
  let r := expJ G.edgeFinset J hf
    (fun s => spin s x * (spin s y * spin s z))
  have single_data (i : V) :
      0 <= expJ G.edgeFinset J hf (fun s => spin s i) ∧
      expJ G.edgeFinset J hf (fun s => spin s i) <= 1 := by
    constructor
    · have h := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({i} : Finset V)
      simpa [spinProd_singleton] using h
    · exact expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
        rcases spin_eq_pm s i with hi | hi <;> simp [hi])
  obtain ⟨hmx0, hmx1⟩ := single_data x
  obtain ⟨hmy0, hmy1⟩ := single_data y
  obtain ⟨hmz0, hmz1⟩ := single_data z
  have hr0 : 0 <= r := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x, y, z} : Finset V)
    rw [show spinProd ({x, y, z} : Finset V) =
        (fun s => spin s x * (spin s y * spin s z)) by
      funext s
      simp [spinProd, hxy, hxz, hyz]] at h
    exact h
  have hp : mx * my <= qxy := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x} : Finset V) ({y} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x y hxy, spinProd_pair x y hxy] at h
    simpa [mx, my, qxy] using h
  have hq : mx * mz <= qxz := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x} : Finset V) ({z} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x z hxz, spinProd_pair x z hxz] at h
    simpa [mx, mz, qxz] using h
  have hs : my * mz <= qyz := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({y} : Finset V) ({z} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair y z hyz, spinProd_pair y z hyz] at h
    simpa [my, mz, qyz] using h
  have hraw := grahamInhomThreePoint_le G J hf hJ hhf x y z
  change r <= mx * qyz + qxy * mz + qxz * my -
      2 * mx * my * mz -
      2 * (qxz - mx * mz) * (qyz - my * mz) * mz at hraw
  have hcovxz : 0 <= qxz - mx * mz := sub_nonneg.mpr hq
  have hcovyz : 0 <= qyz - my * mz := sub_nonneg.mpr hs
  have hcorrection : 0 <=
      2 * (qxz - mx * mz) * (qyz - my * mz) * mz := by positivity
  let U := mx * qyz + my * qxz + mz * qxy - 2 * mx * my * mz
  have hrU : r <= U := by dsimp [U]; nlinarith
  have hU0 : 0 <= U := hr0.trans hrU
  have hrsq : r ^ 2 <= U ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hr0 hrU
  have hbound := threeBridge_ghsSquare_le_firstBound
    hmx0 hmy0 hmz0 hmx1 hmy1 hmz1 hp hq hs
  change 3 * U ^ 2 <=
      (mx ^ 2 + my ^ 2 + mz ^ 2) +
        3 * (mx ^ 2 + my ^ 2 + mz ^ 2) *
          (qxy ^ 2 + qxz ^ 2 + qyz ^ 2) -
        (mx ^ 2 + my ^ 2 + mz ^ 2) ^ 3 at hbound
  change (mx ^ 2 + my ^ 2 + mz ^ 2) ^ 3 -
      3 * (mx ^ 2 + my ^ 2 + mz ^ 2) *
        (qxy ^ 2 + qxz ^ 2 + qyz ^ 2) -
      (mx ^ 2 + my ^ 2 + mz ^ 2) + 3 * r ^ 2 <= 0
  nlinarith



theorem threeBridgeVarianceSkewBernsteinCoeff_one_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threeBridgeVarianceSkewBernsteinCoeff
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) 1 <= 0 := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let mz := expJ G.edgeFinset J hf (fun s => spin s z)
  let qxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let qxz := expJ G.edgeFinset J hf (fun s => spin s x * spin s z)
  let qyz := expJ G.edgeFinset J hf (fun s => spin s y * spin s z)
  let a := mx ^ 2 + my ^ 2 + mz ^ 2
  let b := qxy ^ 2 + qxz ^ 2 + qyz ^ 2
  let c := (expJ G.edgeFinset J hf
    (fun s => spin s x * (spin s y * spin s z))) ^ 2
  have single_data (i : V) :
      0 <= expJ G.edgeFinset J hf (fun s => spin s i) ∧
      expJ G.edgeFinset J hf (fun s => spin s i) <= 1 := by
    constructor
    · have h := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({i} : Finset V)
      simpa [spinProd_singleton] using h
    · exact expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
        rcases spin_eq_pm s i with hi | hi <;> simp [hi])
  have pair_nonneg (i j : V) (hij : i ≠ j) :
      0 <= expJ G.edgeFinset J hf (fun s => spin s i * spin s j) := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({i, j} : Finset V)
    simpa [spinProd_pair i j hij] using h
  obtain ⟨hmx0, hmx1⟩ := single_data x
  obtain ⟨hmy0, hmy1⟩ := single_data y
  obtain ⟨hmz0, hmz1⟩ := single_data z
  have hqxy0 := pair_nonneg x y hxy
  have hqxz0 := pair_nonneg x z hxz
  have hqyz0 := pair_nonneg y z hyz
  have hp : mx * my <= qxy := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x} : Finset V) ({y} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x y hxy, spinProd_pair x y hxy] at h
    simpa [mx, my, qxy] using h
  have hq : mx * mz <= qxz := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x} : Finset V) ({z} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x z hxz, spinProd_pair x z hxz] at h
    simpa [mx, mz, qxz] using h
  have hs : my * mz <= qyz := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({y} : Finset V) ({z} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair y z hyz, spinProd_pair y z hyz] at h
    simpa [my, mz, qyz] using h
  have hpair : 2 * a <= 3 + b := by
    simpa [a, b, mx, my, mz, qxy, qxz, qyz] using
      threeBridge_two_sqsum_le_three_add_pairSqsum
        hmx0 hmy0 hmz0 hmx1 hmy1 hmz1 hp hq hs
  have hzero := threeBridgeVarianceSkewBernsteinCoeff_zero_nonpos
    G J hf hJ hhf hxy hxz hyz
  change a ^ 3 - 3 * a * b - a + 3 * c <= 0 at hzero
  have hdis : 0 <= 1 - a + b - c := by
    simpa [a, b, c, threeBridgeOneCoeff, threeBridgeTwoCoeff,
      threeBridgeThreeCoeff, mx, my, mz, qxy, qxz, qyz] using
      threeBridge_allDisagreementCoefficient_nonneg G J hf x y z
  have ha0 : 0 <= a := by dsimp [a]; positivity
  have hb0 : 0 <= b := by dsimp [b]; positivity
  change (2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b -
    2 * a + b * c + 3 * c) / 2 <= 0
  exact threeBridge_bernsteinOne_nonpos_of_bounds
    ha0 hb0 hzero hdis hpair


theorem threeBridgeVarianceSkewBernsteinCoeff_two_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threeBridgeVarianceSkewBernsteinCoeff
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) 2 <= 0 := by
  let mx := expJ G.edgeFinset J hf (fun s => spin s x)
  let my := expJ G.edgeFinset J hf (fun s => spin s y)
  let mz := expJ G.edgeFinset J hf (fun s => spin s z)
  let qxy := expJ G.edgeFinset J hf (fun s => spin s x * spin s y)
  let qxz := expJ G.edgeFinset J hf (fun s => spin s x * spin s z)
  let qyz := expJ G.edgeFinset J hf (fun s => spin s y * spin s z)
  let r := expJ G.edgeFinset J hf
    (fun s => spin s x * (spin s y * spin s z))
  let a := mx ^ 2 + my ^ 2 + mz ^ 2
  let b := qxy ^ 2 + qxz ^ 2 + qyz ^ 2
  let c := r ^ 2
  have single_data (i : V) :
      0 <= expJ G.edgeFinset J hf (fun s => spin s i) ∧
      expJ G.edgeFinset J hf (fun s => spin s i) <= 1 := by
    constructor
    · have h := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({i} : Finset V)
      simpa [spinProd_singleton] using h
    · exact expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
        rcases spin_eq_pm s i with hi | hi <;> simp [hi])
  have pair_data (i j : V) (hij : i ≠ j) :
      0 <= expJ G.edgeFinset J hf (fun s => spin s i * spin s j) ∧
      expJ G.edgeFinset J hf (fun s => spin s i * spin s j) <= 1 := by
    constructor
    · have h := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({i, j} : Finset V)
      simpa [spinProd_pair i j hij] using h
    · exact expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
        rcases spin_eq_pm s i with hi | hi <;>
          rcases spin_eq_pm s j with hj | hj <;> simp [hi, hj])
  obtain ⟨hmx0, hmx1⟩ := single_data x
  obtain ⟨hmy0, hmy1⟩ := single_data y
  obtain ⟨hmz0, hmz1⟩ := single_data z
  obtain ⟨hqxy0, hqxy1⟩ := pair_data x y hxy
  obtain ⟨hqxz0, hqxz1⟩ := pair_data x z hxz
  obtain ⟨hqyz0, hqyz1⟩ := pair_data y z hyz
  have hr0 : 0 <= r := by
    have h := ghsvp_expJ_nonneg G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x, y, z} : Finset V)
    rw [show spinProd ({x, y, z} : Finset V) =
        (fun s => spin s x * (spin s y * spin s z)) by
      funext s
      simp [spinProd, hxy, hxz, hyz]] at h
    exact h
  have hr1 : r <= 1 := expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
    rcases spin_eq_pm s x with hx | hx <;>
      rcases spin_eq_pm s y with hy | hy <;>
        rcases spin_eq_pm s z with hz | hz <;> simp [hx, hy, hz])
  have hp : mx * my <= qxy := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x} : Finset V) ({y} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x y hxy, spinProd_pair x y hxy] at h
    simpa [mx, my, qxy] using h
  have hq : mx * mz <= qxz := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({x} : Finset V) ({z} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair x z hxz, spinProd_pair x z hxz] at h
    simpa [mx, mz, qxz] using h
  have hs : my * mz <= qyz := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({y} : Finset V) ({z} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair y z hyz, spinProd_pair y z hyz] at h
    simpa [my, mz, qyz] using h
  have hpair : 2 * a <= 3 + b := by
    simpa [a, b, mx, my, mz, qxy, qxz, qyz] using
      threeBridge_two_sqsum_le_three_add_pairSqsum
        hmx0 hmy0 hmz0 hmx1 hmy1 hmz1 hp hq hs
  have hzero := threeBridgeVarianceSkewBernsteinCoeff_zero_nonpos
    G J hf hJ hhf hxy hxz hyz
  change a ^ 3 - 3 * a * b - a + 3 * c <= 0 at hzero
  have hdis : 0 <= 1 - a + b - c := by
    simpa [a, b, c, threeBridgeOneCoeff, threeBridgeTwoCoeff,
      threeBridgeThreeCoeff, mx, my, mz, qxy, qxz, qyz, r] using
      threeBridge_allDisagreementCoefficient_nonneg G J hf x y z
  have ha0 : 0 <= a := by dsimp [a]; positivity
  have hb0 : 0 <= b := by dsimp [b]; positivity
  have hc0 : 0 <= c := by dsimp [c]; positivity
  have hb3 : b <= 3 := by
    have hxySq : qxy ^ 2 <= 1 := by nlinarith
    have hxzSq : qxz ^ 2 <= 1 := by nlinarith
    have hyzSq : qyz ^ 2 <= 1 := by nlinarith
    dsimp [b]
    linarith
  have hc1 : c <= 1 := by dsimp [c]; nlinarith
  change -(a ^ 3 * b - 6 * a ^ 3 + 3 * a ^ 2 * b * c -
    13 * a ^ 2 * c - a * b ^ 3 + 3 * a * b ^ 2 + 12 * a * b -
    9 * a * c ^ 2 + 6 * a + b ^ 2 * c + 3 * b * c) / 6 <= 0
  exact threeBridge_bernsteinTwo_nonpos_of_bounds
    ha0 hb0 hc0 hb3 hc1 hzero hdis hpair




theorem threeBridgeVarianceSkewBernsteinCoeff_three_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threeBridgeVarianceSkewBernsteinCoeff
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) 3 <= 0 := by
  let a := threeBridgeOneCoeff G J hf x y z
  let b := threeBridgeTwoCoeff G J hf x y z
  let c := threeBridgeThreeCoeff G J hf x y z
  have hab : a * b <= 2 * a + 3 * c := by
    simpa [a, b, c] using threeBridge_ab_le_two_a_add_three_c
      G J hf hJ hhf hxy hxz hyz
  have hD : 0 <= 1 - a + b - c := by
    simpa [a, b, c] using
      threeBridge_allDisagreementCoefficient_nonneg G J hf x y z
  have hsum : 0 <= a + b + c + 1 := by
    dsimp [a, b, c, threeBridgeOneCoeff, threeBridgeTwoCoeff,
      threeBridgeThreeCoeff]
    positivity
  change -(a * b - 2 * a - 3 * c) * (a - b + c - 1) *
      (a + b + c + 1) / 2 <= 0
  have hfirst : a * b - 2 * a - 3 * c <= 0 := by linarith
  have hsecond : a - b + c - 1 <= 0 := by linarith
  have hprod : 0 <=
      (a * b - 2 * a - 3 * c) * (a - b + c - 1) :=
    mul_nonneg_of_nonpos_of_nonpos hfirst hsecond
  have hnum :
      -(a * b - 2 * a - 3 * c) * (a - b + c - 1) *
          (a + b + c + 1) <= 0 := by
    rw [show -(a * b - 2 * a - 3 * c) * (a - b + c - 1) *
        (a + b + c + 1) =
      -((a * b - 2 * a - 3 * c) * (a - b + c - 1) *
        (a + b + c + 1)) by ring]
    exact neg_nonpos.mpr (mul_nonneg hprod hsum)
  exact div_nonpos_of_nonpos_of_nonneg hnum (by norm_num)




theorem threeBridgeVarianceSkewBernsteinCoeff_four_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threeBridgeVarianceSkewBernsteinCoeff
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) 4 <= 0 := by
  let a := threeBridgeOneCoeff G J hf x y z
  let b := threeBridgeTwoCoeff G J hf x y z
  let c := threeBridgeThreeCoeff G J hf x y z
  have hab : a * b <= a + b * c + 3 * c := by
    simpa [a, b, c, mul_comm] using
      threeBridge_ab_le_a_add_bc_add_three_c
        G J hf hJ hhf hxy hxz hyz
  have hD : 0 <= 1 - a + b - c := by
    simpa [a, b, c] using
      threeBridge_allDisagreementCoefficient_nonneg G J hf x y z
  have hsum : 0 <= a + b + c + 1 := by
    dsimp [a, b, c, threeBridgeOneCoeff, threeBridgeTwoCoeff,
      threeBridgeThreeCoeff]
    positivity
  change -(a - b + c - 1) * (a + b + c + 1) *
      (a * b - a - b * c - 3 * c) <= 0
  have hfirst : a - b + c - 1 <= 0 := by linarith
  have hthird : a * b - a - b * c - 3 * c <= 0 := by linarith
  have hnegprod : (a - b + c - 1) * (a + b + c + 1) <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg hfirst hsum
  have hprod : 0 <=
      (a - b + c - 1) * (a + b + c + 1) *
        (a * b - a - b * c - 3 * c) :=
    mul_nonneg_of_nonpos_of_nonpos hnegprod hthird
  rw [show -(a - b + c - 1) * (a + b + c + 1) *
      (a * b - a - b * c - 3 * c) =
    -((a - b + c - 1) * (a + b + c + 1) *
      (a * b - a - b * c - 3 * c)) by ring]
  exact neg_nonpos.mpr hprod


theorem threeBridgeVarianceSkewBernsteinCoeff_all_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (i : Fin 5) :
    threeBridgeVarianceSkewBernsteinCoeff
        (threeBridgeOneCoeff G J hf x y z)
        (threeBridgeTwoCoeff G J hf x y z)
        (threeBridgeThreeCoeff G J hf x y z) i <= 0 := by
  fin_cases i
  · exact threeBridgeVarianceSkewBernsteinCoeff_zero_nonpos
      G J hf hJ hhf hxy hxz hyz
  · exact threeBridgeVarianceSkewBernsteinCoeff_one_nonpos
      G J hf hJ hhf hxy hxz hyz
  · exact threeBridgeVarianceSkewBernsteinCoeff_two_nonpos
      G J hf hJ hhf hxy hxz hyz
  · exact threeBridgeVarianceSkewBernsteinCoeff_three_nonpos
      G J hf hJ hhf hxy hxz hyz
  · exact threeBridgeVarianceSkewBernsteinCoeff_four_nonpos
      G J hf hJ hhf hxy hxz hyz


theorem replicaBridgeVariance_threeBridgeSites_le_neg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (r : Real) (hr : 0 <= r) :
    replicaBridgeVariance G J hf (threeBridgeSites x y z) r <=
      replicaBridgeVariance G J hf (threeBridgeSites x y z) (-r) := by
  by_cases hre : r = 0
  · simp [hre]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hre)
  apply (replicaBridgeVariance_threeBridgeSites_le_neg_iff_skew
    G J hf x y z hrp).2
  apply threeBridgeVarianceSkewPolynomial_nonpos_of_bernstein
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos r).le
  · exact (Real.tanh_lt_one r).le
  · exact threeBridgeVarianceSkewBernsteinCoeff_all_nonpos
      G J hf hJ hhf hxy hxz hyz


theorem replicaBridgeFreeEnergy_threeBridgeSites_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (r : Real) (hr : 0 <= r) :
    replicaBridgeFreeEnergy G J hf (threeBridgeSites x y z) r <=
      2 * r * threeBridgeOneCoeff G J hf x y z := by
  have h := replicaBridgeFreeEnergy_le_of_variance_order G J hf
    (threeBridgeSites x y z) r hr (fun t ht =>
      replicaBridgeVariance_threeBridgeSites_le_neg
        G J hf hJ hhf hxy hxz hyz t ht)
  simpa [threeBridgeSites, threeBridgeOneCoeff, Fin.sum_univ_succ,
    add_assoc] using h

end

end StatMech.Ising
