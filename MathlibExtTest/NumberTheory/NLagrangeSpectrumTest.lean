/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.NLagrangeSpectrum

-- At `k = 1` for `ξ = √2`, the convergent is `1`, the complete quotient is
-- `√2 + 1`, the reversed prefix is empty, and the identity of
-- `MetaMathlibExt.convergent_quality_and_lagrange_limsup` reads
-- `-1 / (1 - √2) = √2 + 1`.
example : (-1 : ℝ) ^ 1 / (((Real.sqrt 2).convergent 0).den ^ 2 *
    (((Real.sqrt 2).convergent 0 : ℝ) - Real.sqrt 2)) = Real.sqrt 2 + 1 := by
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have h := (MetaMathlibExt.convergent_quality_and_lagrange_limsup _ hirr).1 1 (by norm_num)
  have h1lt : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2lt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hfloor : ⌊Real.sqrt 2⌋ = 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨by exact_mod_cast h1lt.le, by norm_num [Real.sqrt_lt']⟩
  have hconv : (Real.sqrt 2).convergent 0 = 1 := by
    rw [Real.convergent_zero, hfloor]
    norm_cast
  rw [hconv] at h
  dsimp only at h
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfract : Int.fract (Real.sqrt 2) = Real.sqrt 2 - 1 := by
    rw [← Int.self_sub_floor, hfloor]
    norm_num
  have hcq1 : (fun x : ℝ => (Int.fract x)⁻¹)^[1] (Real.sqrt 2) = Real.sqrt 2 + 1 := by
    simp only [Function.iterate_one]
    rw [hfract]
    exact inv_eq_of_mul_eq_one_left (by nlinarith [hsq])
  rw [hconv]
  simp only [Rat.den_one, Rat.cast_one] at h
  simp only [Rat.den_one, Rat.cast_one]
  rw [hcq1] at h
  simp at h
  rw [hfloor, hfract] at h
  linear_combination h

-- At √3 the first three digits are 1, 1, 2. The reversed prefix [0; 2, 1] contributes 1/3.
example :
    let x := Real.sqrt 3
    let q := x.convergent 2
    q = 5 / 3 ∧ (-1 : ℝ) ^ 3 / ((q.den : ℝ) ^ 2 * ((q : ℝ) - x)) = (3 * x + 5) / 6 := by
  let x := Real.sqrt 3
  let y := (x + 1) / 2
  have hirr : Irrational x := Nat.prime_three.irrational_sqrt
  have hsq : x ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlo : 1 < x := by norm_num [x, Real.lt_sqrt]
  have hhi : x < 2 := by norm_num [x, Real.sqrt_lt']
  have hx : ⌊x⌋ = 1 := Int.floor_eq_iff.mpr (by norm_num; exact ⟨hlo.le, hhi⟩)
  have hy : ⌊y⌋ = 1 := Int.floor_eq_iff.mpr (by dsimp [y]; constructor <;> linarith)
  have hxy : (Int.fract x)⁻¹ = y := by
    apply inv_eq_of_mul_eq_one_left
    rw [← Int.self_sub_floor, hx]
    dsimp [y]
    push_cast
    nlinarith
  have hyx : (Int.fract y)⁻¹ = x + 1 := by
    apply inv_eq_of_mul_eq_one_left
    rw [← Int.self_sub_floor, hy]
    dsimp [y]
    push_cast
    nlinarith
  constructor
  · change x.convergent 2 = 5 / 3
    rw [Real.convergent_succ, hx, hxy, Real.convergent_succ, hy, hyx, Real.convergent_zero,
      Int.floor_add_one, hx]
    norm_num
  · let step := fun z : ℝ => (Int.fract z)⁻¹
    calc
      _ = (⌊step (step (step x))⌋ : ℝ) +
          1 / ((⌊step (step x)⌋ : ℝ) + 1 / ((⌊step x⌋ : ℝ) + 0)) +
          Int.fract (step (step (step x))) :=
        (MetaMathlibExt.convergent_quality_and_lagrange_limsup x hirr).1 3 (by decide)
      _ = y + 1 / 3 := by
        simp only [step, hxy, hyx, Int.fract_add_one, Int.floor_add_one, hx, hy]
        rw [← Int.self_sub_floor, hy]
        push_cast
        ring
      _ = (3 * x + 5) / 6 := by dsimp [y]; ring

-- The limsup clause specializes to the complete-quotient cuts for √2.
example :
    let x := Real.sqrt 2
    let cq := fun k : ℕ => (fun z : ℝ => (Int.fract z)⁻¹)^[k] x
    let digit := fun k => ⌊cq k⌋
    let rev := fun k : ℕ => ((List.range (k - 1)).reverse.map (fun i => digit (i + 1))).foldr
      (fun b acc => 1 / ((b : ℝ) + acc)) 0
    MetaMathlibExt.nLagrangeApproximability 1 x =
      Filter.limsup (fun k => ((digit k + rev k + Int.fract (cq k) : ℝ) : EReal)) Filter.atTop :=
  (MetaMathlibExt.convergent_quality_and_lagrange_limsup _ irrational_sqrt_two).2
