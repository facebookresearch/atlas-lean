/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.FiniteGroupYoung
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExt.Analysis.Fourier.FiniteGroupYoungTests

/-- Convolution with `0` on either side is `0`. -/
example (g : ZMod 4 → ℂ) : finGroupConv 0 g = 0 := finGroupConv_zero_left g

example (f : ZMod 4 → ℂ) : finGroupConv f 0 = 0 := finGroupConv_zero_right f

/-- Convolution on a finite abelian group is commutative and associative. -/
example (f g : ZMod 4 → ℂ) : finGroupConv f g = finGroupConv g f :=
  finGroupConv_comm f g

example (f g h : ZMod 4 → ℂ) :
    finGroupConv (finGroupConv f g) h = finGroupConv f (finGroupConv g h) :=
  finGroupConv_assoc f g h

/-- The delta function at `0` is the identity for convolution. -/
example (g : ZMod 4 → ℂ) :
    finGroupConv (fun y => if y = 0 then (1 : ℂ) else 0) g = g :=
  finGroupConv_delta_left g

/-- Young's inequality, instantiated on `ZMod 3` with `p = q = 3 / 2`, `r = 3`. -/
example (f g : ZMod 3 → ℂ) :
    (∑ x, ‖finGroupConv f g x‖ ^ (3 : ℝ)) ^ (1 / 3 : ℝ)
      ≤ (∑ x, ‖f x‖ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) *
        (∑ x, ‖g x‖ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) :=
  young_convolution_finite_group (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Sharpness: for the constant function `1` on `ZMod 2` with
`p = q = 4 / 3`, `r = 2`, Young's inequality is an equality: both sides are
`2 ^ (3 / 2)`. -/
example :
    (∑ x : ZMod 2, ‖finGroupConv (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) x‖ ^ (2 : ℝ)) ^
        (1 / 2 : ℝ)
      = (∑ _x : ZMod 2, ‖(1 : ℂ)‖ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) *
        (∑ _x : ZMod 2, ‖(1 : ℂ)‖ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) := by
  have hconv : ∀ x : ZMod 2,
      finGroupConv (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) x = 2 := by
    intro x
    rw [finGroupConv_apply]
    simp
  have hnorm1 : ‖(1 : ℂ)‖ = 1 := norm_one
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    norm_num
  have hL : (∑ x : ZMod 2,
        ‖finGroupConv (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Finset.sum_congr rfl fun x _ => by rw [hconv x]]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card 2, hnorm2]
    rw [show (2 : ℕ) • ((2 : ℝ) ^ (2 : ℝ)) = (8 : ℝ) by
      rw [nsmul_eq_mul]
      norm_num]
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
  have hR : (∑ _x : ZMod 2, ‖(1 : ℂ)‖ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) =
      (2 : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card 2, hnorm1, Real.one_rpow]
    rw [show (2 : ℕ) • (1 : ℝ) = (2 : ℝ) by rw [nsmul_eq_mul]; norm_num]
    congr 1
    norm_num
  rw [hL, hR]
  rw [← Real.rpow_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  congr 1
  norm_num

end MathlibExt.Analysis.Fourier.FiniteGroupYoungTests
