/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField

/-!
# A lower bound for the naive height of a rational point on an elliptic curve

The affine coordinates have absolute value at most the projective height of `(u : v : 1)`.
Solving the curve equation for the constant coefficient then bounds the coefficient norm
in terms of the linear coefficient and the cube of the height.
-/

namespace MetaMathlibExt

private theorem abs_coord_le_naiveHeight (u v : ℚ) (i : Fin 3) :
    |((![u, v, 1] i : ℚ) : ℝ)| ≤ Height.mulHeight ![u, v, 1] := by
  let x : Fin 3 → ℚ := ![u, v, 1]
  let q := x i
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  calc
    |(q : ℝ)| ≤ |(q.num : ℝ)| := by
      rw [Rat.cast_def, abs_div, abs_of_nonneg (Nat.cast_nonneg q.den : (0 : ℝ) ≤ q.den)]
      exact div_le_self (abs_nonneg _) hden
    _ ≤ Height.mulHeight₁ q := by
      rw [Rat.mulHeight₁_eq_max, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
      exact le_max_left _ _
    _ = Height.mulHeight (x ∘ ![i, 2]) := by
      rw [Height.mulHeight₁_eq_mulHeight]
      exact congrArg Height.mulHeight (List.ofFn_inj.mp rfl)
    _ ≤ Height.mulHeight x := Height.mulHeight_comp_le _ _

private theorem coeffNorm_le_of_curve_eq {a b u v H : ℝ} (hH : 1 ≤ H)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hP : v ^ 2 = u ^ 3 + a * u + b) :
    Real.sqrt (2 + a ^ 2 + b ^ 2) ≤ (4 + 2 * |a|) * H ^ 3 := by
  have hH₃ : H ≤ H ^ 3 := le_self_pow₀ hH (by decide)
  have hb : |b| ≤ (2 + |a|) * H ^ 3 := calc
    |b| = |v ^ 2 - u ^ 3 - a * u| := by rw [hP]; ring_nf
    _ ≤ |v ^ 2| + |u ^ 3| + |a * u| :=
      (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ H ^ 2 + H ^ 3 + |a| * H := by
      simp only [abs_pow, abs_mul]
      gcongr
    _ ≤ H ^ 3 + H ^ 3 + |a| * H ^ 3 := by
      have : H ^ 2 ≤ H ^ 3 := pow_le_pow_right₀ hH (by decide : 2 ≤ 3)
      gcongr
    _ = (2 + |a|) * H ^ 3 := by ring
  calc
    Real.sqrt (2 + a ^ 2 + b ^ 2) ≤ 2 + |a| + |b| := by
      apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith only [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
        mul_nonneg (abs_nonneg a) (abs_nonneg b)]
    _ ≤ (2 + |a|) * H ^ 3 + (2 + |a|) * H ^ 3 :=
      add_le_add (le_mul_of_one_le_right (by positivity) (hH.trans hH₃)) hb
    _ = (4 + 2 * |a|) * H ^ 3 := by ring

set_option linter.unusedVariables false in
/-- **Height lower bound on $y^2 = x^3 + ax + b$ when $|a|$ is small.** Let $a, b \in \mathbb{Z}$
with $ab \ne 0$ and $4a^3 + 27b^2 \ne 0$, let $\lVert p \rVert = \sqrt{2 + a^2 + b^2}$, and suppose
$1 + |a| < \lVert p \rVert^{1/2}/1.782$. For $u, v \in \mathbb{Q}$ let
$H(u, v) = \max(|U|, |V|, |W|)$, where $U, V, W$ are coprime integers with
$(U : V : W) = (u : v : 1)$. Then every rational solution $(u, v)$ of $v^2 = u^3 + au + b$ with
$uv \ne 0$ satisfies $H(u, v) > \lVert p \rVert^{1/6}/1.634$.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Corollary 1 (`integers-2025-A66-cor-1`). -/
public theorem naiveHeight_gt_of_small_linear_coeff (a b : ℤ) (hab : a * b ≠ 0)
    (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hsmall : 1 + |(a : ℝ)| < Real.sqrt (2 + a ^ 2 + b ^ 2) ^ ((1 : ℝ) / 2) / 1.782) (u v : ℚ)
    (huv : u * v ≠ 0) (hP : v ^ 2 = u ^ 3 + a * u + b) :
    Real.sqrt (2 + a ^ 2 + b ^ 2) ^ ((1 : ℝ) / 6) / 1.634 < Height.mulHeight ![u, v, 1] := by
  let H := Height.mulHeight ![u, v, 1]
  let N := Real.sqrt (2 + (a : ℝ) ^ 2 + (b : ℝ) ^ 2)
  have hH : 0 < H := Height.mulHeight_pos _
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hbound : N ≤ (4 + 2 * |(a : ℝ)|) * H ^ 3 :=
    coeffNorm_le_of_curve_eq (Height.one_le_mulHeight _) (abs_coord_le_naiveHeight u v 0)
      (abs_coord_le_naiveHeight u v 1) (by exact_mod_cast hP)
  change 1 + |(a : ℝ)| < N ^ ((1 : ℝ) / 2) / 1.782 at hsmall
  rw [← Real.sqrt_eq_rpow] at hsmall
  have hcoeff : 4 + 2 * |(a : ℝ)| < Real.sqrt N * 1.634 ^ 3 := by
    norm_num1 at hsmall ⊢
    linarith only [hsmall, abs_nonneg (a : ℝ)]
  change N ^ ((1 : ℝ) / 6) / 1.634 < H
  apply (div_lt_iff₀ (by norm_num)).mpr
  apply lt_of_pow_lt_pow_left₀ 3 (by positivity)
  rw [← Real.rpow_mul_natCast hN, show (1 : ℝ) / 6 * (3 : ℕ) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  apply lt_of_mul_lt_mul_left (a := Real.sqrt N) _ (Real.sqrt_nonneg _)
  calc
    Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN
    _ ≤ _ := hbound
    _ < (Real.sqrt N * 1.634 ^ 3) * H ^ 3 := mul_lt_mul_of_pos_right hcoeff (pow_pos hH _)
    _ = Real.sqrt N * (H * 1.634) ^ 3 := by ring

end MetaMathlibExt
