/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Height of a rational point in terms of its x-coordinate

We bound the naive height of a rational point on `y² = x³ + ax - b` by
`√(1 + |a|)` times the three-halves power of the height of its x-coordinate.

Statements from Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66.
-/

namespace MetaMathlibExt

private lemma tuple_sup (w : AbsoluteValue ℚ ℝ) (u v : ℚ) :
    (⨆ i, w (![u, v, 1] i)) = max (w u) (max (w v) 1) := by
  apply eq_of_forall_ge_iff
  intro c
  simp [ciSup_le_iff, Fin.forall_fin_succ]

private lemma max_support (u : ℚ) :
    Function.HasFiniteMulSupport (fun w : NumberField.FinitePlace ℚ => max (w u) 1) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simpa using (Function.hasFiniteMulSupport_one :
      Function.HasFiniteMulSupport (fun _ : NumberField.FinitePlace ℚ => (1 : ℝ)))
  · exact (NumberField.FinitePlace.hasFiniteMulSupport hu).sup Function.hasFiniteMulSupport_one

private lemma finite_bound (a b : ℤ) (u v : ℚ) (hP : v ^ 2 = u ^ 3 + a * u - b)
    (w : NumberField.FinitePlace ℚ) :
    max (w u) (max (w v) 1) ^ 2 ≤ max (w u) 1 ^ 3 := by
  have hw : IsNonarchimedean (w ·) := NumberField.FinitePlace.add_le w
  have hi (n : ℤ) : w n ≤ 1 :=
    hw.apply_intCast_le_one (map_zero_le w 1) (map_one w) (map_neg_eq_map w)
  let M := max (w u) 1
  have hM : 1 ≤ M := le_max_right _ _
  have hu : w u ≤ M := le_max_left _ _
  have hu3 : w u ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (apply_nonneg w u) hu 3
  have hM3 : M ≤ M ^ 3 := le_self_pow₀ hM (by decide)
  have hv : w v ^ 2 ≤ M ^ 3 := calc
    w v ^ 2 = w (u ^ 3 + a * u - b) := by rw [← map_pow, hP]
    _ ≤ max (w (u ^ 3 + a * u)) (w (-b : ℚ)) := by
      simpa only [sub_eq_add_neg] using NumberField.FinitePlace.add_le w (u ^ 3 + a * u) (-b)
    _ ≤ max (max (w (u ^ 3)) (w ((a : ℚ) * u))) 1 :=
      max_le_max (NumberField.FinitePlace.add_le w _ _) (by simpa using hi b)
    _ ≤ M ^ 3 := by
      simp only [map_pow, map_mul]
      exact max_le (max_le hu3 ((mul_le_of_le_one_left (apply_nonneg w u) (hi a)).trans
        (hu.trans hM3))) (hM.trans hM3)
  rw [max_pow_of_nonneg (apply_nonneg w u) (le_max_of_le_right zero_le_one),
    max_pow_of_nonneg (apply_nonneg w v) zero_le_one, one_pow]
  exact max_le ((pow_le_pow_left₀ (apply_nonneg w u) hu 2).trans
    (pow_le_pow_right₀ hM (by decide))) (max_le hv (hM.trans hM3))

private lemma real_bound (a b u v : ℝ) (ha : 0 < |a|) (hb : 0 < b)
    (hP : v ^ 2 = u ^ 3 + a * u - b) :
    max |u| (max |v| 1) ^ 2 < (1 + |a|) * max |u| 1 ^ 3 := by
  let M := max |u| 1
  have hM : 1 ≤ M := le_max_right _ _
  have hu : |u| ≤ M := le_max_left _ _
  have hM3 : M ≤ M ^ 3 := le_self_pow₀ hM (by decide)
  have hMpos : 0 < M ^ 3 := pow_pos (zero_lt_one.trans_le hM) _
  have hstrict : M ^ 3 < (1 + |a|) * M ^ 3 := by nlinarith
  have hu3 : u ^ 3 ≤ M ^ 3 := calc
    u ^ 3 ≤ |u| ^ 3 := by simpa only [abs_pow] using le_abs_self (u ^ (3 : ℕ))
    _ ≤ M ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hu _
  have hau : a * u ≤ |a| * M ^ 3 := calc
    a * u ≤ |a| * |u| := by simpa only [abs_mul] using le_abs_self (a * u)
    _ ≤ |a| * M ^ 3 := mul_le_mul_of_nonneg_left (hu.trans hM3) (abs_nonneg _)
  have hv : v ^ 2 < (1 + |a|) * M ^ 3 := by nlinarith only [hP, hb, hu3, hau]
  have hu2 : |u| ^ 2 < (1 + |a|) * M ^ 3 :=
    ((pow_le_pow_left₀ (abs_nonneg _) hu 2).trans
      (pow_le_pow_right₀ hM (by decide : 2 ≤ 3))).trans_lt hstrict
  have h1 : (1 : ℝ) ^ 2 < (1 + |a|) * M ^ 3 := by
    simpa using (hM.trans hM3).trans_lt hstrict
  rw [max_pow_of_nonneg (abs_nonneg u) (le_max_of_le_right zero_le_one),
    max_pow_of_nonneg (abs_nonneg v) zero_le_one]
  exact max_lt hu2 (max_lt (by simpa only [sq_abs] using hv) h1)

private lemma height_eq (u v : ℚ) : Height.mulHeight ![u, v, 1] =
    max |(u : ℝ)| (max |(v : ℝ)| 1) *
      ∏ᶠ w : NumberField.FinitePlace ℚ, max (w u) (max (w v) 1) := by
  rw [NumberField.mulHeight_eq (by simp)]
  simp_rw [show ∀ w : NumberField.InfinitePlace ℚ,
    (⨆ i, w (![u, v, 1] i)) = max |(u : ℝ)| (max |(v : ℝ)| 1) from
      fun w => by simpa only [← NumberField.InfinitePlace.coe_apply,
        Rat.infinitePlace_apply, Rat.cast_abs]
        using tuple_sup w.val u v]
  simp_rw [show ∀ w : NumberField.FinitePlace ℚ,
    (⨆ i, w (![u, v, 1] i)) = max (w u) (max (w v) 1) from
      fun w => tuple_sup w.val u v]
  simp

private lemma height_x_eq (u : ℚ) : Height.mulHeight ![u, 1] =
    max |(u : ℝ)| 1 * ∏ᶠ w : NumberField.FinitePlace ℚ, max (w u) 1 := by
  rw [← Height.mulHeight₁_eq_mulHeight, NumberField.mulHeight₁_eq]
  simp

private lemma squared_bound (a b : ℤ) (ha : a ≠ 0) (hb : 0 < b) (u v : ℚ)
    (hP : v ^ 2 = u ^ 3 + a * u - b) :
    Height.mulHeight ![u, v, 1] ^ 2 <
      (1 + |(a : ℝ)|) * Height.mulHeight ![u, 1] ^ 3 := by
  have hreal := real_bound (a : ℝ) (b : ℝ) (u : ℝ) (v : ℝ)
    (abs_pos.mpr (by exact_mod_cast ha)) (by exact_mod_cast hb) (by exact_mod_cast hP)
  have hs : Function.HasFiniteMulSupport
      (fun w : NumberField.FinitePlace ℚ => max (w u) (max (w v) 1)) := by
    simpa only [max_assoc, max_left_comm, max_self] using (max_support u).sup (max_support v)
  have hf : (∏ᶠ w : NumberField.FinitePlace ℚ, max (w u) (max (w v) 1)) ^ 2 ≤
      (∏ᶠ w : NumberField.FinitePlace ℚ, max (w u) 1) ^ 3 := by
    rw [finprod_pow hs, finprod_pow (max_support u)]
    exact finprod_le_finprod₀ (hs.pow 2) (fun _ => sq_nonneg _)
      ((max_support u).pow 3) (finite_bound a b u v hP)
  have hpos : 0 < (∏ᶠ w : NumberField.FinitePlace ℚ,
      max (w u) (max (w v) 1)) ^ 2 := by
    have h1 : 1 ≤ ∏ᶠ w : NumberField.FinitePlace ℚ, max (w u) (max (w v) 1) :=
      one_le_finprod fun w => (le_max_right (w v) 1).trans (le_max_right _ _)
    positivity
  rw [height_eq, height_x_eq, mul_pow, mul_pow, ← mul_assoc]
  exact (mul_lt_mul_of_pos_right hreal hpos).trans_le
    (mul_le_mul_of_nonneg_left hf (by positivity))

/-- **Height of a point on $y^2 = x^3 + ax - b$ versus the height of its $x$-coordinate.** Let
$a, b \in \mathbb{Z}$ with $a \ne 0$, $b > 0$ and $4a^3 + 27b^2 \ne 0$. For $u \in \mathbb{Q}$
let $H(u) = \max(|u_0|, u_1)$, where $u = u_0/u_1$ in lowest terms with $u_1 > 0$, and for
$u, v \in \mathbb{Q}$ let $H(u, v) = \max(|U|, |V|, |W|)$, where $U, V, W$ are coprime integers
with $(U : V : W) = (u : v : 1)$. Then every rational solution $(u, v)$ of
$v^2 = u^3 + au - b$ satisfies $H(u, v) < \sqrt{1 + |a|}\, H(u)^{3/2}$.

Source: Dimitrios Poulakis, *Lower Bounds for the Height of Rational Points of Elliptic
Curves*, INTEGERS 25 (2025), Article A66, Lemma 4 (`integers-2025-A66-lem-4`). -/
public theorem naiveHeight_lt_sqrt_mul_naiveHeight_x_rpow (a b : ℤ) (ha : a ≠ 0)
    (hb : 0 < b) (hE : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (u v : ℚ)
    (hP : v ^ 2 = u ^ 3 + a * u - b) :
    Height.mulHeight ![u, v, 1] <
      Real.sqrt (1 + |(a : ℝ)|) * Height.mulHeight ![u, 1] ^ ((3 : ℝ) / 2) := by
  have _ := hE
  have h := squared_bound a b ha hb u v hP
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_mul_natCast (by positivity),
    show (3 : ℝ) / 2 * (2 : ℕ) = 3 by norm_num]
  simpa only [Real.rpow_ofNat] using h

end MetaMathlibExt
