/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.HadamardProduct
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.Analysis.PSeries

/-!
# Tests for genus-one Hadamard products
-/

@[expose] public section

open Filter Asymptotics Bornology Complex

private lemma exp_two_mul_hasGrowthOrderLE_one :
    HasGrowthOrderLE (fun z => Complex.exp (2 * z)) 1 := by
  refine hasGrowthOrderLE_one_of_isBigO_exp_mul_norm (A := 2)
    (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
  rw [Complex.norm_exp, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine Real.exp_le_exp.mpr ?_
  have := Complex.re_le_norm z
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

/-- **`exp (2z)` has order exactly `1`**, via the exponential-type criterion. -/
example : HasGrowthOrder (fun z => Complex.exp (2 * z)) 1 := by
  refine hasGrowthOrder_one_of_not_isBigO_exp_norm exp_two_mul_hasGrowthOrderLE_one fun h => ?_
  have h' := (h.comp_tendsto (RCLike.tendsto_ofReal_atTop_cobounded ℂ)).norm_left
  have hO : (fun x : ℝ => Real.exp (2 * x)) =O[atTop] fun x : ℝ => Real.exp x := by
    refine (h'.congr_left fun x => ?_).congr' (Eventually.of_forall fun _ => rfl) ?_
    · simp [Function.comp, Complex.norm_exp]
    · filter_upwards [eventually_ge_atTop 0] with x hx
      simp [Function.comp, abs_of_nonneg hx]
  have hlo : (fun x : ℝ => Real.exp x) =o[atTop] fun x : ℝ => Real.exp (2 * x) :=
    Real.isLittleO_exp_comp_exp_comp.mpr (by
      refine tendsto_id.congr fun x => ?_
      simp only [id]; ring)
  exact isLittleO_irrefl (Eventually.of_forall fun x => (Real.exp_pos _).ne').frequently
    (hO.trans_isLittleO hlo)

/-- The `‖s‖ log ‖s‖` criterion, at `exp`. -/
example : HasGrowthOrderLE Complex.exp 1 := by
  refine hasGrowthOrderLE_one_of_eventually_norm_le_exp_mul_log (c := 1) ?_
  filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually
    (eventually_ge_atTop (Real.exp 1))] with s hs
  rw [Complex.norm_exp, one_mul]
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le (Real.exp_pos 1) hs
  have hlog : 1 ≤ Real.log ‖s‖ := by
    rw [Real.le_log_iff_exp_le hs0]; exact hs
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm s).trans ?_)
  nlinarith

/-- Order `< 1` gives exponential type with constant `1`, here for a constant. -/
example : (fun _ : ℂ => (5 : ℂ)) =O[cobounded ℂ] fun s => Real.exp ‖s‖ :=
  (hasGrowthOrderLE_const (5 : ℂ) (1 / 2)).isBigO_exp_norm_of_lt_one (by norm_num)

/-- The zeros `n + 1` of a would-be `1 / Γ(1 - s)` satisfy `∑ ‖zₙ‖⁻² < ∞`. -/
private lemma summable_nat_succ : Summable fun n : ℕ => ‖((n : ℂ) + 1)‖ ^ (-2 : ℝ) := by
  have h := (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).comp_injective
    (add_left_injective 1)
  refine h.congr fun n => ?_
  simp only [Function.comp]
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast,
    Real.rpow_neg (by positivity)]

example (s : ℂ) : Summable fun n : ℕ => 1 / (s - ((n : ℂ) + 1)) + 1 / ((n : ℂ) + 1) :=
  summable_one_div_sub_add_one_div (fun n => by exact_mod_cast n.succ_ne_zero) summable_nat_succ s

example : ∀ᶠ n : ℕ in cofinite, (10 : ℝ) ≤ ‖((n : ℂ) + 1)‖ :=
  eventually_le_norm_of_summable_norm_rpow_neg_two (fun n => by exact_mod_cast n.succ_ne_zero)
    summable_nat_succ (by norm_num)

example (w : ℂ) : {n : ℕ | (n : ℂ) + 1 = w}.Finite :=
  finite_setOf_eq_of_summable_norm_rpow_neg_two (fun n => by exact_mod_cast n.succ_ne_zero)
    summable_nat_succ w

/-! ### Hadamard products with no zeros -/

private lemma hAB_exp (s : ℂ) : Complex.exp s =
    Complex.exp (0 + 1 * s) * ∏' n : Empty, (1 - s / Empty.elim n) * Complex.exp (s / Empty.elim n) :=
  by simp

example : Complex.exp 0 = Complex.exp 0 := exp_eq_apply_zero_of_eq_exp_mul_tprod hAB_exp

/-- The logarithmic derivative of `exp` is the `B = 1` of its Hadamard product. -/
example (s : ℂ) : logDeriv Complex.exp s = 1 + ∑' n : Empty, (1 / (s - Empty.elim n) +
    1 / Empty.elim n) :=
  logDeriv_eq_add_tsum_of_eq_exp_mul_tprod (fun n => n.elim) (by simp) hAB_exp
    (fun n => n.elim) (Complex.differentiable_exp s) (Complex.exp_ne_zero s)

example : ∃ b : ℝ, ∀ s, ‖Complex.exp s‖ ≤ Real.exp (‖(0 : ℂ)‖ + b * ‖s‖) :=
  exists_norm_le_exp_of_eq_exp_mul_tprod hAB_exp

/-- The symmetric-product identity is satisfiable (trivially) by the constant `1`. -/
example : HasSum (fun n : Empty => (1 / (Empty.elim n : ℂ)).re) (-(0 : ℂ).re) :=
  hasSum_re_one_div_of_eq_exp_mul_tprod (f := fun _ => 1) (ε := 1) (A := 0) (B := 0)
    (differentiable_const _) (hasGrowthOrderLE_const _ _) one_ne_zero
    (fun w => by
      rw [(analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero]
      simp)
    (fun s => by simp) (fun w h => absurd h one_ne_zero) (fun s => by simp)
