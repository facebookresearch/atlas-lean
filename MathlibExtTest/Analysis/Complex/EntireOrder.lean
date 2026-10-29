/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.EntireOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Tests for the order of growth of entire functions

Non-vacuity of `Complex.HasGrowthOrderLE` and `Complex.HasGrowthOrder`: `exp` has order `1`,
`z ↦ z` and every polynomial have order `0`, `exp ∘ exp` has no finite order, and a constant
function has order at most every real number and order exactly `0`.
-/

@[expose] public section

open Filter Asymptotics Bornology Complex

/-! ### Helpers -/

/-- If `exp ∘ F =O[cobounded ℂ] exp (‖z‖ ^ p)` along the positive reals, then
`exp (Re F x) =O exp (x ^ p)` as real functions. -/
private lemma isBigO_real_of_growth {F : ℂ → ℂ} {p : ℝ}
    (h : (fun z => Complex.exp (F z)) =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ p)) :
    (fun x : ℝ => Real.exp (F x).re) =O[atTop] fun x : ℝ => Real.exp (x ^ p) := by
  have h' := h.comp_tendsto (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  refine (h'.norm_left.congr_left fun x => ?_).congr' (Eventually.of_forall fun _ => rfl) ?_
  · simp [Function.comp, Complex.norm_exp]
  · filter_upwards [eventually_ge_atTop 0] with x hx
    simp [Function.comp, abs_of_nonneg hx]

/-- `x ^ s ≤ x / 2` eventually for `s < 1`, so `x - x ^ s → ∞`. -/
private lemma tendsto_sub_rpow_atTop {s : ℝ} (hs : s < 1) :
    Tendsto (fun x : ℝ => x - x ^ s) atTop atTop := by
  have hb := (tendsto_rpow_neg_atTop (y := 1 - s) (by linarith)).eventually
    (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hb, eventually_gt_atTop 0] with x hx hx0
  have he : x ^ s = x ^ (-(1 - s)) * x := by
    rw [← Real.rpow_add_one hx0.ne']; congr 1; ring
  simp only [id]
  nlinarith

/-! ### Constants -/

/-- A constant has order at most every exponent, including negative ones. -/
example : HasGrowthOrderLE (fun _ : ℂ => (3 : ℂ)) (-5) :=
  hasGrowthOrderLE_const _ _

/-- **Boundary probe.** A constant function has order `0`, the classical value, even though it
has order at most every negative exponent. -/
example (c : ℂ) : HasGrowthOrder (fun _ : ℂ => c) 0 :=
  hasGrowthOrder_const c

/-- A constant function has no order other than `0`; in particular no negative order. -/
example (c : ℂ) (ρ : ℝ) (h : HasGrowthOrder (fun _ : ℂ => c) ρ) : ρ = 0 :=
  h.unique (hasGrowthOrder_const c)

/-- Negative orders are excluded outright. -/
example (f : ℂ → ℂ) : ¬ HasGrowthOrder f (-1) := fun h => by
  have := h.nonneg
  norm_num at this

/-- A bounded function has order at most every exponent. -/
example : HasGrowthOrderLE (fun z : ℂ => Complex.exp (Complex.I * z.re)) (-1) := by
  refine hasGrowthOrderLE_of_isBigO_one (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)) _
  rw [Complex.norm_exp]
  simp

/-! ### `exp` has order `1` -/

/-- `exp` has exponential type, hence order at most `1`. -/
private theorem exp_hasGrowthOrderLE_one : HasGrowthOrderLE Complex.exp 1 := by
  refine hasGrowthOrderLE_one_of_isBigO_exp_mul_norm (A := 1)
    (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
  rw [Complex.norm_exp, one_mul, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (Complex.re_le_norm z)

/-- `exp` does not have order at most any `ρ < 1`. -/
private theorem exp_not_hasGrowthOrderLE {ρ : ℝ} (hρ : ρ < 1) :
    ¬ HasGrowthOrderLE Complex.exp ρ := by
  intro h
  have hO := isBigO_real_of_growth (F := id) (h ((1 - ρ) / 2) (by linarith))
  simp only [id, Complex.ofReal_re] at hO
  have hlo : (fun x : ℝ => Real.exp (x ^ (ρ + (1 - ρ) / 2))) =o[atTop] fun x => Real.exp x :=
    Real.isLittleO_exp_comp_exp_comp.mpr (tendsto_sub_rpow_atTop (by linarith))
  exact isLittleO_irrefl (Eventually.of_forall fun x => (Real.exp_pos x).ne').frequently
    (hO.trans_isLittleO hlo)

/-- **`exp` has order exactly `1`.** -/
private theorem exp_hasGrowthOrder_one : HasGrowthOrder Complex.exp 1 :=
  ⟨zero_le_one, exp_hasGrowthOrderLE_one, fun _ hρ => exp_not_hasGrowthOrderLE hρ.2⟩

example : HasGrowthOrder Complex.exp 1 := exp_hasGrowthOrder_one

/-- Uniqueness: `exp` has no other order. -/
example : ¬ HasGrowthOrder Complex.exp 2 := fun h => by
  have := h.unique exp_hasGrowthOrder_one
  norm_num at this

/-- Products: `exp z * exp z = exp (2z)` has order at most `1`. -/
example : HasGrowthOrderLE (fun z => Complex.exp z * Complex.exp z) 1 :=
  exp_hasGrowthOrderLE_one.mul exp_hasGrowthOrderLE_one

/-- Monotonicity in the exponent. -/
example : HasGrowthOrderLE Complex.exp 3 :=
  exp_hasGrowthOrderLE_one.mono (by norm_num)

/-! ### `z ↦ z` has order `0` -/

/-- `z` is `O(exp (‖z‖ ^ ε))` for every `ε > 0`. -/
private theorem id_hasGrowthOrderLE_zero : HasGrowthOrderLE (fun z : ℂ => z) 0 := by
  intro ε hε
  rw [zero_add]
  -- `y ^ (1 / ε) = o(exp y)`, composed with `y = x ^ ε`
  have h1 := (isLittleO_rpow_exp_atTop (1 / ε)).isBigO.comp_tendsto
    ((tendsto_rpow_atTop hε).comp (tendsto_norm_cobounded_atTop (E := ℂ)))
  refine IsBigO.trans (isBigO_refl (fun z : ℂ => z) (cobounded ℂ)).norm_right ((h1.congr' ?_ ?_))
  · filter_upwards with z
    simp only [Function.comp]
    rw [← Real.rpow_mul (norm_nonneg z), mul_one_div_cancel hε.ne', Real.rpow_one]
  · filter_upwards with z
    rfl

/-- `z` does not have order at most any `ρ < 0`: it would be bounded. -/
private theorem id_not_hasGrowthOrderLE {ρ : ℝ} (hρ : ρ < 0) :
    ¬ HasGrowthOrderLE (fun z : ℂ => z) ρ := by
  intro h
  have h1 : (fun z : ℂ => z) =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ (ρ + -ρ / 2)) :=
    h (-ρ / 2) (by linarith)
  obtain ⟨C, hC⟩ := h1.bound
  have hev := (tendsto_norm_cobounded_atTop (E := ℂ)).eventually
    ((eventually_ge_atTop 1).and (eventually_gt_atTop (C * Real.exp 1)))
  obtain ⟨z, hz, hz1, hzC⟩ := (hC.and hev).exists
  have hle : Real.exp (‖z‖ ^ (ρ + -ρ / 2)) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hz
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg z, Real.exp_pos (‖z‖ ^ (ρ + -ρ / 2))]
  nlinarith [mul_le_mul_of_nonneg_left hle hC0]

/-- **`z ↦ z` has order exactly `0`.** -/
example : HasGrowthOrder (fun z : ℂ => z) 0 :=
  hasGrowthOrder_zero_iff.mpr id_hasGrowthOrderLE_zero

/-- `z ↦ z` has order at most no negative exponent, so order `0` is sharp also among the
exponents of `HasGrowthOrderLE`. -/
example : ¬ HasGrowthOrderLE (fun z : ℂ => z) (-1) :=
  id_not_hasGrowthOrderLE (by norm_num)

/-! ### Polynomials have order `0` -/

/-- Every polynomial has order at most `0`. -/
private theorem polynomial_hasGrowthOrderLE_zero (p : Polynomial ℂ) :
    HasGrowthOrderLE (fun z => p.eval z) 0 := by
  induction p using Polynomial.induction_on with
  | C a => simpa using hasGrowthOrderLE_const a 0
  | add p q hp hq => simpa using hp.add hq
  | monomial n a h =>
    simpa [pow_succ, mul_assoc] using h.mul id_hasGrowthOrderLE_zero

/-- **Every polynomial has order exactly `0`.** -/
example (p : Polynomial ℂ) : HasGrowthOrder (fun z => p.eval z) 0 :=
  hasGrowthOrder_zero_iff.mpr (polynomial_hasGrowthOrderLE_zero p)

/-- A concrete polynomial: `z ^ 3 - 2 z + 1` has order `0`. -/
example : HasGrowthOrder (fun z : ℂ => z ^ 3 - 2 * z + 1) 0 := by
  have := polynomial_hasGrowthOrderLE_zero (.X ^ 3 - .C 2 * .X + 1)
  exact hasGrowthOrder_zero_iff.mpr (by simpa using this)

/-! ### `exp ∘ exp` has no finite order -/

/-- **`exp (exp z)` has no finite order.** -/
example (ρ : ℝ) : ¬ HasGrowthOrderLE (fun z => Complex.exp (Complex.exp z)) ρ := by
  intro h
  have hO := isBigO_real_of_growth (F := Complex.exp) (h 1 one_pos)
  have hre : ∀ x : ℝ, (Complex.exp x).re = Real.exp x := fun x => by
    rw [← Complex.ofReal_exp, Complex.ofReal_re]
  simp only [hre] at hO
  have hsub : Tendsto (fun x : ℝ => Real.exp x - x ^ (ρ + 1)) atTop atTop := by
    have hb := (isLittleO_rpow_exp_atTop (ρ + 1)).bound (c := 1 / 2) (by norm_num)
    refine tendsto_atTop_mono' atTop ?_
      (Real.tendsto_exp_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hb, eventually_ge_atTop 0] with x hx hx0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _),
      Real.norm_of_nonneg (Real.exp_pos _).le] at hx
    linarith
  have hlo : (fun x : ℝ => Real.exp (x ^ (ρ + 1))) =o[atTop] fun x => Real.exp (Real.exp x) :=
    Real.isLittleO_exp_comp_exp_comp.mpr hsub
  exact isLittleO_irrefl (Eventually.of_forall fun x => (Real.exp_pos _).ne').frequently
    (hO.trans_isLittleO hlo)

/-! ### Zeros -/

/-- The zero-counting bound for a zero-free function: the count is `0`. -/
example {ε : ℝ} (hε : 0 < ε) :
    (fun r : ℝ => ((∑ᶠ u, MeromorphicOn.divisor Complex.exp (Metric.closedBall 0 r) u : ℤ) : ℝ))
      =O[atTop] fun r => r ^ (1 + ε) :=
  exp_hasGrowthOrderLE_one.isBigO_sum_divisor_closedBall Complex.differentiable_exp zero_le_one hε

/-- The convergence-exponent bound is satisfiable: `exp` with the empty family of zeros. -/
example {ε : ℝ} (hε : 0 < ε) : Summable fun n : Empty => ‖(Empty.elim n : ℂ)‖ ^ (-1 - ε) :=
  exp_hasGrowthOrderLE_one.summable_norm_rpow_neg Complex.differentiable_exp zero_le_one
    (by simp) (fun w => by
      rw [(Complex.differentiable_exp.analyticAt w).analyticOrderAt_eq_zero.mpr
        (Complex.exp_ne_zero w)]
      simp) hε
