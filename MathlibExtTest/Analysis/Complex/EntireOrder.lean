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

Non-vacuity of `Complex.Hadamard.EntireOfOrderAtMost` and `Complex.HasGrowthOrder`: `exp` has
order `1`, `z ↦ z` and every polynomial have order `0`, `exp ∘ exp` has no finite order, and a
constant function has order exactly `0`. Boundary probes for negative exponents: a constant of
norm at most `1` has order at most every real number, while the constant `5` and `z ↦ z` have
order at most no negative exponent.
-/

@[expose] public section

open Filter Asymptotics Bornology Complex Complex.Hadamard Topology

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

/-! ### The definition and its `O`-form -/

/-- The definition is PrimeNumberTheoremAnd's bound, unfolded. -/
example : EntireOfOrderAtMost 1 Complex.exp ↔ Differentiable ℂ Complex.exp ∧
    ∀ ε : ℝ, 0 < ε → ∃ C > 0, ∀ z : ℂ, ‖Complex.exp z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (1 + ε)) :=
  Iff.rfl

/-! ### Constants -/

/-- A constant has order at most every nonnegative exponent. -/
example : EntireOfOrderAtMost (1 / 2) (fun _ : ℂ => (3 : ℂ)) :=
  entireOfOrderAtMost_const _ (by norm_num)

/-- **Boundary probe.** A constant of norm at most `1` has order at most every exponent,
including negative ones. -/
example : EntireOfOrderAtMost (-1) (fun _ : ℂ => (1 / 2 : ℂ)) := by
  refine ⟨differentiable_const _, fun ε _ => ⟨1, one_pos, fun z => ?_⟩⟩
  have h0 : (0 : ℝ) ≤ 1 * (1 + ‖z‖) ^ (-1 + ε) := by positivity
  calc ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    _ ≤ 1 := by norm_num
    _ ≤ Real.exp (1 * (1 + ‖z‖) ^ (-1 + ε)) := Real.one_le_exp h0

/-- **Boundary probe.** The constant `5` has order at most no negative exponent: the bound
`exp (C (1 + ‖z‖) ^ (ρ + ε))` tends to `1` when `ρ + ε < 0`. This is why the closure properties
of `EntireOfOrderAtMost` assume `0 ≤ ρ`. -/
example : ¬ EntireOfOrderAtMost (-1) (fun _ : ℂ => (5 : ℂ)) := by
  intro h
  obtain ⟨C, -, hb⟩ := h.exists_bound (ε := 1 / 2) (by norm_num)
  have ht : Tendsto (fun x : ℝ => C * (1 + x) ^ (-1 + 1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).const_mul C
    rw [mul_zero] at this
    convert this using 3
    norm_num
  obtain ⟨x, hx, hx0⟩ :=
    ((ht.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 5)))).and
      (eventually_ge_atTop 0)).exists
  have h1 := hb x
  rw [Complex.norm_real, Real.norm_of_nonneg hx0] at h1
  have h2 : Real.exp (C * (1 + x) ^ (-1 + 1 / 2 : ℝ)) < 5 :=
    (Real.exp_lt_exp.mpr hx).trans_eq (Real.exp_log (by norm_num))
  have h3 : ‖(5 : ℂ)‖ = 5 := by norm_num
  linarith

/-- A constant function has order `0`. -/
example (c : ℂ) : HasGrowthOrder (fun _ : ℂ => c) 0 :=
  hasGrowthOrder_const c

/-- A constant function has no order other than `0`; in particular no negative order. -/
example (c : ℂ) (ρ : ℝ) (h : HasGrowthOrder (fun _ : ℂ => c) ρ) : ρ = 0 :=
  h.unique (hasGrowthOrder_const c)

/-- Negative orders are excluded outright. -/
example (f : ℂ → ℂ) : ¬ HasGrowthOrder f (-1) := fun h => by
  have := h.nonneg
  norm_num at this

/-- A bounded entire function has order `0`. -/
example : HasGrowthOrder (fun z : ℂ => Complex.exp 2 + 0 * z) 0 := by
  refine hasGrowthOrder_zero_of_isBigO_one (by fun_prop)
    (IsBigO.of_bound ‖Complex.exp 2‖ (Eventually.of_forall fun z => ?_))
  simp

/-! ### `exp` has order `1` -/

/-- `exp` has exponential type, hence order at most `1`. -/
private theorem exp_entireOfOrderAtMost_one : EntireOfOrderAtMost 1 Complex.exp := by
  refine entireOfOrderAtMost_one_of_isBigO_exp_mul_norm (A := 1) Complex.differentiable_exp
    (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
  rw [Complex.norm_exp, one_mul, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (Complex.re_le_norm z)

/-- The `O`-form of order at most `1` for `exp`. -/
example : ∀ ε > (0 : ℝ), Complex.exp =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ (1 + ε)) :=
  ((entireOfOrderAtMost_iff zero_le_one).mp exp_entireOfOrderAtMost_one).2

/-- `exp` does not have order at most any `ρ < 1`. -/
private theorem exp_not_entireOfOrderAtMost {ρ : ℝ} (hρ : ρ < 1) :
    ¬ EntireOfOrderAtMost ρ Complex.exp := by
  intro h
  have hmax : max ρ 0 < 1 := max_lt hρ one_pos
  have hO := isBigO_real_of_growth (F := id) (h.isBigO_exp_rpow (τ := (max ρ 0 + 1) / 2)
    (by linarith [le_max_left ρ 0]) (by linarith [le_max_right ρ 0]))
  simp only [id, Complex.ofReal_re] at hO
  have hlo : (fun x : ℝ => Real.exp (x ^ ((max ρ 0 + 1) / 2))) =o[atTop] fun x => Real.exp x :=
    Real.isLittleO_exp_comp_exp_comp.mpr (tendsto_sub_rpow_atTop (by linarith))
  exact isLittleO_irrefl (Eventually.of_forall fun x => (Real.exp_pos x).ne').frequently
    (hO.trans_isLittleO hlo)

/-- **`exp` has order exactly `1`.** -/
private theorem exp_hasGrowthOrder_one : HasGrowthOrder Complex.exp 1 :=
  ⟨zero_le_one, exp_entireOfOrderAtMost_one, fun _ hρ => exp_not_entireOfOrderAtMost hρ.2⟩

example : HasGrowthOrder Complex.exp 1 := exp_hasGrowthOrder_one

/-- Uniqueness: `exp` has no other order. -/
example : ¬ HasGrowthOrder Complex.exp 2 := fun h => by
  have := h.unique exp_hasGrowthOrder_one
  norm_num at this

/-- Products: `exp z * exp z = exp (2z)` has order at most `1`. -/
example : EntireOfOrderAtMost 1 (fun z => Complex.exp z * Complex.exp z) :=
  exp_entireOfOrderAtMost_one.mul exp_entireOfOrderAtMost_one

/-- Sums: `exp z + exp z` has order at most `1`. -/
example : EntireOfOrderAtMost 1 (fun z => Complex.exp z + Complex.exp z) :=
  exp_entireOfOrderAtMost_one.add exp_entireOfOrderAtMost_one zero_le_one

/-- Domination: an entire function that is `O(exp)` at infinity has order at most `1`. -/
example : EntireOfOrderAtMost 1 (fun z => 2 * Complex.exp z) :=
  exp_entireOfOrderAtMost_one.trans_isBigO zero_le_one (by fun_prop)
    ((isBigO_refl Complex.exp _).const_mul_left 2)

/-- Monotonicity in the exponent. -/
example : EntireOfOrderAtMost 3 Complex.exp :=
  exp_entireOfOrderAtMost_one.mono (by norm_num)

/-! ### `z ↦ z` has order `0` -/

/-- `z` is `O(exp (‖z‖ ^ ε))` for every `ε > 0`. -/
private theorem id_entireOfOrderAtMost_zero : EntireOfOrderAtMost 0 (fun z : ℂ => z) := by
  refine EntireOfOrderAtMost.of_isBigO differentiable_fun_id le_rfl fun ε hε => ?_
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

/-- `z` does not have order at most any `ρ < 0`: it would be bounded by `exp C`. -/
private theorem id_not_entireOfOrderAtMost {ρ : ℝ} (hρ : ρ < 0) :
    ¬ EntireOfOrderAtMost ρ (fun z : ℂ => z) := by
  intro h
  obtain ⟨C, hC, hb⟩ := h.exists_bound (ε := -ρ / 2) (by linarith)
  set x : ℝ := Real.exp C + 1 with hx
  have hx0 : 0 ≤ x := by positivity
  have hle : (1 + ‖(x : ℂ)‖) ^ (ρ + -ρ / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (x : ℂ)]) (by linarith)
  have h1 := (hb x).trans (Real.exp_le_exp.mpr (mul_le_of_le_one_right hC.le hle))
  rw [Complex.norm_real, Real.norm_of_nonneg hx0] at h1
  linarith

/-- **`z ↦ z` has order exactly `0`.** -/
example : HasGrowthOrder (fun z : ℂ => z) 0 :=
  hasGrowthOrder_zero_iff.mpr id_entireOfOrderAtMost_zero

/-- `z ↦ z` has order at most no negative exponent, so order `0` is sharp also among the
exponents of `EntireOfOrderAtMost`. -/
example : ¬ EntireOfOrderAtMost (-1) (fun z : ℂ => z) :=
  id_not_entireOfOrderAtMost (by norm_num)

/-! ### Polynomials have order `0` -/

/-- Every polynomial has order at most `0`. -/
private theorem polynomial_entireOfOrderAtMost_zero (p : Polynomial ℂ) :
    EntireOfOrderAtMost 0 (fun z => p.eval z) := by
  induction p using Polynomial.induction_on with
  | C a => simpa using entireOfOrderAtMost_const a le_rfl
  | add p q hp hq => simpa using hp.add hq le_rfl
  | monomial n a h =>
    simpa [pow_succ, mul_assoc] using h.mul id_entireOfOrderAtMost_zero

/-- **Every polynomial has order exactly `0`.** -/
example (p : Polynomial ℂ) : HasGrowthOrder (fun z => p.eval z) 0 :=
  hasGrowthOrder_zero_iff.mpr (polynomial_entireOfOrderAtMost_zero p)

/-- A concrete polynomial: `z ^ 3 - 2 z + 1` has order `0`. -/
example : HasGrowthOrder (fun z : ℂ => z ^ 3 - 2 * z + 1) 0 := by
  have := polynomial_entireOfOrderAtMost_zero (.X ^ 3 - .C 2 * .X + 1)
  exact hasGrowthOrder_zero_iff.mpr (by simpa using this)

/-! ### `exp ∘ exp` has no finite order -/

/-- **`exp (exp z)` has no finite order.** -/
example (ρ : ℝ) : ¬ EntireOfOrderAtMost ρ (fun z => Complex.exp (Complex.exp z)) := by
  intro h
  have hO := isBigO_real_of_growth (F := Complex.exp)
    (h.isBigO_exp_rpow (τ := max ρ 0 + 1) (by linarith [le_max_left ρ 0])
      (by linarith [le_max_right ρ 0]))
  have hre : ∀ x : ℝ, (Complex.exp x).re = Real.exp x := fun x => by
    rw [← Complex.ofReal_exp, Complex.ofReal_re]
  simp only [hre] at hO
  have hsub : Tendsto (fun x : ℝ => Real.exp x - x ^ (max ρ 0 + 1)) atTop atTop := by
    have hb := (isLittleO_rpow_exp_atTop (max ρ 0 + 1)).bound (c := 1 / 2) (by norm_num)
    refine tendsto_atTop_mono' atTop ?_
      (Real.tendsto_exp_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hb, eventually_ge_atTop 0] with x hx hx0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _),
      Real.norm_of_nonneg (Real.exp_pos _).le] at hx
    linarith
  have hlo : (fun x : ℝ => Real.exp (x ^ (max ρ 0 + 1))) =o[atTop]
      fun x => Real.exp (Real.exp x) :=
    Real.isLittleO_exp_comp_exp_comp.mpr hsub
  exact isLittleO_irrefl (Eventually.of_forall fun x => (Real.exp_pos _).ne').frequently
    (hO.trans_isLittleO hlo)

/-! ### Zeros -/

/-- The zero-counting bound for a zero-free function: the count is `0`. -/
example {ε : ℝ} (hε : 0 < ε) :
    (fun r : ℝ => ((∑ᶠ u, MeromorphicOn.divisor Complex.exp (Metric.closedBall 0 r) u : ℤ) : ℝ))
      =O[atTop] fun r => r ^ (1 + ε) :=
  exp_entireOfOrderAtMost_one.isBigO_sum_divisor_closedBall zero_le_one hε

/-- The convergence-exponent bound is satisfiable: `exp` with the empty family of zeros. -/
example {ε : ℝ} (hε : 0 < ε) : Summable fun n : Empty => ‖(Empty.elim n : ℂ)‖ ^ (-1 - ε) :=
  exp_entireOfOrderAtMost_one.summable_norm_rpow_neg zero_le_one
    (by simp) (fun w => by
      rw [(Complex.differentiable_exp.analyticAt w).analyticOrderAt_eq_zero.mpr
        (Complex.exp_ne_zero w)]
      simp) hε
