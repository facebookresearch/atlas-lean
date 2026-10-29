/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.HadamardFactorization
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Genus-one Hadamard products

This file collects consequences of a Hadamard factorization
`f s = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)` of an entire function of order at most `1`,
together with criteria for the growth order of an entire function.

## Main statements

* `Complex.hasGrowthOrderLE_one_of_eventually_norm_le_exp_mul_log`: a bound
  `‖f s‖ ≤ exp (c ‖s‖ log ‖s‖)` at infinity gives order at most `1`.
* `Complex.not_isBigO_exp_mul_norm_of_factorial_le`: factorial growth along a sequence going to
  infinity at linear speed rules out exponential type.
* `Complex.hasGrowthOrder_one_of_not_isBigO_exp_norm`: order at most `1`, but not of exponential
  type with constant `1`, gives order exactly `1`.
* `Complex.summable_one_div_sub_add_one_div`: the paired sum `∑ (1 / (s - zₙ) + 1 / zₙ)`
  converges when `∑ ‖zₙ‖⁻² < ∞`.
* `Complex.logDeriv_eq_add_tsum_of_eq_exp_mul_tprod`: the logarithmic derivative of a Hadamard
  product is `B + ∑ (1 / (s - zₙ) + 1 / zₙ)`.
* `Complex.exp_eq_apply_zero_of_eq_exp_mul_tprod`: the constant term satisfies `exp A = f 0`.
* `Complex.setOf_eq_zero_infinite_of_hasGrowthOrderLE_one`: an entire function of order at most
  `1` that is not of exponential type has infinitely many zeros.
* `Complex.hasSum_re_one_div_of_eq_exp_mul_tprod`: if `f s = ε conj (f (1 - conj s))` and the
  zeros lie in the strip `0 ≤ Re s ≤ 1`, then `∑ Re (1 / zₙ) = -Re B`.
-/

@[expose] public section

open Filter Topology Asymptotics Bornology

namespace Complex

/-! ### Growth criteria -/

section Growth

variable {E : Type*} [Norm E] {f : ℂ → E}

/-- A bound `‖f s‖ ≤ exp (c ‖s‖ log ‖s‖)` at infinity gives order of growth at most `1`. -/
theorem hasGrowthOrderLE_one_of_eventually_norm_le_exp_mul_log {c : ℝ}
    (hf : ∀ᶠ s in cobounded ℂ, ‖f s‖ ≤ Real.exp (c * ‖s‖ * Real.log ‖s‖)) :
    HasGrowthOrderLE f 1 := by
  intro ε hε
  have hlo := (isLittleO_log_rpow_atTop hε).bound (c := 1 / (|c| + 1)) (by positivity)
  have hev : ∀ᶠ x : ℝ in atTop, c * x * Real.log x ≤ x ^ ((1 : ℝ) + ε) := by
    filter_upwards [hlo, eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 ε)] at hx
    have h1 : c * Real.log x ≤ x ^ ε := by
      calc c * Real.log x ≤ |c| * |Real.log x| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ (|c| + 1) * |Real.log x| := by gcongr; linarith
        _ ≤ (|c| + 1) * (1 / (|c| + 1) * x ^ ε) := by gcongr
        _ = x ^ ε := by field_simp
    rw [Real.rpow_add hx0, Real.rpow_one]
    nlinarith
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hf, tendsto_norm_cobounded_atTop.eventually hev] with s hs hs'
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hs.trans (Real.exp_le_exp.mpr hs')

/-- Order of growth less than `1` gives exponential type with constant `1`. -/
theorem HasGrowthOrderLE.isBigO_exp_norm_of_lt_one {ρ : ℝ} (h : HasGrowthOrderLE f ρ)
    (hρ : ρ < 1) : f =O[cobounded ℂ] fun s => Real.exp ‖s‖ := by
  have := h (1 - ρ) (by linarith)
  simpa using this

/-- **Factorial growth rules out exponential type.** If `‖s n‖ ≤ a (n + 1)`, `s n → ∞` and
`n! ≤ C Kⁿ ‖f (s n)‖` for all large `n`, then `f` is not `O(exp (b ‖s‖))` for any `b`. -/
theorem not_isBigO_exp_mul_norm_of_factorial_le {F : Type*} [SeminormedAddGroup F] {f : ℂ → F}
    {s : ℕ → ℂ}
    (hs : Tendsto s atTop (cobounded ℂ)) {a C K : ℝ} (hsn : ∀ n, ‖s n‖ ≤ a * (n + 1))
    (hf : ∀ᶠ n in atTop, (n.factorial : ℝ) ≤ C * K ^ n * ‖f (s n)‖) (b : ℝ) :
    ¬ f =O[cobounded ℂ] fun z => Real.exp (b * ‖z‖) := by
  intro hO
  obtain ⟨c, hc⟩ := hO.bound
  set t : ℝ := |K| * Real.exp (|b| * |a|) with ht
  set M : ℝ := |C| * |c| * Real.exp (|b| * |a|) with hM
  have hbound : ∀ᶠ n in atTop, (n.factorial : ℝ) ≤ M * t ^ n := by
    filter_upwards [hf, hs.eventually hc] with n hn hn'
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hn'
    have hexp : Real.exp (b * ‖s n‖) ≤ Real.exp (|b| * |a|) * Real.exp (|b| * |a|) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      have h1 : b * ‖s n‖ ≤ |b| * ‖s n‖ := mul_le_mul_of_nonneg_right (le_abs_self b)
        (norm_nonneg _)
      have h2 : ‖s n‖ ≤ |a| * (n + 1) :=
        (hsn n).trans (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity))
      have h3 : |b| * ‖s n‖ ≤ |b| * (|a| * (n + 1)) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
      nlinarith
    calc (n.factorial : ℝ) ≤ C * K ^ n * ‖f (s n)‖ := hn
      _ ≤ |C| * |K| ^ n * (|c| * Real.exp (b * ‖s n‖)) := by
        rw [← abs_pow]
        refine (le_abs_self _).trans ?_
        rw [abs_mul, abs_mul, abs_norm]
        gcongr
        exact hn'.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (Real.exp_pos _).le)
      _ ≤ |C| * |K| ^ n * (|c| * (Real.exp (|b| * |a|) * Real.exp (|b| * |a|) ^ n)) := by
        gcongr
      _ = M * t ^ n := by rw [hM, ht, mul_pow]; ring
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop t
  have hMpos : 0 < M + 1 := by positivity
  obtain ⟨n, hn, hn'⟩ := ((hlim.eventually (gt_mem_nhds (one_div_pos.mpr hMpos))).and
    hbound).exists
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_lt_div_iff₀ hfac hMpos, one_mul] at hn
  have : 0 ≤ t ^ n := pow_nonneg (by positivity) n
  nlinarith

/-- An entire function of order at most `1` that is not `O(exp ‖s‖)` has order exactly `1`. -/
theorem hasGrowthOrder_one_of_not_isBigO_exp_norm (h1 : HasGrowthOrderLE f 1)
    (h : ¬ f =O[cobounded ℂ] fun s => Real.exp ‖s‖) : HasGrowthOrder f 1 :=
  ⟨zero_le_one, h1, fun _ hρ hρ' => h (hρ'.isBigO_exp_norm_of_lt_one hρ.2)⟩

end Growth

/-! ### The paired zero sum -/

section PairedSum

variable {ι : Type*} {z : ι → ℂ}

private lemma rpow_neg_two_eq (x : ℝ) : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast,
    inv_pow, one_div]

/-- Nonzero points with `∑ ‖zₙ‖⁻² < ∞` eventually (cofinitely) lie outside every ball. -/
theorem eventually_le_norm_of_summable_norm_rpow_neg_two (hz0 : ∀ n, z n ≠ 0)
    (hsum : Summable fun n => ‖z n‖ ^ (-2 : ℝ)) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in cofinite, R ≤ ‖z n‖ := by
  have := hsum.tendsto_cofinite_zero.eventually
    (gt_mem_nhds (a := 1 / R ^ 2) (one_div_pos.mpr (pow_pos hR 2)))
  filter_upwards [this] with n hn
  rw [rpow_neg_two_eq] at hn
  by_contra hlt
  push Not at hlt
  have hzn : 0 < ‖z n‖ := norm_pos_iff.mpr (hz0 n)
  have : 1 / R ^ 2 < 1 / ‖z n‖ ^ 2 := one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  linarith

/-- Each value is taken only finitely often by a family with `∑ ‖zₙ‖⁻² < ∞`. -/
theorem finite_setOf_eq_of_summable_norm_rpow_neg_two (hz0 : ∀ n, z n ≠ 0)
    (hsum : Summable fun n => ‖z n‖ ^ (-2 : ℝ)) (w : ℂ) : {n | z n = w}.Finite := by
  have h := eventually_le_norm_of_summable_norm_rpow_neg_two hz0 hsum
    (R := ‖w‖ + 1) (by positivity)
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun n hn => ?_
  simp only [Set.mem_ofPred_eq] at hn ⊢
  rw [hn]
  linarith

/-- **The paired zero sum converges.** For nonzero `zₙ` with `∑ ‖zₙ‖⁻² < ∞`,
`∑ (1 / (s - zₙ) + 1 / zₙ)` is summable for every `s`: the terms are
`s / ((s - zₙ) zₙ) = O(‖zₙ‖⁻²)`. -/
theorem summable_one_div_sub_add_one_div (hz0 : ∀ n, z n ≠ 0)
    (hsum : Summable fun n => ‖z n‖ ^ (-2 : ℝ)) (s : ℂ) :
    Summable fun n => 1 / (s - z n) + 1 / z n := by
  refine (hsum.mul_left (2 * ‖s‖)).of_norm_bounded_eventually ?_
  filter_upwards [eventually_le_norm_of_summable_norm_rpow_neg_two hz0 hsum
    (R := 2 * ‖s‖ + 1) (by positivity)] with n hn
  have hzn : 0 < ‖z n‖ := by linarith [norm_nonneg s]
  have hz0 : z n ≠ 0 := norm_pos_iff.mp hzn
  have hsz : ‖z n‖ / 2 ≤ ‖s - z n‖ := by
    have := norm_sub_norm_le (z n) s
    rw [norm_sub_rev] at this
    linarith
  have hzs : s - z n ≠ 0 := by
    intro h; rw [h, norm_zero] at hsz; linarith
  have hrw : 1 / (s - z n) + 1 / z n = s / ((s - z n) * z n) := by
    field_simp [hzs, hz0]; ring
  rw [hrw, norm_div, norm_mul, rpow_neg_two_eq, div_le_iff₀ (mul_pos (norm_pos_iff.mpr hzs) hzn)]
  calc ‖s‖ = 2 * ‖s‖ * (1 / ‖z n‖ ^ 2) * ((‖z n‖ / 2) * ‖z n‖) := by
        field_simp
    _ ≤ 2 * ‖s‖ * (1 / ‖z n‖ ^ 2) * (‖s - z n‖ * ‖z n‖) := by gcongr

end PairedSum

/-! ### Hadamard products -/

section Hadamard

variable {ι : Type*} {z : ι → ℂ} {f : ℂ → ℂ} {A B : ℂ}

/-- The constant of a Hadamard product: if
`f s = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)`, then `exp A = f 0`. -/
theorem exp_eq_apply_zero_of_eq_exp_mul_tprod
    (hAB : ∀ s, f s = exp (A + B * s) * ∏' n, (1 - s / z n) * exp (s / z n)) :
    exp A = f 0 := by
  rw [hAB 0]
  simp

/-- `‖(1 - w) eʷ - 1‖ ≤ 3 ‖w‖²` for `‖w‖ ≤ 1`. -/
private lemma norm_one_sub_mul_exp_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 - w) * exp w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have h1 := norm_exp_sub_one_sub_id_le hw
  have h2 := norm_exp_sub_one_le hw
  have : (1 - w) * exp w - 1 = (exp w - 1 - w) - w * (exp w - 1) := by ring
  rw [this]
  calc _ ≤ ‖exp w - 1 - w‖ + ‖w * (exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by rw [norm_mul]; gcongr
    _ = 3 * ‖w‖ ^ 2 := by ring

/-- **The logarithmic derivative of a Hadamard product.** If
`f s = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)` with `zₙ ≠ 0`, `∑ ‖zₙ‖⁻² < ∞` and every `zₙ`
a zero of `f`, then at every `s` with `f s ≠ 0`,
`f'(s) / f(s) = B + ∑ₙ (1 / (s - zₙ) + 1 / zₙ)`. -/
theorem logDeriv_eq_add_tsum_of_eq_exp_mul_tprod (hz0 : ∀ n, z n ≠ 0)
    (hsum : Summable fun n => ‖z n‖ ^ (-2 : ℝ))
    (hAB : ∀ s, f s = exp (A + B * s) * ∏' n, (1 - s / z n) * exp (s / z n))
    (hzero : ∀ n, f (z n) = 0) {s : ℂ} (hd : DifferentiableAt ℂ f s) (hfs : f s ≠ 0) :
    logDeriv f s = B + ∑' n, (1 / (s - z n) + 1 / z n) := by
  set P : ℂ → ℂ := fun w => ∏' n, (1 - w / z n) * exp (w / z n) with hP
  have hm := summable_one_div_sub_add_one_div hz0 hsum s
  have hxi : f = fun w => exp (A + B * w) * P w := funext hAB
  have hPs : P s ≠ 0 := by
    intro h; apply hfs; rw [hxi]; simp only [h, mul_zero]
  have hPd : DifferentiableAt ℂ P s := by
    have : P = fun w => f w / exp (A + B * w) := by
      funext w; rw [hAB w, mul_div_cancel_left₀ _ (exp_ne_zero _)]
    rw [this]; exact hd.div (by fun_prop) (exp_ne_zero _)
  have hL3 : logDeriv f s = B + logDeriv P s := by
    rw [hxi, logDeriv_fun_mul (f := fun w => exp (A + B * w)) (g := P) s
      (exp_ne_zero _) hPs (by fun_prop) hPd]
    congr 1
    have h3 : HasDerivAt (fun w => exp (A + B * w)) _ s :=
      (((hasDerivAt_id s).const_mul B).const_add A).cexp
    rw [logDeriv_apply, h3.deriv, id]
    field_simp [exp_ne_zero]
  have hzs : ∀ n, s - z n ≠ 0 := fun n h => hfs (by rw [sub_eq_zero.mp h]; exact hzero n)
  have hfac0 : ∀ n, 1 - s / z n ≠ 0 := fun n => by
    rw [one_sub_div (hz0 n)]
    exact div_ne_zero (by intro h; apply hzs n; linear_combination -h) (hz0 n)
  have hlogf : ∀ n, logDeriv (fun w => (1 - w / z n) * exp (w / z n)) s =
      1 / (s - z n) + 1 / z n := by
    intro n
    have h1 : HasDerivAt (fun w : ℂ => w / z n) (1 / z n) s := by
      simpa using (hasDerivAt_id s).div_const (z n)
    have h2 : HasDerivAt (fun w => (1 - w / z n) * exp (w / z n)) _ s :=
      (h1.const_sub 1).mul h1.cexp
    rw [logDeriv_apply, h2.deriv]
    have := hz0 n
    have := hzs n
    have := hfac0 n
    have : z n - s ≠ 0 := fun h => hzs n (by linear_combination -h)
    field_simp
    ring
  have htend : MultipliableLocallyUniformlyOn
      (fun n w => (1 - w / z n) * exp (w / z n)) (Metric.ball s 1) := by
    set R : ℝ := ‖s‖ + 1 with hR
    have h := Summable.multipliableLocallyUniformlyOn_one_add (K := Metric.ball s 1)
      (f := fun n w => (1 - w / z n) * exp (w / z n) - 1) Metric.isOpen_ball
      (hsum.mul_left (3 * R ^ 2)) (by
        filter_upwards [eventually_le_norm_of_summable_norm_rpow_neg_two hz0 hsum
          (R := R) (by positivity)] with n hn x hx
        have hzn : 0 < ‖z n‖ := norm_pos_iff.mpr (hz0 n)
        have hxR : ‖x‖ ≤ R := by
          rw [Metric.mem_ball, dist_eq_norm] at hx
          have := norm_le_norm_add_norm_sub' x s
          linarith
        have hw : ‖x / z n‖ ≤ 1 := by
          rw [norm_div, div_le_one hzn]; linarith
        calc ‖(1 - x / z n) * exp (x / z n) - 1‖ ≤ 3 * ‖x / z n‖ ^ 2 :=
              norm_one_sub_mul_exp_sub_one_le hw
          _ = 3 * ‖x‖ ^ 2 * ‖z n‖ ^ (-2 : ℝ) := by
            rw [rpow_neg_two_eq, norm_div, div_pow]; ring
          _ ≤ 3 * R ^ 2 * ‖z n‖ ^ (-2 : ℝ) := by gcongr)
      (fun n => by fun_prop)
    simpa using h
  have hL4 : logDeriv P s = ∑' n, (1 / (s - z n) + 1 / z n) := by
    have hf' : ∀ n, (1 - s / z n) * exp (s / z n) ≠ 0 :=
      fun n => mul_ne_zero (hfac0 n) (exp_ne_zero _)
    have hT := logDeriv_tendsto Metric.isOpen_ball (Metric.mem_ball_self one_pos)
      htend.hasProdLocallyUniformlyOn (.of_forall <| fun F => by fun_prop) hPs
    rw [eq_comm, ← hm.hasSum_iff]
    refine hT.congr fun F => ?_
    rw [logDeriv_fun_prod (fun i _ => hf' i) (fun i _ => by fun_prop)]
    exact Finset.sum_congr rfl fun n _ => hlogf n
  rw [hL3, hL4]

/-- A family listing the zeros of `f` with multiplicity consists of zeros of `f`. -/
theorem apply_eq_zero_of_card_eq_analyticOrderAt
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w) (n : ι) : f (z n) = 0 := by
  by_contra hne
  have h1 : analyticOrderAt f (z n) = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hne)
  have h2 := hz (z n)
  rw [h1] at h2
  exact (ENat.card_ne_zero_iff_nonempty _).mpr ⟨⟨n, rfl⟩⟩ h2

/-- For an entire `f` of order at most `1` with `f 0 ≠ 0`, a family listing its zeros with
multiplicity satisfies `∑ ‖zₙ‖⁻² < ∞`. -/
theorem summable_norm_rpow_neg_two_of_hasGrowthOrderLE_one (hd : Differentiable ℂ f)
    (h1 : HasGrowthOrderLE f 1) (hf0 : f 0 ≠ 0)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w) :
    Summable fun n => ‖z n‖ ^ (-2 : ℝ) := by
  have := h1.summable_norm_rpow_neg hd zero_le_one hf0 hz one_pos
  convert this using 3
  norm_num

/-- A finite genus-one Hadamard product `exp (A + B s) ∏ (1 - s / zₙ) exp (s / zₙ)` is of
exponential type. -/
theorem exists_norm_le_exp_of_eq_exp_mul_tprod [Finite ι]
    (hAB : ∀ s, f s = exp (A + B * s) * ∏' n, (1 - s / z n) * exp (s / z n)) :
    ∃ b : ℝ, ∀ s, ‖f s‖ ≤ Real.exp (‖A‖ + b * ‖s‖) := by
  have := Fintype.ofFinite ι
  refine ⟨‖B‖ + 2 * ∑ i, ‖z i‖⁻¹, fun s => ?_⟩
  rw [hAB s, tprod_fintype, norm_mul, norm_prod]
  have h1 : ‖exp (A + B * s)‖ ≤ Real.exp (‖A‖ + ‖B‖ * ‖s‖) := by
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    exact (norm_add_le _ _).trans (by rw [norm_mul])
  have h2 : ∀ i, ‖(1 - s / z i) * exp (s / z i)‖ ≤ Real.exp (2 * (‖s‖ * ‖z i‖⁻¹)) := by
    intro i
    have hn : ‖s / z i‖ = ‖s‖ * ‖z i‖⁻¹ := by rw [norm_div, div_eq_mul_inv]
    rw [norm_mul, two_mul, Real.exp_add]
    have ha : ‖1 - s / z i‖ ≤ Real.exp (‖s‖ * ‖z i‖⁻¹) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, hn]
      linarith [Real.add_one_le_exp (‖s‖ * ‖z i‖⁻¹)]
    have hb : ‖exp (s / z i)‖ ≤ Real.exp (‖s‖ * ‖z i‖⁻¹) := by
      rw [← hn]; exact norm_exp_le_exp_norm _
    exact mul_le_mul ha hb (norm_nonneg _) (Real.exp_pos _).le
  have h3 : ∏ i, ‖(1 - s / z i) * exp (s / z i)‖ ≤ Real.exp (∑ i, 2 * (‖s‖ * ‖z i‖⁻¹)) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h2 i)
  have h4 : ‖A‖ + (‖B‖ + 2 * ∑ i, ‖z i‖⁻¹) * ‖s‖ =
      (‖A‖ + ‖B‖ * ‖s‖) + ∑ i, 2 * (‖s‖ * ‖z i‖⁻¹) := by
    rw [add_mul, Finset.mul_sum, Finset.sum_mul, add_assoc]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4, Real.exp_add]
  exact mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le

/-- **An entire function of order at most `1` that is not of exponential type has infinitely
many zeros.** -/
theorem setOf_eq_zero_infinite_of_hasGrowthOrderLE_one (hd : Differentiable ℂ f)
    (h1 : HasGrowthOrderLE f 1) (hf0 : f 0 ≠ 0)
    (h : ∀ b : ℝ, ¬ f =O[cobounded ℂ] fun s => Real.exp (b * ‖s‖)) :
    {w | f w = 0}.Infinite := by
  intro hZ
  set N : ℂ → ℕ := fun w => (analyticOrderAt f w).toNat with hN
  have hz := card_sigma_fin_analyticOrderAt hd hf0
  -- the index type is finite
  set T : Set (ℂ × ℕ) := ⋃ w ∈ {w | f w = 0}, (fun m => (w, m)) '' Set.Iio (N w) with hT
  have hTfin : T.Finite := hZ.biUnion fun w _ => (Set.finite_Iio (N w)).image _
  have : Finite T := hTfin.to_subtype
  let g : (Σ w : ℂ, Fin (N w)) → T := fun n =>
    ⟨(n.1, (n.2 : ℕ)), by
      rw [hT, Set.mem_iUnion₂]
      exact ⟨n.1, apply_fst_eq_zero_of_sigma_fin_analyticOrderAt n, (n.2 : ℕ), n.2.2, rfl⟩⟩
  have hg : Function.Injective g := by
    rintro ⟨w, i⟩ ⟨w', j⟩ hij
    simp only [g, Subtype.mk.injEq, Prod.mk.injEq] at hij
    obtain ⟨rfl, h2⟩ := hij
    rw [Fin.ext h2]
  have : Finite (Σ w : ℂ, Fin (N w)) := Finite.of_injective g hg
  obtain ⟨A, B, hAB⟩ := exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one hd h1 hf0 hz
  obtain ⟨b, hb⟩ := exists_norm_le_exp_of_eq_exp_mul_tprod hAB
  refine h b (IsBigO.of_bound (Real.exp ‖A‖) (Eventually.of_forall fun s => ?_))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  exact hb s

open ComplexConjugate in
/-- **The real parts of the reciprocal zeros of a symmetric Hadamard product.** Let `f` be entire
of order at most `1` with `f 0 ≠ 0`, with zeros `zₙ` (listed with multiplicity) in the strip
`0 ≤ Re s ≤ 1`, satisfying `f s = ε conj (f (1 - conj s))` for some constant `ε`. If
`f s = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)`, then `∑ₙ Re (1 / zₙ) = -Re B`. -/
theorem hasSum_re_one_div_of_eq_exp_mul_tprod (hd : Differentiable ℂ f)
    (h1 : HasGrowthOrderLE f 1) (hf0 : f 0 ≠ 0)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt f w) {ε : ℂ}
    (hsym : ∀ s, f s = ε * conj (f (1 - conj s)))
    (hstrip : ∀ w, f w = 0 → 0 ≤ w.re ∧ w.re ≤ 1)
    (hAB : ∀ s, f s = exp (A + B * s) * ∏' n, (1 - s / z n) * exp (s / z n)) :
    HasSum (fun n => (1 / z n).re) (-B.re) := by
  classical
  have hF0 : f 0 = ε * conj (f 1) := by rw [hsym 0]; simp
  have hε0 : ε ≠ 0 := by rintro h; apply hf0; rw [hF0, h, zero_mul]
  have hf1 : f 1 ≠ 0 := by
    intro h; apply hf0; rw [hF0, h, map_zero, mul_zero]
  -- `f'(0) / f(0) = -conj (f'(1) / f(1))`
  have hD0 : HasDerivAt f (-(ε * conj (deriv f 1))) 0 := by
    have h1' : HasDerivAt (fun s => conj (f (conj s))) (conj (deriv f 1)) 1 := by
      have := (hd (conj 1)).hasDerivAt.conj_conj
      simp only [map_one] at this
      exact this
    have h2 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have h3 := (h1'.comp_of_eq (0 : ℂ) h2 (by simp)).const_mul ε
    refine (h3.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [Function.comp]
      rw [hsym s, map_sub, map_one]
    · ring
  have hlog01 : deriv f 0 / f 0 = -conj (deriv f 1 / f 1) := by
    rw [hD0.deriv, hF0, map_div₀]
    field_simp
  -- the log-derivative of the product
  have hzero := apply_eq_zero_of_card_eq_analyticOrderAt hz
  have hz0 : ∀ n, z n ≠ 0 := fun n h => hf0 (h ▸ hzero n)
  have hsum := summable_norm_rpow_neg_two_of_hasGrowthOrderLE_one hd h1 hf0 hz
  have hLD : ∀ s, f s ≠ 0 → logDeriv f s = B + ∑' n, (1 / (s - z n) + 1 / z n) :=
    fun s hs => logDeriv_eq_add_tsum_of_eq_exp_mul_tprod hz0 hsum hAB hzero (hd s) hs
  have hB0 : deriv f 0 / f 0 = B := by
    rw [← logDeriv_apply, hLD 0 hf0]
    simp
  set S := ∑' n, (1 / (1 - z n) + 1 / z n) with hS
  have hB1 : deriv f 1 / f 1 = B + S := by rw [← logDeriv_apply, hLD 1 hf1]
  have hBre : 2 * B.re = -S.re := by
    have := congrArg re (hlog01.trans (by rw [hB1]))
    rw [hB0] at this
    simp at this
    linarith
  -- the order of vanishing is invariant under `w ↦ 1 - conj w`
  have hord1 : ∀ w (k : ℕ), (k : ℕ∞) ≤ analyticOrderAt f w →
      (k : ℕ∞) ≤ analyticOrderAt f (1 - conj w) := by
    intro w k hk
    obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt (hd.analyticAt w)).mp hk
    have hcont : Tendsto (fun s : ℂ => 1 - conj s) (𝓝 (1 - conj w)) (𝓝 w) := by
      have := ((continuous_const (y := (1 : ℂ))).sub continuous_conj).tendsto (1 - conj w)
      simp only [Pi.sub_apply, map_sub, map_one, conj_conj, sub_sub_cancel] at this
      exact this
    refine (natCast_le_analyticOrderAt (hd.analyticAt _)).mpr
      ⟨fun s => ε * (-1) ^ k * conj (g (1 - conj s)), ?_, ?_⟩
    · rw [analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hcont.eventually hg.eventually_analyticAt] with s hs
      refine DifferentiableAt.const_mul ?_ _
      have h1' : DifferentiableAt ℂ (fun t : ℂ => g (1 - t)) (conj s) :=
        hs.differentiableAt.comp _ (differentiableAt_id.const_sub 1)
      have := h1'.conj_conj
      rw [conj_conj] at this
      exact this
    · filter_upwards [hcont.eventually hfg] with s hs
      rw [hsym s, hs, smul_eq_mul, map_mul, map_pow, map_sub, map_sub, map_one, conj_conj]
      have : (1 - s - conj w) = -(s - (1 - conj w)) := by ring
      rw [this, neg_pow, smul_eq_mul]
      ring
  have hord : ∀ w, analyticOrderAt f (1 - conj w) = analyticOrderAt f w := by
    intro w
    refine le_antisymm (ENat.forall_natCast_le_iff_le.mp fun k hk => ?_)
      (ENat.forall_natCast_le_iff_le.mp fun k hk => hord1 w k hk)
    have := hord1 _ k hk
    rwa [map_sub, map_one, conj_conj, sub_sub_cancel] at this
  -- hence a permutation `e` of the zeros with `z (e n) = 1 - conj (z n)`
  set z' : ι → ℂ := fun n => 1 - conj (z n) with hz'
  have hfin : ∀ w, Finite {n // z n = w} := fun w =>
    (finite_setOf_eq_of_summable_norm_rpow_neg_two hz0 hsum w).to_subtype
  have E : ∀ w, {n // z' n = w} ≃ {n // z n = w} := by
    intro w
    refine (Equiv.subtypeEquivRight (q := fun n => z n = 1 - conj w) fun n => ?_).trans ?_
    · change 1 - conj (z n) = w ↔ z n = 1 - conj w
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    · haveI := hfin w
      haveI := hfin (1 - conj w)
      have hc : Nat.card {n // z n = 1 - conj w} = Nat.card {n // z n = w} := by
        have := (hz _).trans ((hord w).trans (hz w).symm)
        rw [ENat.card_eq_coe_natCard, ENat.card_eq_coe_natCard] at this
        exact_mod_cast this
      exact (Finite.card_eq.mp hc).some
  set e : ι ≃ ι := (Equiv.sigmaFiberEquiv z').symm.trans
    ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv z)) with he_def
  have hze : ∀ n, z (e n) = z' n := fun n => (E (z' n) ⟨n, rfl⟩).2
  -- the sums
  have hsumRe : Summable fun n => (1 / z n).re := by
    refine Summable.of_norm_bounded hsum (fun n => ?_)
    have hn : 0 < normSq (z n) := normSq_pos.mpr (hz0 n)
    have hs := hstrip _ (hzero n)
    rw [Real.norm_eq_abs, one_div, inv_re, abs_div, abs_of_nonneg hn.le, rpow_neg_two_eq,
      normSq_eq_norm_sq, ← normSq_eq_norm_sq, div_eq_mul_inv, one_div]
    have : |(z n).re| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
    exact mul_le_of_le_one_left (by positivity) this
  set T := ∑' n, (1 / z n).re with hT_def
  have hT : HasSum (fun n => (1 / z n).re) T := hsumRe.hasSum
  have hT' : HasSum (fun n => (1 / (1 - z n)).re) T := by
    have : (fun n => (1 / (1 - z n)).re) = (fun n => (1 / z n).re) ∘ e := by
      funext n
      simp only [Function.comp, hze, hz']
      rw [← conj_re, map_div₀, map_one, map_sub, map_one]
    rw [this]
    exact e.hasSum_iff.mpr hT
  have hSre : HasSum (fun n => (1 / (1 - z n)).re + (1 / z n).re) S.re := by
    have h := reCLM.hasSum (summable_one_div_sub_add_one_div hz0 hsum 1).hasSum
    simpa [hS] using h
  have h2 : S.re = T + T := hSre.unique (hT'.add hT)
  convert hT using 1
  linarith

end Hadamard

end Complex
