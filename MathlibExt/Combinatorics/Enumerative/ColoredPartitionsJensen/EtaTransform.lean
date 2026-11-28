/-
Copyright (c) 2026 Sky (GitHub: ChironTheCentaur). All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Sky (GitHub: ChironTheCentaur)

Adapted from `PartitionsJensen/EtaTransform.lean` of
https://github.com/ChironTheCentaur/rh-lab-partitions-jensen at commit
57beb8dbff7b84e125931fe2e53080f325f4f108.
-/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# the partition generating function under `τ ↦ 4π²/τ` (from Mathlib's η)

`eulerP q = ∏_{n ≥ 1} (1 − q^n)` and `partGen q = 1 / eulerP q`, the generating function of the
partition
numbers. From Mathlib's `η(−1/z) = (√I)⁻¹ √z η(z)` (`ModularForm.eta_comp_eq_csqrt_I_inv`, constant
pinned)
at `z = iτ/2π`:

* `partGen_transform`: for `Re τ > 0`,
  `F(e^{−τ}) = (τ/2π)^{1/2} e^{π²/(6τ) − τ/24} F(e^{−4π²/τ})` (principal power, no unknown
constant);
* `norm_partGen_sub_one_le`: `‖F(q) − 1‖ ≤ 4‖q‖` for `‖q‖ ≤ 1/8`;
* `partGen_main`: for `Re τ > 0`, `Re(4π²/τ) ≥ 3`,
  `F(e^{−τ}) = (τ/2π)^{1/2} e^{π²/(6τ) − τ/24} (1 + E)`, `‖E‖ ≤ 4 e^{−Re(4π²/τ)}`;
* `partGen_cone`: in the cone `|Im τ| ≤ M Re τ`, `Re τ ≤ 4π²/(3(1+M²))`,
`‖E‖ ≤ 4 e^{−4π²/((1+M²) Re τ)}`;
* `partGen_real`: for `0 < y ≤ 1`, `F(e^{−y}) = exp(π²/(6y) + ½ log(y/2π) − y/24 + e)` with
`|e| ≤ 8 e^{−4π²/y}`;
* `partGen_pow_main`: the `r`-th power form used by the circle method.
-/

noncomputable section

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

open Complex ModularForm Filter Topology
open scoped Real

/-- Euler's product `∏_{n ≥ 1} (1 − q^n)`. -/
def eulerP (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

/-- The partition generating function `∏_{n ≥ 1} (1 − q^n)⁻¹ = 1 / eulerP q`. -/
def partGen (q : ℂ) : ℂ := (eulerP q)⁻¹

lemma summable_norm_pow_succ {q : ℂ} (hq : ‖q‖ < 1) : Summable fun n : ℕ ↦ ‖-q ^ (n + 1)‖ := by
  simpa [norm_pow] using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg
      q) hq)

lemma eulerP_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : eulerP q ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ ↦ -q ^ (n + 1)) (R := ℂ) ?_
    (summable_norm_pow_succ hq)
  · simpa [eulerP, sub_eq_add_neg] using h
  · intro n h0
    have h1 : q ^ (n + 1) = 1 := by linear_combination -h0
    have : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero n)
    simp [h1] at this

lemma partGen_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : partGen q ≠ 0 := inv_ne_zero (eulerP_ne_zero hq)

/- `η z = e^{2πiz/24} · eulerP (e^{2πiz})`. -/
private lemma eta_eq_eulerP (z : ℂ) : η z = cexp (2 * π * I * z / 24) * eulerP
    (cexp (2 * π * I * z)) := by
  simp only [ModularForm.eta, eulerP, Function.Periodic.qParam, eta_q_eq_pow]
  norm_num

/- `√(I w) = √I · √w` for `Re w > 0` (principal powers). -/
private lemma cpow_half_I_mul {w : ℂ} (hw : 0 < w.re) :
    (I * w) ^ (2⁻¹ : ℂ) = I ^ (2⁻¹ : ℂ) * w ^ (2⁻¹ : ℂ) := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  have harg : |arg w| < π / 2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  rw [cpow_def_of_ne_zero (mul_ne_zero I_ne_zero hw0), cpow_def_of_ne_zero I_ne_zero,
    cpow_def_of_ne_zero hw0, ← Complex.exp_add,
    log_mul I_ne_zero hw0 ?_]
  · ring_nf
  · rw [arg_I]
    have := abs_lt.1 harg
    constructor <;> linarith [Real.pi_pos]

/- **The transformation.** For `Re τ > 0`,
`F(e^{−τ}) = (τ/2π)^{1/2} e^{π²/(6τ) − τ/24} F(e^{−4π²/τ})`. -/
private theorem partGen_transform {τ : ℂ} (hτ : 0 < τ.re) :
    partGen (cexp (-τ)) =
      (τ / (2 * π)) ^ (2⁻¹ : ℂ) * cexp (π ^ 2 / (6 * τ) - τ / 24) * partGen (cexp (-(4 * π ^ 2 /
          τ))) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hτ0 : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  set z : ℂ := I * (τ / (2 * π)) with hz
  have hwre : 0 < (τ / (2 * π)).re := by
    rw [div_re]
    have : ((2 : ℂ) * π).re = 2 * π := by simp
    have h2 : ((2 : ℂ) * π).im = 0 := by simp
    rw [this, h2]
    have : normSq ((2 : ℂ) * π) = (2 * π) ^ 2 := by rw [normSq_apply]; simp; ring
    rw [this]
    have := Real.pi_pos
    simp only [mul_zero, zero_div, add_zero]
    positivity
  have hzim : 0 < z.im := by simpa [hz] using hwre
  have h := eta_comp_eq_csqrt_I_inv (show z ∈ {w : ℂ | 0 < w.im} from hzim)
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have e1 : 2 * π * I * z = -τ := by
    rw [hz]; field_simp; rw [I_sq]
  have e2 : 2 * π * I * (-1 / z) = -(4 * π ^ 2 / τ) := by
    rw [hz]; field_simp; norm_num
  rw [eta_eq_eulerP, eta_eq_eulerP, e1, e2] at h
  rw [show Complex.sqrt z = z ^ (2⁻¹ : ℂ) from rfl, hz, cpow_half_I_mul hwre] at h
  have hsI : I ^ (2⁻¹ : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp
  have hq1 : ‖cexp (-τ)‖ < 1 := by
    rw [norm_exp]; simpa using hτ
  have hdre : 0 < (4 * π ^ 2 / τ).re := by
    have : (4 * π ^ 2 / τ : ℂ) = ((4 * π ^ 2 : ℝ) : ℂ) * τ⁻¹ := by push_cast; ring
    rw [this, re_ofReal_mul, inv_re]
    have : 0 < normSq τ := normSq_pos.2 hτ0
    have := Real.pi_pos
    positivity
  have hq2 : ‖cexp (-(4 * π ^ 2 / τ))‖ < 1 := by
    rw [norm_exp]; simpa using hdre
  have hP1 := eulerP_ne_zero hq1
  have hP2 := eulerP_ne_zero hq2
  have ex : cexp (π ^ 2 / (6 * τ) - τ / 24) * cexp (-(4 * π ^ 2 / τ) / 24) = cexp (-τ / 24) := by
    rw [← Complex.exp_add]; congr 1; field_simp; ring
  rw [← ex, show Complex.sqrt I = I ^ (2⁻¹ : ℂ) from rfl] at h
  have hE : cexp (π ^ 2 / (6 * τ) - τ / 24) ≠ 0 := Complex.exp_ne_zero _
  have hE2 : cexp (-(4 * π ^ 2 / τ) / 24) ≠ 0 := Complex.exp_ne_zero _
  have h' : eulerP (cexp (-(4 * π ^ 2 / τ))) =
      (τ / (2 * π)) ^ (2⁻¹ : ℂ) * cexp (π ^ 2 / (6 * τ) - τ / 24) * eulerP (cexp (-τ)) := by
    apply mul_left_cancel₀ hE2
    rw [h]; field_simp
  simp only [partGen]
  rw [h']
  have hw : (τ / (2 * π)) ^ (2⁻¹ : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp [hτ0, hπ]
  generalize (τ / (2 * π)) ^ (2⁻¹ : ℂ) = w at hw ⊢
  generalize cexp (π ^ 2 / (6 * τ) - τ / 24) = E at hE ⊢
  field_simp

/-! ### The dual factor is `1 + O(‖q‖)` -/

lemma tsum_norm_pow_succ {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' n : ℕ, ‖-q ^ (n + 1)‖ = ‖q‖ * (1 - ‖q‖)⁻¹ := by
  simp only [norm_neg, pow_succ', norm_mul, norm_pow]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg q) hq]

lemma exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : 0 < 1 - x := by linarith
  rw [Real.exp_neg] at h1
  have := Real.exp_pos x
  rw [le_inv_comm₀ this h2]; exact h1

lemma norm_eulerP_sub_one_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖eulerP q - 1‖ ≤ Real.exp (2 * ‖q‖) - 1 := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hs := summable_norm_pow_succ hq1
  have hmul : Multipliable fun n : ℕ ↦ 1 + -q ^ (n + 1) := multipliable_one_add_of_summable hs
  have ht : Tendsto (fun n : ℕ ↦ ∏ i ∈ Finset.range n, (1 + -q ^ (i + 1))) atTop (𝓝 (eulerP q)) :=
      by
    have := hmul.hasProd.tendsto_prod_nat
    simpa [eulerP, sub_eq_add_neg] using this
  have hsum : ∑' n : ℕ, ‖-q ^ (n + 1)‖ ≤ 2 * ‖q‖ := by
    rw [tsum_norm_pow_succ hq1]
    have h0 : 0 < 1 - ‖q‖ := by linarith
    have : (1 - ‖q‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ h0 two_pos]; linarith
    nlinarith [norm_nonneg q]
  refine le_of_tendsto ((continuous_norm.tendsto _).comp (ht.sub_const 1))
    (Eventually.of_forall fun n ↦ ?_)
  calc ‖∏ i ∈ Finset.range n, (1 + -q ^ (i + 1)) - 1‖
      ≤ Real.exp (∑ i ∈ Finset.range n, ‖-q ^ (i + 1)‖) - 1 :=
        (Finset.range n).norm_prod_one_add_sub_one_le _
    _ ≤ Real.exp (2 * ‖q‖) - 1 := by
        gcongr
        exact (hs.sum_le_tsum _ (fun _ _ ↦ norm_nonneg _)).trans hsum

/- **Tail bound.** `‖F(q) − 1‖ ≤ 4‖q‖` for `‖q‖ ≤ 1/8`. -/
private theorem norm_partGen_sub_one_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 8) : ‖partGen q - 1‖ ≤ 4 * ‖q‖ := by
  have hr := norm_nonneg q
  set D := eulerP q - 1 with hD
  have hD1 : ‖D‖ ≤ 8 / 3 * ‖q‖ := by
    have h1 := norm_eulerP_sub_one_le (q := q) (by linarith)
    have h2 := exp_le_inv_one_sub (x := 2 * ‖q‖) (by linarith)
    have h3 : (1 - 2 * ‖q‖)⁻¹ - 1 ≤ 8 / 3 * ‖q‖ := by
      have h0 : 0 < 1 - 2 * ‖q‖ := by linarith
      rw [inv_eq_one_div, div_sub_one h0.ne', div_le_iff₀ h0]
      nlinarith
    linarith
  have hDs : ‖D‖ ≤ 1 / 3 := by linarith
  have hP : eulerP q = 1 + D := by rw [hD]; ring
  have hlow : 2 / 3 ≤ ‖1 + D‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-D)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hne : (1 + D) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  have : partGen q - 1 = -D / (1 + D) := by
    rw [partGen, hP]; field_simp; ring
  rw [this, norm_div, norm_neg, div_le_iff₀ (by linarith)]
  nlinarith

/- For `Re τ > 0` and `Re(4π²/τ) ≥ 3`: `F(e^{−τ}) = (τ/2π)^{1/2} e^{π²/(6τ) − τ/24} (1 + E)` with
`‖E‖ ≤ 4 e^{−Re(4π²/τ)}`. -/
private theorem partGen_main {τ : ℂ} (hτ : 0 < τ.re) (hd : 3 ≤ (4 * π ^ 2 / τ).re) :
    ∃ E : ℂ, ‖E‖ ≤ 4 * Real.exp (-(4 * π ^ 2 / τ).re) ∧
      partGen (cexp (-τ)) = (τ / (2 * π)) ^ (2⁻¹ : ℂ) * cexp (π ^ 2 / (6 * τ) - τ / 24) *
          (1 + E) := by
  refine ⟨partGen (cexp (-(4 * π ^ 2 / τ))) - 1, ?_, ?_⟩
  · have hn : ‖cexp (-(4 * π ^ 2 / τ))‖ = Real.exp (-(4 * π ^ 2 / τ).re) := by
      rw [norm_exp, neg_re]
    rw [← hn]
    apply norm_partGen_sub_one_le
    rw [hn]
    have h3 : Real.exp (-(4 * π ^ 2 / τ).re) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
    have h8 : Real.exp (-3) ≤ 1 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
      have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc ((1 : ℝ) / 8)⁻¹ = 2 ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := by gcongr
    linarith
  · rw [partGen_transform hτ]; ring

/- `Re(4π²/τ) ≥ 4π²/((1+M²) Re τ)` in the cone `|Im τ| ≤ M Re τ`. -/
private lemma re_dual_ge {M : ℝ} {τ : ℂ} (hτ : 0 < τ.re) (hcone : |τ.im| ≤ M * τ.re) :
    4 * π ^ 2 / ((1 + M ^ 2) * τ.re) ≤ (4 * π ^ 2 / τ).re := by
  have hτ0 : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hN : 0 < normSq τ := normSq_pos.2 hτ0
  have : (4 * π ^ 2 / τ : ℂ) = ((4 * π ^ 2 : ℝ) : ℂ) * τ⁻¹ := by push_cast; ring
  rw [this, re_ofReal_mul, inv_re, normSq_apply]
  have hy : τ.im * τ.im ≤ M ^ 2 * τ.re ^ 2 := by
    have h0 : 0 ≤ |τ.im| := abs_nonneg _
    have := mul_le_mul hcone hcone h0 (le_trans h0 hcone)
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)] at this
    nlinarith
  have hπ := Real.pi_pos
  have hpos : 0 < τ.re * τ.re + τ.im * τ.im := by nlinarith
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hpos]
  nlinarith [sq_nonneg τ.re, mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) (pow_pos hπ 2)) hτ]

/-- **Cone bound** (major arc of the circle method): for `Re τ > 0`, `|Im τ| ≤ M Re τ` and
`Re τ ≤ 4π²/(3(1+M²))`,
`F(e^{−τ}) = (τ/2π)^{1/2} e^{π²/(6τ) − τ/24}(1 + E)`, `‖E‖ ≤ 4 e^{−4π²/((1+M²) Re τ)}`. -/
theorem partGen_cone {M : ℝ} {τ : ℂ} (hτ : 0 < τ.re) (hcone : |τ.im| ≤ M * τ.re)
    (hsmall : τ.re ≤ 4 * π ^ 2 / (3 * (1 + M ^ 2))) :
    ∃ E : ℂ, ‖E‖ ≤ 4 * Real.exp (-(4 * π ^ 2 / ((1 + M ^ 2) * τ.re))) ∧
      partGen (cexp (-τ)) = (τ / (2 * π)) ^ (2⁻¹ : ℂ) * cexp (π ^ 2 / (6 * τ) - τ / 24) *
          (1 + E) := by
  have key := re_dual_ge hτ hcone
  have hM : 0 < 1 + M ^ 2 := by positivity
  have h3 : 3 ≤ 4 * π ^ 2 / ((1 + M ^ 2) * τ.re) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hsmall
    linarith
  obtain ⟨E, hE, hF⟩ := partGen_main hτ (h3.trans key)
  refine ⟨E, hE.trans ?_, hF⟩
  gcongr

/-- If `F(e^{−τ}) = (τ/2π)^{1/2} e^{π²/(6τ) − τ/24} (1 + E)`, then
`F(e^{−τ})^r = (τ/2π)^{r/2} e^{r(π²/(6τ) − τ/24)} (1 + E)^r`. -/
theorem partGen_pow_eq (r : ℕ) {τ E : ℂ}
    (hF : partGen (cexp (-τ)) =
      (τ / (2 * π)) ^ (2⁻¹ : ℂ) * cexp (π ^ 2 / (6 * τ) - τ / 24) * (1 + E)) :
    partGen (cexp (-τ)) ^ r =
      (τ / (2 * π)) ^ ((r : ℂ) / 2) * cexp (r * (π ^ 2 / (6 * τ) - τ / 24)) * (1 + E) ^ r := by
  rw [hF, mul_pow, mul_pow, Complex.exp_nat_mul, div_eq_mul_inv (r : ℂ), cpow_nat_mul]

/-! ### Real argument -/

/- On `[0, 1)`, `F` is a positive real number. -/
private lemma partGen_ofReal {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : ∃ p : ℝ, 0 < p ∧ partGen
    (x : ℂ) = p := by
  have hs : Summable fun n : ℕ ↦ ‖-x ^ (n + 1)‖ := by
    simpa [norm_pow, Real.norm_eq_abs, abs_of_nonneg h0] using
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one h0 h1)
  have hpos : ∀ n : ℕ, 0 < 1 + -x ^ (n + 1) := fun n ↦ by
    have : x ^ (n + 1) < 1 := pow_lt_one₀ h0 h1 (Nat.succ_ne_zero n)
    linarith
  have hmul : Multipliable fun n : ℕ ↦ 1 + -x ^ (n + 1) := multipliable_one_add_of_summable hs
  have hlog : Summable fun n : ℕ ↦ Real.log (1 + -x ^ (n + 1)) := by
    have := Summable.summable_log_norm_one_add (f := fun n : ℕ ↦ -x ^ (n + 1)) hs
    refine this.congr fun n ↦ ?_
    rw [Real.norm_eq_abs, abs_of_pos (hpos n)]
  set P : ℝ := ∏' n : ℕ, (1 + -x ^ (n + 1)) with hP
  have hPpos : 0 < P := by
    rw [hP, ← Real.rexp_tsum_eq_tprod hpos hlog]; exact Real.exp_pos _
  have hmap := hmul.hasProd.map Complex.ofRealHom continuous_ofReal
  have hC : eulerP (x : ℂ) = (P : ℂ) := by
    rw [eulerP]
    refine HasProd.tprod_eq ?_
    convert hmap using 1
    funext n; simp [sub_eq_add_neg]
  exact ⟨P⁻¹, inv_pos.2 hPpos, by rw [partGen, hC, ofReal_inv]⟩

lemma abs_log_le_two_mul {p : ℝ} (hp : 1 / 2 ≤ p) : |Real.log p| ≤ 2 * |p - 1| := by
  have hp0 : 0 < p := by linarith
  have hu := Real.log_le_sub_one_of_pos hp0
  have hl : 1 - p⁻¹ ≤ Real.log p := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hp0)
    rw [Real.log_inv] at this; linarith
  have hl' : -(2 * |p - 1|) ≤ 1 - p⁻¹ := by
    have : 1 - p⁻¹ = (p - 1) / p := by field_simp
    rw [this]
    rcases le_or_gt 1 p with h | h
    · have : 0 ≤ (p - 1) / p := div_nonneg (by linarith) hp0.le
      linarith [abs_nonneg (p - 1)]
    · rw [abs_of_neg (by linarith : p - 1 < 0), le_div_iff₀ hp0]
      nlinarith
  rw [abs_le]; constructor <;> [linarith; linarith [le_abs_self (p - 1)]]

/-- **Real bound.** For `0 < y ≤ 1`, `F(e^{−y}) = exp(π²/(6y) + ½ log(y/2π) − y/24 + e)`,
`|e| ≤ 8 e^{−4π²/y}`. -/
theorem partGen_real {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∃ e : ℝ, |e| ≤ 8 * Real.exp (-(4 * π ^ 2 / y)) ∧
      partGen (cexp (-(y : ℂ))) =
        (Real.exp (π ^ 2 / (6 * y) + 1 / 2 * Real.log (y / (2 * π)) - y / 24 + e) : ℝ) := by
  have hπ := Real.pi_pos
  have hd : (4 * π ^ 2 / (y : ℂ)).re = 4 * π ^ 2 / y := by
    rw [show (4 * π ^ 2 / (y : ℂ)) = ((4 * π ^ 2 / y : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have hbig : 3 ≤ 4 * π ^ 2 / y := by
    rw [le_div_iff₀ hy]; nlinarith [Real.two_le_pi]
  have hq : cexp (-(4 * π ^ 2 / (y : ℂ))) = ((Real.exp (-(4 * π ^ 2 / y)) : ℝ) : ℂ) := by
    rw [ofReal_exp]; push_cast; ring_nf
  have hx1 : Real.exp (-(4 * π ^ 2 / y)) < 1 := Real.exp_lt_one_iff.2 (by
    have : 0 < 4 * π ^ 2 / y := by positivity
    linarith)
  obtain ⟨p, hp, hpF⟩ := partGen_ofReal (Real.exp_pos _).le hx1
  -- `p` is within `4 e^{−4π²/y}` of `1`
  have hsmall : Real.exp (-(4 * π ^ 2 / y)) ≤ 1 / 8 := by
    have h3 : Real.exp (-(4 * π ^ 2 / y)) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
    have h8 : Real.exp (-3) ≤ 1 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
      have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc ((1 : ℝ) / 8)⁻¹ = 2 ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := by gcongr
    linarith
  have hp1 : |p - 1| ≤ 4 * Real.exp (-(4 * π ^ 2 / y)) := by
    have := norm_partGen_sub_one_le (q := ((Real.exp (-(4 * π ^ 2 / y)) : ℝ) : ℂ))
      (by rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hsmall)
    rw [hpF, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at this
    exact this
  have hphalf : 1 / 2 ≤ p := by
    have := (abs_le.1 (hp1.trans (by linarith : 4 * Real.exp (-(4 * π ^ 2 / y)) ≤ 1 / 2))).1
    linarith
  refine ⟨Real.log p, (abs_log_le_two_mul hphalf).trans (by linarith), ?_⟩
  have hT := partGen_transform (τ := (y : ℂ)) (by simpa using hy)
  rw [hT, hq, hpF]
  have hw : ((y : ℂ) / (2 * π)) ^ (2⁻¹ : ℂ) = ((Real.exp (1 / 2 * Real.log (y / (2 * π))) : ℝ) :
      ℂ) := by
    have hyπ : 0 < y / (2 * π) := by positivity
    rw [show ((y : ℂ) / (2 * π)) = ((y / (2 * π) : ℝ) : ℂ) by push_cast; ring,
      show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hyπ.le,
      Real.rpow_def_of_pos hyπ]
    congr 2; ring
  have he : cexp (π ^ 2 / (6 * (y : ℂ)) - y / 24) = ((Real.exp (π ^ 2 / (6 * y) - y / 24)) : ℝ) :=
      by
    rw [ofReal_exp]; push_cast; ring_nf
  rw [hw, he, ← ofReal_mul, ← ofReal_mul]
  congr 1
  rw [← Real.exp_log hp, ← Real.exp_add, ← Real.exp_add, Real.exp_log hp]
  congr 1; ring

end

end MetaMathlibExt.ColoredPartitionsJensen
