/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds

/-!
# Gaussian sums and a bound for the Riemann theta function

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), 89–140, proves in Lemma 2.4.2 (pp. 100–101), following an argument of R. de Jong,
a bound for the theta function of a curve. The analytic part of the proof bounds the Riemann theta
function `ϑ(z; τ)` by a Gaussian sum over `ℤ^g`, splits that sum into one-variable Gaussian sums,
bounds each of them and finishes with a numerical inequality; the arithmetic part averages the
resulting bounds over the complex embeddings. This file proves these steps:

* `Javanpeykar.exp_mul_norm_riemannTheta_le`: the theta series majorant, the inequality after
  equation (6), p. 100;
* `Javanpeykar.tsum_exp_neg_sum_mul_add_sq`: the product formula for `g`-variable Gaussian sums,
  used in the second inequality of the display on p. 101;
* `Javanpeykar.tsum_exp_neg_pi_mul_add_sq_le`: the bound
  `∑ₙ exp(-πt(n + b)²) ≤ 2 / (1 - exp(-πt)) ≤ 2(1 + 1/(πt))` behind the last two inequalities of
  the display on p. 101;
* `Javanpeykar.two_pow_mul_one_add_pow_le`: the numerical bound
  `2^g (1 + 2/(π√3 c(g)))^g ≤ 2^(3g³+5g)`, equation (6), p. 100;
* `Javanpeykar.average_le_of_le_of_average_le`: the averaging step "Combining (5) with the upper
  bound (6) implies the result", p. 100.

The Riemann theta function is `Javanpeykar.riemannTheta`, the series
`∑_{n ∈ ℤ^g} exp(π i ᵗn τ n + 2π i ᵗn z)` of Javanpeykar's §2.1 (p. 94).
-/

@[expose] public section

namespace Javanpeykar

open Real Matrix Finset

/-! ### One-variable Gaussian sums -/

private theorem summable_exp_neg_pi_mul_add_sq {t : ℝ} (ht : 0 < t) (b : ℝ) :
    Summable fun n : ℤ => Real.exp (-π * t * (n + b) ^ 2) := by
  refine (HurwitzKernelBounds.summable_f_int 0 b ht).congr fun n => ?_
  simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
  congr 1
  ring

private theorem summable_exp_neg_mul_add_sq {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Summable fun n : ℤ => Real.exp (-a * (n + b) ^ 2) := by
  refine (summable_exp_neg_pi_mul_add_sq (div_pos ha pi_pos) b).congr fun n => ?_
  congr 1
  field_simp

private theorem tsum_exp_neg_pi_mul_add_sq_le_of_mem_Icc {t : ℝ} (ht : 0 < t) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ∑' n : ℤ, Real.exp (-π * t * (n + a) ^ 2) ≤ 2 / (1 - Real.exp (-π * t)) := by
  have hF : ∑' n : ℤ, Real.exp (-π * t * (n + a) ^ 2) = HurwitzKernelBounds.F_int 0 a t := by
    simp only [HurwitzKernelBounds.F_int, Function.Periodic.lift_coe, HurwitzKernelBounds.f_int,
      pow_zero, one_mul]
    congr 1
    ext n
    congr 1
    ring
  rw [hF, HurwitzKernelBounds.F_int_eq_of_mem_Icc 0 ha ht]
  have hd : 0 < 1 - Real.exp (-π * t) := by
    have h := Real.exp_lt_exp.mpr (show -π * t < 0 by nlinarith [pi_pos])
    rw [Real.exp_zero] at h
    linarith
  have b1 := (le_abs_self _).trans (HurwitzKernelBounds.F_nat_zero_le ha.1 ht)
  have b2 := (le_abs_self _).trans (HurwitzKernelBounds.F_nat_zero_le (sub_nonneg.mpr ha.2) ht)
  have e1 : Real.exp (-π * a ^ 2 * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have := mul_nonneg (mul_nonneg pi_pos.le (sq_nonneg a)) ht.le
      linarith)
  have e2 : Real.exp (-π * (1 - a) ^ 2 * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have := mul_nonneg (mul_nonneg pi_pos.le (sq_nonneg (1 - a))) ht.le
      linarith)
  have h1 : Real.exp (-π * a ^ 2 * t) / (1 - Real.exp (-π * t)) ≤ 1 / (1 - Real.exp (-π * t)) :=
    div_le_div_of_nonneg_right e1 hd.le
  have h2 : Real.exp (-π * (1 - a) ^ 2 * t) / (1 - Real.exp (-π * t)) ≤
      1 / (1 - Real.exp (-π * t)) :=
    div_le_div_of_nonneg_right e2 hd.le
  have : 2 / (1 - Real.exp (-π * t)) = 1 / (1 - Real.exp (-π * t)) + 1 / (1 - Real.exp (-π * t)) :=
    by ring
  linarith

private theorem two_div_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) :
    2 / (1 - Real.exp (-x)) ≤ 2 * (1 + 1 / x) := by
  set u := Real.exp (-x) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hux : u * Real.exp x = 1 := by rw [hu, ← Real.exp_add]; simp
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have hu1 : u * (1 + x) ≤ 1 := by nlinarith
  have hd : 0 < 1 - u := by nlinarith
  rw [div_le_iff₀ hd]
  have key : 0 ≤ (1 - u - x * u) / x := div_nonneg (by nlinarith) hx.le
  have : 2 * (1 + 1 / x) * (1 - u) = 2 + 2 * ((1 - u - x * u) / x) := by
    field_simp
    ring
  linarith

/-- **A bound for a one-variable Gaussian sum.** For real numbers `t > 0` and `b`,
`∑_{n ∈ ℤ} exp(-πt(n + b)²) ≤ 2 / (1 - exp(-πt)) ≤ 2(1 + 1/(πt))`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2, p. 101, the last two inequalities of the display, where it
is applied with `t = c(g) Im(τ)ᵢᵢ`. -/
theorem tsum_exp_neg_pi_mul_add_sq_le {t : ℝ} (ht : 0 < t) (b : ℝ) :
    ∑' n : ℤ, Real.exp (-π * t * (n + b) ^ 2) ≤ 2 / (1 - Real.exp (-π * t)) ∧
      2 / (1 - Real.exp (-π * t)) ≤ 2 * (1 + 1 / (π * t)) := by
  refine ⟨?_, by simpa [neg_mul] using two_div_one_sub_exp_neg_le (mul_pos pi_pos ht)⟩
  have hshift : ∑' n : ℤ, Real.exp (-π * t * (n + b) ^ 2) =
      ∑' n : ℤ, Real.exp (-π * t * (n + Int.fract b) ^ 2) := by
    rw [← (Equiv.addRight ⌊b⌋).tsum_eq (fun n : ℤ => Real.exp (-π * t * (n + Int.fract b) ^ 2))]
    congr 1
    ext n
    simp only [Equiv.coe_addRight, Int.cast_add, Int.fract]
    ring_nf
  rw [hshift]
  exact tsum_exp_neg_pi_mul_add_sq_le_of_mem_Icc ht ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩

/-! ### Products of one-variable sums -/

private theorem summable_prod_of_pos_aux :
    ∀ (g : ℕ) (f : Fin g → ℤ → ℝ), (∀ i n, 0 < f i n) → (∀ i, Summable (f i)) →
      Summable (fun n : Fin g → ℤ => ∏ i, f i (n i)) ∧
        ∑' n : Fin g → ℤ, ∏ i, f i (n i) = ∏ i, ∑' m, f i m
  | 0, f, _, _ => by
    refine ⟨(hasSum_fintype _).summable, ?_⟩
    simp
  | g + 1, f, hpos, hsum => by
    obtain ⟨ih1, ih2⟩ := summable_prod_of_pos_aux g (fun i => f i.succ) (fun i n => hpos _ n)
      (fun i => hsum _)
    let e := Fin.consEquiv (fun _ : Fin (g + 1) => ℤ)
    have hcomp : (fun n : Fin (g + 1) → ℤ => ∏ i, f i (n i)) ∘ e =
        fun p : ℤ × (Fin g → ℤ) => f 0 p.1 * ∏ i : Fin g, f i.succ (p.2 i) := by
      ext p
      simp [e, Fin.consEquiv, Fin.prod_univ_succ]
    have hn0 : Summable fun m => ‖f 0 m‖ :=
      (hsum 0).congr fun m => (Real.norm_of_nonneg (hpos 0 m).le).symm
    have hn1 : Summable fun n : Fin g → ℤ => ‖∏ i : Fin g, f i.succ (n i)‖ :=
      ih1.congr fun n => (Real.norm_of_nonneg (prod_nonneg fun i _ => (hpos _ _).le)).symm
    have hs : Summable ((fun n : Fin (g + 1) → ℤ => ∏ i, f i (n i)) ∘ e) := by
      rw [hcomp]
      exact summable_mul_of_summable_norm hn0 hn1
    refine ⟨(e.summable_iff).mp hs, ?_⟩
    rw [← e.tsum_eq, Fin.prod_univ_succ, ← ih2]
    change ∑' p, ((fun n : Fin (g + 1) → ℤ => ∏ i, f i (n i)) ∘ e) p = _
    rw [hcomp, tsum_mul_tsum_of_summable_norm hn0 hn1]

private theorem summable_prod_of_pos {g : ℕ} (f : Fin g → ℤ → ℝ) (hpos : ∀ i n, 0 < f i n)
    (hsum : ∀ i, Summable (f i)) : Summable fun n : Fin g → ℤ => ∏ i, f i (n i) :=
  (summable_prod_of_pos_aux g f hpos hsum).1

private theorem tsum_prod_eq_prod_tsum_of_pos {g : ℕ} (f : Fin g → ℤ → ℝ)
    (hpos : ∀ i n, 0 < f i n) :
    ∑' n : Fin g → ℤ, ∏ i, f i (n i) = ∏ i, ∑' m, f i m := by
  by_cases hsum : ∀ i, Summable (f i)
  · exact (summable_prod_of_pos_aux g f hpos hsum).2
  simp only [not_forall] at hsum
  obtain ⟨i, hi⟩ := hsum
  rw [prod_eq_zero (mem_univ i) (tsum_eq_zero_of_not_summable hi)]
  refine tsum_eq_zero_of_not_summable fun hS => hi ?_
  classical
  let φ : ℤ → Fin g → ℤ := fun m => Function.update (fun _ => 0) i m
  have hφ : Function.Injective φ := fun m m' h => by
    simpa [φ] using congrFun h i
  set C := ∏ j ∈ univ.erase i, f j 0
  have hC : C ≠ 0 := (prod_pos fun j _ => hpos j 0).ne'
  have hcomp : (fun n : Fin g → ℤ => ∏ j, f j (n j)) ∘ φ = fun m => f i m * C := by
    ext m
    simp only [Function.comp_apply, C]
    rw [← mul_prod_erase univ _ (mem_univ i)]
    congr 1
    · simp [φ]
    · refine prod_congr rfl fun j hj => ?_
      simp [φ, Function.update_of_ne (ne_of_mem_erase hj)]
  have := hS.comp_injective hφ
  rw [hcomp] at this
  exact (summable_mul_right_iff hC).mp this

/-- **A product of one-variable Gaussian sums.** For real numbers `a₁, …, a_g` and
`b ∈ ℝ^g`,
`∑_{n ∈ ℤ^g} exp(-∑ᵢ aᵢ(nᵢ + bᵢ)²) = ∏ᵢ ∑_{nᵢ ∈ ℤ} exp(-aᵢ(nᵢ + bᵢ)²)`.
When every `aᵢ > 0` all the series converge (`Javanpeykar.summable_exp_neg_sum_mul_add_sq`); the
identity, as stated here for the values Lean assigns to series, needs no sign condition on the
`aᵢ` (if some series diverges, both sides are `0`).

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2, p. 101, the second inequality of the display, used with
`aᵢ = π c(g) Im(τ)ᵢᵢ`. -/
theorem tsum_exp_neg_sum_mul_add_sq {g : ℕ} (a b : Fin g → ℝ) :
    ∑' n : Fin g → ℤ, Real.exp (-∑ i, a i * (n i + b i) ^ 2) =
      ∏ i, ∑' m : ℤ, Real.exp (-a i * (m + b i) ^ 2) := by
  have h : ∀ n : Fin g → ℤ, Real.exp (-∑ i, a i * (n i + b i) ^ 2) =
      ∏ i, Real.exp (-a i * (n i + b i) ^ 2) := fun n => by
    rw [← Real.exp_sum, ← sum_neg_distrib]
    simp [neg_mul]
  simp_rw [h]
  exact tsum_prod_eq_prod_tsum_of_pos (fun i m => Real.exp (-a i * (m + b i) ^ 2))
    fun _ _ => Real.exp_pos _

/-- For `a₁, …, a_g > 0` and `b ∈ ℝ^g`, the series `∑_{n ∈ ℤ^g} exp(-∑ᵢ aᵢ(nᵢ + bᵢ)²)`
converges. -/
theorem summable_exp_neg_sum_mul_add_sq {g : ℕ} {a : Fin g → ℝ} (ha : ∀ i, 0 < a i)
    (b : Fin g → ℝ) :
    Summable fun n : Fin g → ℤ => Real.exp (-∑ i, a i * (n i + b i) ^ 2) := by
  have h : ∀ n : Fin g → ℤ, Real.exp (-∑ i, a i * (n i + b i) ^ 2) =
      ∏ i, Real.exp (-a i * (n i + b i) ^ 2) := fun n => by
    rw [← Real.exp_sum, ← sum_neg_distrib]
    simp [neg_mul]
  simp_rw [h]
  exact summable_prod_of_pos (fun i m => Real.exp (-a i * (m + b i) ^ 2))
    (fun _ _ => Real.exp_pos _) fun i => summable_exp_neg_mul_add_sq (ha i) (b i)

/-! ### The numerical bound -/

private theorem cube_le_four_pow : ∀ g : ℕ, g ^ 3 ≤ 4 ^ g
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | g + 3 => by
    have ih := cube_le_four_pow (g + 2)
    have h : (g + 3) ^ 3 ≤ 4 * (g + 2) ^ 3 := by
      have e : 4 * (g + 2) ^ 3 = (g + 3) ^ 3 + (3 * g ^ 3 + 15 * g ^ 2 + 21 * g + 5) := by ring
      rw [e]
      exact Nat.le_add_right _ _
    calc (g + 3) ^ 3 ≤ 4 * (g + 2) ^ 3 := h
      _ ≤ 4 * 4 ^ (g + 2) := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (g + 3) := by ring

/-- **A numerical bound for the theta function.** For every natural number `g`, with
`c(g) = (4/g³)^(g-1) (3/4)^(g(g-1)/2)`,
`2^g (1 + 2/(π√3 c(g)))^g ≤ 2^(3g³+5g)`.
Here `g - 1` and `g(g-1)/2` are computed in `ℕ`; for `g ≥ 1` they are the exponents of the
source (`g(g-1)` is even), and for `g = 0` both sides are `1`. The source has `g ≥ 1`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2: the bound `2^(3g³+5g)` of equation (6), p. 100, for the
last term `2^g (1 + 2/(π√3 c(g)))^g` of the display on p. 101, with `c(g)` as defined on p. 101. -/
theorem two_pow_mul_one_add_pow_le (g : ℕ) :
    (2 : ℝ) ^ g * (1 + 2 / (π * √3 *
        ((4 / (g : ℝ) ^ 3) ^ (g - 1) * (3 / 4 : ℝ) ^ (g * (g - 1) / 2)))) ^ g ≤
      (2 : ℝ) ^ (3 * g ^ 3 + 5 * g) := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  set x : ℝ := (g : ℝ) with hx
  set m : ℕ := g * (g - 1) / 2 with hm
  have hx0 : 0 < x := by rw [hx]; exact_mod_cast hg
  set c : ℝ := (4 / x ^ 3) ^ (g - 1) * (3 / 4 : ℝ) ^ m with hc
  set d : ℝ := (x ^ 3 / 4) ^ (g - 1) * (4 / 3 : ℝ) ^ m with hd
  have hc0 : 0 < c := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hcd : c * d = 1 := by
    rw [hc, hd, mul_mul_mul_comm, ← mul_pow, ← mul_pow]
    have h1 : 4 / x ^ 3 * (x ^ 3 / 4) = 1 := by field_simp
    norm_num [h1]
  -- `d ≤ 2^(3g²)`.
  have hcube : x ^ 3 ≤ (2 : ℝ) ^ (2 * g) := by
    rw [pow_mul]
    norm_num
    rw [hx]
    exact_mod_cast cube_le_four_pow g
  have hm_le : m ≤ g * (g - 1) := Nat.div_le_self _ _
  have hd_le : d ≤ (2 : ℝ) ^ (3 * g ^ 2) := by
    have h1 : (x ^ 3 / 4) ^ (g - 1) ≤ ((2 : ℝ) ^ (2 * g)) ^ (g - 1) :=
      pow_le_pow_left₀ (by positivity) ((div_le_self (by positivity) (by norm_num)).trans hcube) _
    have h2 : (4 / 3 : ℝ) ^ m ≤ (2 : ℝ) ^ (g * (g - 1)) :=
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (4 / 3 : ℝ) ≤ 2) m).trans
        (pow_le_pow_right₀ (by norm_num) hm_le)
    have h3 : d ≤ (2 : ℝ) ^ (2 * g * (g - 1) + g * (g - 1)) := by
      rw [hd, pow_add, pow_mul]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    refine h3.trans (pow_le_pow_right₀ (by norm_num) ?_)
    have : g - 1 ≤ g := Nat.sub_le g 1
    nlinarith [Nat.mul_le_mul_left g this]
  -- `2 / (π √3 c) ≤ d`.
  have hpi3 : 2 ≤ π * √3 := by
    have h3 : (1 : ℝ) ≤ √3 := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [Real.two_le_pi]
  have hterm : 2 / (π * √3 * c) ≤ d := by
    have hdc : d = 1 / c := by field_simp; linarith [hcd]
    rw [hdc, div_le_div_iff₀ (by positivity) hc0]
    nlinarith
  have hbase : 1 + 2 / (π * √3 * c) ≤ (2 : ℝ) ^ (3 * g ^ 2 + 1) := by
    have h1 : (1 : ℝ) ≤ 2 ^ (3 * g ^ 2) := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  calc (2 : ℝ) ^ g * (1 + 2 / (π * √3 * c)) ^ g
      ≤ (2 : ℝ) ^ g * ((2 : ℝ) ^ (3 * g ^ 2 + 1)) ^ g := by
        gcongr
    _ = (2 : ℝ) ^ (3 * g ^ 3 + 2 * g) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
    _ ≤ (2 : ℝ) ^ (3 * g ^ 3 + 5 * g) := pow_le_pow_right₀ (by norm_num) (by omega)

/-! ### The averaging step -/

/-- **Combining the bounds for the theta function.** Let `g` and `N` be natural numbers and `h`,
`L₁, …, L_N`, `D₁, …, D_N` real numbers such that `Lⱼ ≤ Dⱼ/4 + (3g³ + 5g) log 2` for each `j`
and `(1/N) ∑ⱼ Dⱼ ≤ g log max(1, h) + (2g³ + 2) log 2`. Then
`(1/N) ∑ⱼ Lⱼ ≤ (g/4) log max(1, h) + (4g³ + 5g + 1) log 2`.
The source has `g ≥ 1` and `N ≥ 1`; neither is needed (for `N = 0` both averages are `0`, as
`1/0 = 0` in Lean).

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2, p. 100 ("Combining (5) with the upper bound (6) implies
the result"), with `N = [K : ℚ]`, `j` running over the embeddings `σ : K → ℂ`,
`Lσ = log max ‖ϑ‖` on `Pic_{g-1}(X_σ)`, `Dσ = log det Im(τσ)` and `h = h_Fal(X)`. -/
theorem average_le_of_le_of_average_le (g N : ℕ) (h : ℝ) (L D : Fin N → ℝ)
    (hL : ∀ j, L j ≤ D j / 4 + (3 * (g : ℝ) ^ 3 + 5 * g) * Real.log 2)
    (hD : 1 / (N : ℝ) * ∑ j, D j ≤
      g * Real.log (max 1 h) + (2 * (g : ℝ) ^ 3 + 2) * Real.log 2) :
    1 / (N : ℝ) * ∑ j, L j ≤
      g / 4 * Real.log (max 1 h) + (4 * (g : ℝ) ^ 3 + 5 * g + 1) * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg3 : (0 : ℝ) ≤ (g : ℝ) ^ 3 := by positivity
  set C : ℝ := (3 * (g : ℝ) ^ 3 + 5 * g) * Real.log 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have havg : 1 / (N : ℝ) * ∑ j, L j ≤ 1 / 4 * (1 / (N : ℝ) * ∑ j, D j) + C := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [hC0]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hsum : ∑ j, L j ≤ ∑ j, (D j / 4 + C) := sum_le_sum fun j _ => hL j
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_div] at hsum
    have : 1 / (N : ℝ) * ∑ j, L j ≤ 1 / (N : ℝ) * ((∑ j, D j) / 4 + N * C) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    calc 1 / (N : ℝ) * ∑ j, L j ≤ 1 / (N : ℝ) * ((∑ j, D j) / 4 + N * C) := this
      _ = 1 / 4 * (1 / (N : ℝ) * ∑ j, D j) + C := by field_simp
  nlinarith

/-! ### The theta series majorant -/

/-- The Riemann theta function `ϑ(z; τ) = ∑_{n ∈ ℤ^g} exp(π i ᵗn τ n + 2π i ᵗn z)` of a
`g × g` complex matrix `τ` and `z ∈ ℂ^g`, as in A. Javanpeykar, *Polynomial bounds for Arakelov
invariants of Belyi curves*, Algebra Number Theory 8 (2014), §2.1, p. 94 (the value of a
divergent series being `0`). The series converges absolutely when `Im(τ)` is positive definite
(`Javanpeykar.summable_norm_riemannTheta_term`). -/
noncomputable def riemannTheta {g : ℕ} (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  ∑' n : Fin g → ℤ, Complex.exp (π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ))
    + 2 * π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z))

private theorem quadForm_smul {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (r : ℝ) (x : Fin g → ℝ) :
    (r • x) ⬝ᵥ Y *ᵥ (r • x) = r ^ 2 * (x ⬝ᵥ Y *ᵥ x) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

private theorem PosDef.exists_pos_mul_sum_sq_le {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ}
    (hY : Y.PosDef) :
    ∃ m > 0, ∀ x : Fin g → ℝ, m * ∑ i, x i ^ 2 ≤ x ⬝ᵥ Y *ᵥ x := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact ⟨1, one_pos, fun x => by simp⟩
  have : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  set Q : (Fin g → ℝ) → ℝ := fun x => x ⬝ᵥ Y *ᵥ x with hQ
  have hQc : Continuous Q := by
    simp only [hQ, dotProduct, mulVec]
    fun_prop
  obtain ⟨x₀, hx₀S, hx₀⟩ := (isCompact_sphere (0 : Fin g → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hQc.continuousOn
  have hx₀1 : ‖x₀‖ = 1 := by simpa using hx₀S
  have hx₀0 : x₀ ≠ 0 := by
    intro h
    simp [h] at hx₀1
  have hm0 : 0 < Q x₀ := by
    simpa [hQ] using hY.dotProduct_mulVec_pos hx₀0
  refine ⟨Q x₀ / g, div_pos hm0 (by exact_mod_cast hg), fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hS : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin g → ℝ) 1 := by
    simp [norm_smul, hn.ne']
  have hQx : Q x₀ ≤ Q (‖x‖⁻¹ • x) := hx₀ hS
  have hQs : Q (‖x‖⁻¹ • x) = (‖x‖⁻¹) ^ 2 * Q x := quadForm_smul Y _ x
  have hQge : Q x₀ * ‖x‖ ^ 2 ≤ Q x := by
    rw [hQs] at hQx
    have := mul_le_mul_of_nonneg_right hQx (sq_nonneg ‖x‖)
    calc Q x₀ * ‖x‖ ^ 2 ≤ (‖x‖⁻¹) ^ 2 * Q x * ‖x‖ ^ 2 := this
      _ = Q x := by field_simp
  have hsum : ∑ i, x i ^ 2 ≤ g * ‖x‖ ^ 2 := by
    calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin g, ‖x‖ ^ 2 := sum_le_sum fun i _ => by
          rw [← sq_abs, ← Real.norm_eq_abs]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
      _ = g * ‖x‖ ^ 2 := by simp
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  calc Q x₀ / g * ∑ i, x i ^ 2 ≤ Q x₀ / g * (g * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (div_pos hm0 hg').le
    _ = Q x₀ * ‖x‖ ^ 2 := by field_simp
    _ ≤ Q x := hQge

/-- For a positive-definite real `g × g` matrix `Y` and `b ∈ ℝ^g`, the series
`∑_{n ∈ ℤ^g} exp(-π ᵗ(n + b) Y (n + b))` converges. -/
theorem summable_exp_neg_pi_quadForm {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef)
    (b : Fin g → ℝ) :
    Summable fun n : Fin g → ℤ =>
      Real.exp (-π * ((fun i => (n i : ℝ) + b i) ⬝ᵥ Y *ᵥ fun i => (n i : ℝ) + b i)) := by
  obtain ⟨m, hm, hmY⟩ := PosDef.exists_pos_mul_sum_sq_le hY
  refine (summable_exp_neg_sum_mul_add_sq (a := fun _ => π * m) (fun _ => mul_pos pi_pos hm)
    b).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun n => Real.exp_le_exp.mpr ?_
  have := hmY fun i => (n i : ℝ) + b i
  rw [← mul_sum]
  nlinarith [pi_pos]

private theorem im_dotProduct_mulVec_ofReal {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (x : Fin g → ℝ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ)).im = x ⬝ᵥ (τ.map Complex.im) *ᵥ x := by
  simp only [dotProduct, mulVec, Complex.im_sum, Matrix.map_apply, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

private theorem im_dotProduct_ofReal {g : ℕ} (x : Fin g → ℝ) (z : Fin g → ℂ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ z).im = x ⬝ᵥ fun i => (z i).im := by
  simp [dotProduct, Complex.im_sum, Complex.mul_im]

/-- The norm of the `n`-th term of the theta series: for real `y = Im(z)` and `Y = Im(τ)`,
`‖exp(π i ᵗn τ n + 2π i ᵗn z)‖ = exp(-π ᵗn Y n - 2π ᵗn y)`. -/
private theorem norm_riemannTheta_term {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ)
    (n : Fin g → ℤ) :
    ‖Complex.exp (π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ))
      + 2 * π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z))‖ =
      Real.exp (-π * ((fun i => (n i : ℝ)) ⬝ᵥ (τ.map Complex.im) *ᵥ fun i => (n i : ℝ))
        - 2 * π * ((fun i => (n i : ℝ)) ⬝ᵥ fun i => (z i).im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h1 := im_dotProduct_mulVec_ofReal τ fun i => (n i : ℝ)
  have h2 := im_dotProduct_ofReal (fun i => (n i : ℝ)) z
  simp only [Complex.ofReal_intCast] at h1 h2
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, h1, h2]
  ring

/-- The `n`-th term of the theta series, multiplied by `exp(-π ᵗy Y⁻¹ y)`, has norm
`exp(-π ᵗ(n + b) Y (n + b))` when `Y b = y`. -/
private theorem exp_mul_norm_riemannTheta_term {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hY : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) (b : Fin g → ℝ)
    (hb : (τ.map Complex.im) *ᵥ b = fun i => (z i).im) (n : Fin g → ℤ) :
    Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ (τ.map Complex.im)⁻¹ *ᵥ fun i => (z i).im)) *
      ‖Complex.exp (π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ))
        + 2 * π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z))‖ =
      Real.exp (-π * ((fun i => (n i : ℝ) + b i) ⬝ᵥ
        (τ.map Complex.im) *ᵥ fun i => (n i : ℝ) + b i)) := by
  set Y := τ.map Complex.im with hYdef
  have hYt : Yᵀ = Y := by
    have := hY.1.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hinv : (fun i => (z i).im) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (z i).im) = b ⬝ᵥ Y *ᵥ b := by
    rw [← hb, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det Y).mp hY.isUnit),
      one_mulVec, dotProduct_comm]
  rw [norm_riemannTheta_term, ← Real.exp_add, hinv, ← hb]
  congr 1
  set N : Fin g → ℝ := fun i => (n i : ℝ)
  have hNb : (fun i => (n i : ℝ) + b i) = N + b := rfl
  have hsym : b ⬝ᵥ Y *ᵥ N = N ⬝ᵥ Y *ᵥ b := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hYt, dotProduct_comm]
  rw [hNb, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym]
  ring

private theorem summable_norm_riemannTheta_term_aux {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hY : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) (b : Fin g → ℝ)
    (hb : (τ.map Complex.im) *ᵥ b = fun i => (z i).im) :
    Summable fun n : Fin g → ℤ =>
      ‖Complex.exp (π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ))
        + 2 * π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z))‖ := by
  set q := (fun i => (z i).im) ⬝ᵥ (τ.map Complex.im)⁻¹ *ᵥ fun i => (z i).im
  refine (((summable_exp_neg_pi_quadForm hY b).mul_left (Real.exp (π * q)))).congr fun n => ?_
  rw [← exp_mul_norm_riemannTheta_term τ hY z b hb n, ← mul_assoc, ← Real.exp_add]
  simp [q]

/-- For `τ` with positive-definite imaginary part, the theta series converges absolutely. -/
theorem summable_norm_riemannTheta_term {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hY : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) :
    Summable fun n : Fin g → ℤ =>
      ‖Complex.exp (π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ))
        + 2 * π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z))‖ := by
  refine summable_norm_riemannTheta_term_aux τ hY z
    ((τ.map Complex.im)⁻¹ *ᵥ fun i => (z i).im) ?_
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hY.isUnit), one_mulVec]

/-- **A theta series majorant.** Let `τ` be a complex `g × g` matrix whose imaginary part
`Y = Im(τ)` is positive definite, let `z ∈ ℂ^g`, `y = Im(z)`, and let `b ∈ ℝ^g` with `Y b = y`
(that is, `b = Y⁻¹ y`). Then
`exp(-π ᵗy Y⁻¹ y) |ϑ(z; τ)| ≤ ∑_{n ∈ ℤ^g} exp(-π ᵗ(n + b) Y (n + b))`,
and the series on the right converges (`Javanpeykar.summable_exp_neg_pi_quadForm`).
The source takes `τ` symmetric; that is not needed here.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2, p. 100, the inequality after equation (6) (where the
exponent on the left is printed as `-π ᵗg (Im(τ))⁻¹ y`, with `ᵗg` standing for `ᵗy`), with `ϑ` as
in §2.1, p. 94. -/
theorem exp_mul_norm_riemannTheta_le {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hY : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) (b : Fin g → ℝ)
    (hb : (τ.map Complex.im) *ᵥ b = fun i => (z i).im) :
    Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ (τ.map Complex.im)⁻¹ *ᵥ fun i => (z i).im)) *
        ‖riemannTheta z τ‖ ≤
      ∑' n : Fin g → ℤ, Real.exp (-π * ((fun i => (n i : ℝ) + b i) ⬝ᵥ
        (τ.map Complex.im) *ᵥ fun i => (n i : ℝ) + b i)) := by
  calc _ ≤ Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ (τ.map Complex.im)⁻¹ *ᵥ fun i => (z i).im)) *
        ∑' n : Fin g → ℤ,
          ‖Complex.exp (π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ))
            + 2 * π * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z))‖ :=
        mul_le_mul_of_nonneg_left
          (norm_tsum_le_tsum_norm (summable_norm_riemannTheta_term_aux τ hY z b hb))
          (Real.exp_pos _).le
    _ = _ := by
        rw [← tsum_mul_left]
        exact tsum_congr (exp_mul_norm_riemannTheta_term τ hY z b hb)

end Javanpeykar
