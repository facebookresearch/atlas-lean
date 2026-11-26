/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumMeanSquare
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The Dirichlet series of powers of the mean gcd-sum function

For every natural number `k`, the Dirichlet series of the `k`-th power of the mean gcd-sum
function `A` is `ζ(s) ^ (2 ^ k) G_k(s)` for `Re s > 1`, where the Dirichlet series `G_k(s)`
converges absolutely for `Re s > 1/2`, and `G_k(s) ζ(2s) ^ (4 ^ k - 3 ^ k - (2 ^ k).choose 2)` is,
for `Re s > 1`, the sum of a Dirichlet series that converges absolutely for `Re s > 1/3`
(`LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul`). Datt, Soni and Sankaranarayanan attribute
this factorization to Isao Kiuchi and Yuki Tsuruta, *Mean Square Estimates for GCD-Sum
Functions*, INTEGERS 25 (2025), Article A53.

The proof takes for `G_k` the series of the Dirichlet convolution `μ ^ (2 ^ k) * A_k`, where
`A_k(n) = A(n) ^ k` and `μ ^ (2 ^ k)` is a convolution power of the Möbius function, and for the
second series that of `q ^ e * μ ^ (2 ^ k) * A_k`, where `q` is the indicator function of the
nonzero squares, whose series is `ζ(2s)`, and `e = 4 ^ k - 3 ^ k - (2 ^ k).choose 2`. Both
functions are multiplicative, so absolute convergence follows from bounds at prime powers: with
`u = 1/p`, the values at `p ^ m` grow polynomially in `m`, the value of the first at `p` is
`(2 - u) ^ k - 2 ^ k = O(u)`, and the value of the second at `p ^ 2` is
`(3 - 2u) ^ k - 3 ^ k - 2 ^ k ((2 - u) ^ k - 2 ^ k) = O(u)`, the constant terms cancelling
because `3 ^ k + (2 ^ k).choose 2 ≤ 4 ^ k`.
-/

namespace MetaMathlibExt.LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul

open ArithmeticFunction Complex
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ### The mean gcd-sum function at prime powers -/

/-- The `k`-th power of the mean gcd-sum function, as a complex arithmetic function. -/
private noncomputable def meanPow (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else ((gcdSumMean n ^ k : ℝ) : ℂ), ite_eq_left rfl⟩

private lemma meanPow_apply {k n : ℕ} (hn : n ≠ 0) :
    meanPow k n = ((gcdSumMean n ^ k : ℝ) : ℂ) :=
  ite_eq_right hn

private lemma meanPow_mult (k : ℕ) : (meanPow k).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn h => ?_⟩
  · simp [meanPow_apply one_ne_zero, gcdSumMean_one]
  · rw [meanPow_apply (mul_ne_zero hm hn), meanPow_apply hm, meanPow_apply hn,
      gcdSumMean_mul_of_coprime h, mul_pow, ofReal_mul]

private lemma meanPow_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    meanPow k (p ^ e) = (((1 + e * (1 - (p : ℝ)⁻¹)) ^ k : ℝ) : ℂ) := by
  rw [meanPow_apply (pow_ne_zero e hp.ne_zero), gcdSumMean_prime_pow hp]

private lemma meanPow_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    meanPow k p = (((2 - (p : ℝ)⁻¹) ^ k : ℝ) : ℂ) := by
  have h := meanPow_prime_pow k hp 1
  rw [pow_one] at h
  rw [h, show (1 : ℝ) + ((1 : ℕ) : ℝ) * (1 - (p : ℝ)⁻¹) = 2 - (p : ℝ)⁻¹ by push_cast; ring]

private lemma meanPow_prime_sq (k : ℕ) {p : ℕ} (hp : p.Prime) :
    meanPow k (p ^ 2) = (((3 - 2 * (p : ℝ)⁻¹) ^ k : ℝ) : ℂ) := by
  rw [meanPow_prime_pow k hp 2,
    show (1 : ℝ) + ((2 : ℕ) : ℝ) * (1 - (p : ℝ)⁻¹) = 3 - 2 * (p : ℝ)⁻¹ by push_cast; ring]

private lemma norm_meanPow_prime_pow_le (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ‖meanPow k (p ^ e)‖ ≤ ((e : ℝ) + 1) ^ k := by
  have hu₀ : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hu₁ : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  have h₀ : 0 ≤ 1 + e * (1 - (p : ℝ)⁻¹) := by
    have : 0 ≤ (e : ℝ) * (1 - (p : ℝ)⁻¹) := mul_nonneg (Nat.cast_nonneg e) (by linarith)
    linarith
  rw [meanPow_prime_pow k hp, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg h₀]
  apply pow_le_pow_left₀ h₀
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) e) hu₀]

/-! ### Dirichlet convolution at prime powers -/

private lemma mul_apply_prime_pow (F G : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (F * G) (p ^ m) = ∑ i ∈ Finset.range (m + 1), F (p ^ i) * G (p ^ (m - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => F a * G b),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hp.pos]

private lemma mul_apply_prime (F G : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) :
    (F * G) p = F 1 * G p + F p * G 1 := by
  simpa [Finset.sum_range_succ] using mul_apply_prime_pow F G hp 1

private lemma mul_apply_prime_sq (F G : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) :
    (F * G) (p ^ 2) = F 1 * G (p ^ 2) + F p * G p + F (p ^ 2) * G 1 := by
  simpa [Finset.sum_range_succ] using mul_apply_prime_pow F G hp 2

private lemma norm_mul_apply_prime_pow_le {X F : ArithmeticFunction ℂ} (hX : ∀ n, ‖X n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {D : ℕ} (hF : ∀ e : ℕ, ‖F (p ^ e)‖ ≤ ((e : ℝ) + 1) ^ D) (m : ℕ) :
    ‖(X * F) (p ^ m)‖ ≤ ((m : ℝ) + 1) ^ (D + 1) := by
  rw [mul_apply_prime_pow X F hp]
  calc ‖∑ i ∈ Finset.range (m + 1), X (p ^ i) * F (p ^ (m - i))‖
      ≤ ∑ i ∈ Finset.range (m + 1), ((m : ℝ) + 1) ^ D := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        calc ‖X (p ^ i)‖ * ‖F (p ^ (m - i))‖ ≤ 1 * (((m - i : ℕ) : ℝ) + 1) ^ D :=
              mul_le_mul (hX _) (hF _) (norm_nonneg _) zero_le_one
          _ ≤ ((m : ℝ) + 1) ^ D := by
              rw [one_mul]
              gcongr
              exact_mod_cast Nat.sub_le m i
    _ = ((m : ℝ) + 1) ^ (D + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
        push_cast
        ring

private lemma norm_pow_mul_apply_le {X F : ArithmeticFunction ℂ} (hX : ∀ n, ‖X n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {D : ℕ} (hF : ∀ e : ℕ, ‖F (p ^ e)‖ ≤ ((e : ℝ) + 1) ^ D) (i e : ℕ) :
    ‖(X ^ i * F) (p ^ e)‖ ≤ ((e : ℝ) + 1) ^ (D + i) := by
  induction i generalizing e with
  | zero => simpa using hF e
  | succ i ih =>
    rw [pow_succ', mul_assoc]
    exact norm_mul_apply_prime_pow_le hX hp ih e

/-! ### The Möbius function -/

private lemma norm_moebius_le (n : ℕ) : ‖(μ : ArithmeticFunction ℂ) n‖ ≤ 1 := by
  rw [intCoe_apply, norm_intCast]
  exact_mod_cast abs_moebius_le_one

private lemma moebius_pow_mul_apply {F : ArithmeticFunction ℂ} (hF : F.IsMultiplicative)
    {p : ℕ} (hp : p.Prime) (i : ℕ) :
    ((μ : ArithmeticFunction ℂ) ^ i * F) p = F p - i ∧
      ((μ : ArithmeticFunction ℂ) ^ i * F) (p ^ 2) = F (p ^ 2) - i * F p + (i.choose 2 : ℕ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : ((μ : ArithmeticFunction ℂ) ^ i * F) 1 = 1 :=
      (isMultiplicative_moebius.intCast.pow.mul hF).map_one
    have hμ1 : (μ : ArithmeticFunction ℂ) 1 = 1 := by simp [intCoe_apply]
    have hμp : (μ : ArithmeticFunction ℂ) p = -1 := by
      simp [intCoe_apply, moebius_apply_prime hp]
    have hμp2 : (μ : ArithmeticFunction ℂ) (p ^ 2) = 0 := by
      simp [intCoe_apply, moebius_apply_prime_pow hp two_ne_zero]
    rw [pow_succ', mul_assoc, mul_apply_prime _ _ hp, mul_apply_prime_sq _ _ hp, ih.1, ih.2, h1,
      hμ1, hμp, hμp2, Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    constructor <;> ring

/-! ### The indicator function of the squares -/

/-- The indicator function of the nonzero squares. -/
private noncomputable def sqInd : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≠ 0 ∧ IsSquare n then 1 else 0, by simp⟩

private lemma isSquare_mul_iff {m n : ℕ} (h : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  refine ⟨fun ⟨r, hr⟩ => ?_, fun ⟨hm, hn⟩ => hm.mul hn⟩
  have hmn : IsUnit (gcd m n) := Nat.isUnit_iff.mpr h
  have hnm : IsUnit (gcd n m) := Nat.isUnit_iff.mpr h.symm
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hmn (show m * n = r ^ 2 by rw [hr, sq])
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hnm (show n * m = r ^ 2 by rw [mul_comm, hr, sq])
  exact ⟨⟨a, by rw [ha, sq]⟩, ⟨b, by rw [hb, sq]⟩⟩

private lemma sqInd_mult : sqInd.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [sqInd], fun {m n} hm hn h => ?_⟩
  simp only [sqInd, coe_mk, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    isSquare_mul_iff h]
  by_cases hm' : IsSquare m <;> by_cases hn' : IsSquare n <;> simp [hm', hn']

private lemma sqInd_one : sqInd 1 = 1 := sqInd_mult.map_one

private lemma sqInd_apply_prime {p : ℕ} (hp : p.Prime) : sqInd p = 0 := by
  simp [sqInd, hp.prime.not_isSquare]

private lemma sqInd_apply_sq {p : ℕ} (hp : p.Prime) : sqInd (p ^ 2) = 1 := by
  simp [sqInd, hp.ne_zero, IsSquare.sq p]

private lemma norm_sqInd_le (n : ℕ) : ‖sqInd n‖ ≤ 1 := by
  simp only [sqInd, coe_mk]
  split_ifs <;> simp

private lemma sqInd_pow_mul_apply {F : ArithmeticFunction ℂ} (hF : F.IsMultiplicative)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (sqInd ^ j * F) p = F p ∧ (sqInd ^ j * F) (p ^ 2) = F (p ^ 2) + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (sqInd ^ j * F) 1 = 1 := (sqInd_mult.pow.mul hF).map_one
    rw [pow_succ', mul_assoc, mul_apply_prime _ _ hp, mul_apply_prime_sq _ _ hp, ih.1, ih.2, h1,
      sqInd_one, sqInd_apply_prime hp, sqInd_apply_sq hp]
    push_cast
    constructor <;> ring

private lemma sq_injective : Function.Injective (fun m : ℕ => m ^ 2) :=
  Nat.pow_left_injective two_ne_zero

private lemma term_sqInd_sq (s : ℂ) (m : ℕ) :
    LSeries.term sqInd s (m ^ 2) = LSeries.term 1 (2 * s) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    rw [LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm]
    simp only [sqInd, coe_mk, ne_eq, hm2, not_false_eq_true, true_and, IsSquare.sq m,
      ite_true, Pi.one_apply, Nat.cast_pow]
    rw [← natCast_cpow_natCast_mul]
    norm_num

private lemma term_sqInd_eq_zero (s : ℂ) {n : ℕ} (hn : n ∉ Set.range (fun m : ℕ => m ^ 2)) :
    LSeries.term sqInd s n = 0 := by
  have hsq : ¬ IsSquare n := fun ⟨r, hr⟩ => hn ⟨r, show r ^ 2 = n by rw [hr, sq]⟩
  rcases eq_or_ne n 0 with rfl | h0
  · rfl
  · rw [LSeries.term_of_ne_zero h0]
    simp [sqInd, hsq]

private lemma lseriesSummable_sqInd {s : ℂ} (hs : 1 < s.re) : LSeriesSummable sqInd s := by
  have h2s : 1 < (2 * s).re := by
    rw [two_mul, add_re]
    linarith
  have h1 : LSeriesSummable 1 (2 * s) := LSeriesSummable_one_iff.mpr h2s
  refine (sq_injective.summable_iff (f := LSeries.term sqInd s)
    fun n hn => term_sqInd_eq_zero s hn).mp ?_
  have hcomp : (LSeries.term sqInd s ∘ fun m : ℕ => m ^ 2) = LSeries.term 1 (2 * s) :=
    funext (term_sqInd_sq s)
  rw [hcomp]
  exact h1

private lemma lseries_sqInd {s : ℂ} (hs : 1 < s.re) : LSeries sqInd s = riemannZeta (2 * s) := by
  have h2s : 1 < (2 * s).re := by
    rw [two_mul, add_re]
    linarith
  rw [← LSeries_one_eq_riemannZeta h2s, LSeries, LSeries,
    ← sq_injective.tsum_eq (f := LSeries.term sqInd s)
      fun n hn => by_contra fun h => hn (term_sqInd_eq_zero s h)]
  simp [term_sqInd_sq]

/-! ### L-series of convolution powers -/

private lemma lseries_pow_mul {X F : ArithmeticFunction ℂ} {s : ℂ} (hX : LSeriesSummable X s)
    (hF : LSeriesSummable F s) (n : ℕ) :
    LSeriesSummable ⇑(X ^ n * F) s ∧ LSeries ⇑(X ^ n * F) s = LSeries X s ^ n * LSeries F s := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact ⟨hF, trivial⟩
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact ⟨LSeriesSummable_mul hX ih.1, by rw [LSeries_mul' hX ih.1, ih.2]; ring⟩

/-! ### Absolute convergence from bounds at prime powers -/

/-- A multiplicative function whose values at prime powers `p ^ e` grow polynomially in `e`, and
are `O(1/p)` for `0 < e < j`, has an absolutely convergent L-series for `Re s > 1/j`. -/
private lemma lseriesSummable_of_bound {F : ArithmeticFunction ℂ} (hF : F.IsMultiplicative)
    {j K : ℕ} {C : ℝ} (hC : 0 ≤ C) {s : ℂ} (hs : 1 < j * s.re)
    (hpoly : ∀ p e : ℕ, p.Prime → ‖F (p ^ e)‖ ≤ C * ((e : ℝ) + 1) ^ K)
    (hsmall : ∀ p e : ℕ, p.Prime → 0 < e → e < j → ‖F (p ^ e)‖ ≤ C * (p : ℝ)⁻¹) :
    LSeriesSummable F s := by
  have hσ : 0 < s.re := by
    by_contra h
    have : (j : ℝ) * s.re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j) (not_lt.mp h)
    linarith
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hσ
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (-s.re) := ⟨_, rfl⟩
  have hr₀ : 0 < r := by
    rw [hr]
    exact Real.rpow_pos_of_pos two_pos _
  have hr₁ : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hσ)
  have hb : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - s.re) + (n : ℝ) ^ (-(j * s.re))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).add (Real.summable_nat_rpow.mpr (by linarith))
  have hd : Summable (fun e : ℕ => C * ((e : ℝ) + 2) ^ K * r ^ e / r ^ j) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ K * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one K (by rw [Real.norm_of_nonneg hr₀.le]; exact hr₁)
    have h2 : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ K * r ^ (n + 2)) :=
      (summable_nat_add_iff 2).mpr h0
    have hr0 : r ≠ 0 := hr₀.ne'
    refine (h2.mul_left (C / r ^ j / r ^ 2)).congr fun e => ?_
    push_cast
    rw [pow_add]
    field_simp
  let w := riemannZetaSummandHom hs₀
  have hw : ArithmeticFunction.IsMultiplicative w.toZeroHom :=
    ⟨w.map_one, fun {m n} _ => w.map_mul m n⟩
  have hterm n : F.pmul w.toZeroHom n = LSeries.term F s n := by
    change F n * (n : ℂ) ^ (-s) = LSeries.term F s n
    rw [LSeries.term_of_ne_zero' hs₀, cpow_neg, div_eq_mul_inv]
  refine (summable_of_prime_power_bound (hF.pmul hw) hb hd (fun _ => by positivity)
    (fun _ => by positivity) fun p e hp => ?_).of_norm.congr hterm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (p : ℝ) ^ (-s.re) := ⟨_, rfl⟩
  have hy₀ : 0 < y := by
    rw [hy]
    exact Real.rpow_pos_of_pos hp0 _
  have hyr : y ≤ r := by
    rw [hy, hr]
    exact Real.rpow_le_rpow_of_nonpos two_pos (by exact_mod_cast hp.two_le) (by linarith)
  have hy₁ : y ≤ 1 := hyr.trans hr₁.le
  have hnorm : ‖F.pmul w.toZeroHom (p ^ (e + 1))‖ = ‖F (p ^ (e + 1))‖ * y ^ (e + 1) := by
    change ‖F _ * w (p ^ (e + 1))‖ = _
    rw [map_pow w, norm_mul, norm_pow]
    change _ * ‖(p : ℂ) ^ (-s)‖ ^ _ = _
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re, hy]
  have hb₁ : (p : ℝ) ^ (-1 - s.re) = (p : ℝ)⁻¹ * y := by
    rw [hy, sub_eq_add_neg, Real.rpow_add hp0, Real.rpow_neg_one]
  have hb₂ : (p : ℝ) ^ (-(j * s.re)) = y ^ j := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    ring_nf
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  rw [hnorm, hb₁, hb₂]
  rcases lt_or_ge (e + 1) j with he | he
  · have h1 := hsmall p (e + 1) hp e.succ_pos he
    have hde : C ≤ C * ((e : ℝ) + 2) ^ K * r ^ e / r ^ j := by
      rw [le_div_iff₀ (pow_pos hr₀ j), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC
      calc r ^ j ≤ r ^ e := pow_le_pow_of_le_one hr₀.le hr₁.le (by omega)
        _ ≤ ((e : ℝ) + 2) ^ K * r ^ e :=
          le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith))
    calc ‖F (p ^ (e + 1))‖ * y ^ (e + 1) ≤ (C * (p : ℝ)⁻¹) * y :=
          mul_le_mul h1 (pow_le_of_le_one hy₀.le hy₁ (by omega)) (by positivity) (by positivity)
      _ = ((p : ℝ)⁻¹ * y) * C := by ring
      _ ≤ ((p : ℝ)⁻¹ * y + y ^ j) * (C * ((e : ℝ) + 2) ^ K * r ^ e / r ^ j) := by
          apply mul_le_mul _ hde hC (by positivity)
          linarith [pow_pos hy₀ j]
  · have h1 := hpoly p (e + 1) hp
    have hy' : y ^ (e + 1) ≤ y ^ j * (r ^ e / r ^ j) := by
      obtain ⟨t, ht⟩ : ∃ t, e + 1 = j + t := ⟨e + 1 - j, by omega⟩
      rw [ht, pow_add]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ (pow_pos hr₀ j)]
      calc y ^ t * r ^ j ≤ r ^ t * r ^ j := by gcongr
        _ = r ^ (e + 1) := by rw [← pow_add, add_comm t j, ← ht]
        _ ≤ r ^ e := pow_le_pow_of_le_one hr₀.le hr₁.le (by omega)
    calc ‖F (p ^ (e + 1))‖ * y ^ (e + 1)
        ≤ (C * (((e + 1 : ℕ) : ℝ) + 1) ^ K) * (y ^ j * (r ^ e / r ^ j)) :=
          mul_le_mul h1 hy' (by positivity) (by positivity)
      _ = y ^ j * (C * ((e : ℝ) + 2) ^ K * r ^ e / r ^ j) := by
          push_cast
          ring
      _ ≤ ((p : ℝ)⁻¹ * y + y ^ j) * (C * ((e : ℝ) + 2) ^ K * r ^ e / r ^ j) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [mul_pos (inv_pos.mpr hp0) hy₀]

/-! ### Elementary estimates -/

private lemma abs_sub_pow_sub_pow_le {a t : ℝ} (ht₀ : 0 ≤ t) (hta : t ≤ a) (ha : a ≤ 4) (k : ℕ) :
    |(a - t) ^ k - a ^ k| ≤ t * k * 4 ^ k := by
  have h1 : |(a - t) - a| = t := by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg ht₀]
  have h2 : max |a - t| |a| ≤ 4 :=
    max_le (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by rw [abs_of_nonneg (by linarith)]; exact ha)
  calc |(a - t) ^ k - a ^ k| ≤ |(a - t) - a| * k * max |a - t| |a| ^ (k - 1) :=
        abs_pow_sub_pow_le _ _ _
    _ ≤ t * k * 4 ^ k := by
      rw [h1]
      gcongr
      calc max |a - t| |a| ^ (k - 1) ≤ 4 ^ (k - 1) :=
            pow_le_pow_left₀ (le_max_of_le_right (abs_nonneg _)) h2 _
        _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)

private lemma three_pow_add_choose_le (k : ℕ) : 3 ^ k + (2 ^ k).choose 2 ≤ 4 ^ k := by
  have h1 : 2 * 3 ^ k ≤ 4 ^ k + 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      have : 2 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
      rw [pow_succ, pow_succ, pow_succ]
      omega
  have h2 : 2 * (2 ^ k).choose 2 + 2 ^ k = 4 ^ k := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd,
      show 4 ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega))]
  omega

/-! ### The two correction series -/

/-- The Dirichlet convolution `μ ^ (2 ^ k) * A_k`, where `A_k(n) = A(n) ^ k`; its L-series is
`G_k`. -/
private noncomputable def gFun (k : ℕ) : ArithmeticFunction ℂ :=
  (μ : ArithmeticFunction ℂ) ^ (2 ^ k) * meanPow k

/-- The Dirichlet convolution `q ^ e * μ ^ (2 ^ k) * A_k`, where `q` is the indicator function of
the nonzero squares; its L-series is `G̃_{k,2}`. -/
private noncomputable def hFun (k : ℕ) : ArithmeticFunction ℂ :=
  sqInd ^ (4 ^ k - 3 ^ k - (2 ^ k).choose 2) * gFun k

private lemma gFun_mult (k : ℕ) : (gFun k).IsMultiplicative :=
  isMultiplicative_moebius.intCast.pow.mul (meanPow_mult k)

private lemma hFun_mult (k : ℕ) : (hFun k).IsMultiplicative :=
  sqInd_mult.pow.mul (gFun_mult k)

/-- The constant in the `O(1/p)` bounds. -/
private noncomputable def bound (k : ℕ) : ℝ := 3 * k * 8 ^ k + 1

private lemma one_le_bound (k : ℕ) : 1 ≤ bound k := by
  have : (0 : ℝ) ≤ 3 * k * 8 ^ k := by positivity
  simp only [bound]
  linarith

private lemma norm_gFun_prime_pow_le (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ‖gFun k (p ^ e)‖ ≤ ((e : ℝ) + 1) ^ (k + 2 ^ k) :=
  norm_pow_mul_apply_le norm_moebius_le hp (norm_meanPow_prime_pow_le k hp) _ e

private lemma norm_hFun_prime_pow_le (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ‖hFun k (p ^ e)‖ ≤ ((e : ℝ) + 1) ^ (k + 2 ^ k + (4 ^ k - 3 ^ k - (2 ^ k).choose 2)) :=
  norm_pow_mul_apply_le norm_sqInd_le hp (norm_gFun_prime_pow_le k hp) _ e

private lemma norm_gFun_prime_le (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ‖gFun k p‖ ≤ bound k * (p : ℝ)⁻¹ := by
  have hu₀ : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hu₁ : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  set u := (p : ℝ)⁻¹ with hu
  have hval : gFun k p = (((2 - u) ^ k - 2 ^ k : ℝ) : ℂ) := by
    rw [gFun, (moebius_pow_mul_apply (meanPow_mult k) hp _).1, meanPow_prime k hp, ← hu]
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  calc |(2 - u) ^ k - 2 ^ k| ≤ u * k * 4 ^ k :=
        abs_sub_pow_sub_pow_le hu₀ (by linarith) (by norm_num) k
    _ ≤ bound k * u := by
        have h48 : (4 : ℝ) ^ k ≤ 8 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
        simp only [bound]
        nlinarith [mul_nonneg hu₀ hk, mul_nonneg (mul_nonneg hu₀ hk) h4]

private lemma norm_hFun_prime_sq_le (k : ℕ) {p : ℕ} (hp : p.Prime) :
    ‖hFun k (p ^ 2)‖ ≤ bound k * (p : ℝ)⁻¹ := by
  have hu₀ : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hu₁ : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  set u := (p : ℝ)⁻¹ with hu
  have hEC : ((4 ^ k - 3 ^ k - (2 ^ k).choose 2 : ℕ) : ℂ) + ((2 ^ k).choose 2 : ℕ) =
      2 ^ k * 2 ^ k - 3 ^ k := by
    have h := three_pow_add_choose_le k
    rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [← mul_pow]
    norm_num
  have hval : hFun k (p ^ 2) =
      (((3 - 2 * u) ^ k - 3 ^ k : ℝ) : ℂ) - 2 ^ k * (((2 - u) ^ k - 2 ^ k : ℝ) : ℂ) := by
    rw [hFun, (sqInd_pow_mul_apply (gFun_mult k) hp _).2, gFun,
      (moebius_pow_mul_apply (meanPow_mult k) hp _).2, meanPow_prime k hp,
      meanPow_prime_sq k hp, ← hu]
    push_cast
    linear_combination hEC
  rw [hval]
  calc ‖(((3 - 2 * u) ^ k - 3 ^ k : ℝ) : ℂ) - 2 ^ k * (((2 - u) ^ k - 2 ^ k : ℝ) : ℂ)‖
      ≤ ‖(((3 - 2 * u) ^ k - 3 ^ k : ℝ) : ℂ)‖ +
          ‖(2 : ℂ) ^ k * (((2 - u) ^ k - 2 ^ k : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ = |(3 - 2 * u) ^ k - 3 ^ k| + 2 ^ k * |(2 - u) ^ k - 2 ^ k| := by
        rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, Complex.norm_ofNat]
    _ ≤ 2 * u * k * 4 ^ k + 2 ^ k * (u * k * 4 ^ k) := by
        gcongr
        · exact abs_sub_pow_sub_pow_le (by linarith) (by linarith) (by norm_num) k
        · exact abs_sub_pow_sub_pow_le hu₀ (by linarith) (by norm_num) k
    _ ≤ bound k * u := by
        have h48 : (4 : ℝ) ^ k ≤ 8 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
        have h28 : (2 : ℝ) ^ k * (u * k * 4 ^ k) = u * k * 8 ^ k := by
          rw [show (8 : ℝ) ^ k = 2 ^ k * 4 ^ k by rw [← mul_pow]; norm_num]
          ring
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
        rw [h28]
        simp only [bound]
        nlinarith [mul_nonneg hu₀ hk, mul_nonneg (mul_nonneg hu₀ hk) h4]

private lemma lseriesSummable_gFun (k : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (gFun k) s := by
  refine lseriesSummable_of_bound (gFun_mult k) (j := 2) (K := k + 2 ^ k)
    (zero_le_one.trans (one_le_bound k)) (by push_cast; linarith)
    (fun p e hp => ?_) (fun p e hp he₀ he₂ => ?_)
  · exact (norm_gFun_prime_pow_le k hp e).trans
      (le_mul_of_one_le_left (by positivity) (one_le_bound k))
  · obtain rfl : e = 1 := by omega
    rw [pow_one]
    exact norm_gFun_prime_le k hp

private lemma lseriesSummable_hFun (k : ℕ) {s : ℂ} (hs : 1 / 3 < s.re) :
    LSeriesSummable (hFun k) s := by
  refine lseriesSummable_of_bound (hFun_mult k) (j := 3)
    (K := k + 2 ^ k + (4 ^ k - 3 ^ k - (2 ^ k).choose 2))
    (zero_le_one.trans (one_le_bound k)) (by push_cast; linarith)
    (fun p e hp => ?_) (fun p e hp he₀ he₃ => ?_)
  · exact (norm_hFun_prime_pow_le k hp e).trans
      (le_mul_of_one_le_left (by positivity) (one_le_bound k))
  · interval_cases e
    · rw [pow_one, hFun, (sqInd_pow_mul_apply (gFun_mult k) hp _).1]
      exact norm_gFun_prime_le k hp
    · exact norm_hFun_prime_sq_le k hp

private lemma lseries_meanPow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((gcdSumMean n ^ k : ℝ) : ℂ)) s =
      riemannZeta s ^ (2 ^ k) * LSeries (gFun k) s := by
  have hζ : LSeriesSummable (ζ : ArithmeticFunction ℂ) s :=
    (LSeriesSummable_congr s fun _ => natCoe_apply).mpr (LSeriesSummable_zeta_iff.mpr hs)
  have hζL : LSeries (ζ : ArithmeticFunction ℂ) s = riemannZeta s := by
    rw [← LSeries_zeta_eq_riemannZeta hs]
    exact LSeries_congr (fun _ => natCoe_apply) s
  have hfG : meanPow k = (ζ : ArithmeticFunction ℂ) ^ (2 ^ k) * gFun k := by
    rw [gFun, ← mul_assoc, ← mul_pow, coe_zeta_mul_coe_moebius, one_pow, one_mul]
  have hL : LSeries (fun n => ((gcdSumMean n ^ k : ℝ) : ℂ)) s = LSeries (meanPow k) s :=
    LSeries_congr (fun hn => (meanPow_apply hn).symm) s
  rw [hL, hfG, (lseries_pow_mul hζ (lseriesSummable_gFun k (by linarith)) _).2, hζL]

private lemma lseries_gFun_mul (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (gFun k) s * riemannZeta (2 * s) ^ (4 ^ k - 3 ^ k - (2 ^ k).choose 2) =
      LSeries (hFun k) s := by
  rw [hFun, (lseries_pow_mul (lseriesSummable_sqInd hs)
    (lseriesSummable_gFun k (by linarith)) _).2, lseries_sqInd hs, mul_comm]

end MetaMathlibExt.LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul

namespace MetaMathlibExt

open LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul in
/-- **Factorization of the Dirichlet series of powers of the mean gcd-sum function.** Let $k$ be a
natural number and let $A$ be the mean gcd-sum function. There are functions
$g, h \colon \mathbb{N} \to \mathbb{C}$ such that the Dirichlet series
$G_k(s) = \sum_{n \ge 1} g(n) n^{-s}$ converges absolutely for every complex $s$ with
$\operatorname{Re} s > 1/2$, the Dirichlet series $\tilde G_{k,2}(s) = \sum_{n \ge 1} h(n) n^{-s}$
converges absolutely for every complex $s$ with $\operatorname{Re} s > 1/3$, and for every complex
$s$ with $\operatorname{Re} s > 1$,
$$\sum_{n \ge 1} A(n)^k n^{-s} = \zeta(s)^{2^k} G_k(s)$$
and
$$G_k(s) \, \zeta(2s)^{4^k - 3^k - \binom{2^k}{2}} = \tilde G_{k,2}(s).$$

The exponent $4^k - 3^k - \binom{2^k}{2}$ is a nonnegative integer, since
$3^k + \binom{2^k}{2} \le 4^k$. The paper also gives an explicit Euler product for
$\tilde G_{k,2}$, which is not stated here.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 8 (`integers-2026-A70-lem-8`). -/
public theorem LSeries_gcdSumMean_pow_eq_riemannZeta_pow_mul (k : ℕ) :
    ∃ g h : ℕ → ℂ, (∀ s : ℂ, 1 / 2 < s.re → LSeriesSummable g s) ∧
      (∀ s : ℂ, 1 / 3 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((gcdSumMean n ^ k : ℝ) : ℂ)) s = riemannZeta s ^ (2 ^ k) * LSeries g s ∧
        LSeries g s * riemannZeta (2 * s) ^ (4 ^ k - 3 ^ k - (2 ^ k).choose 2) = LSeries h s :=
  ⟨gFun k, hFun k, fun _ hs => lseriesSummable_gFun k hs, fun _ hs => lseriesSummable_hFun k hs,
    fun _ hs => ⟨lseries_meanPow k hs, lseries_gFun_mul k hs⟩⟩

end MetaMathlibExt
