/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.SumCoeff
import MathlibExt.NumberTheory.Amicable
import MathlibExt.NumberTheory.PollackPomeranceSieve

/-!
# Large values of the totient of the divisor sum

For a positive nondecreasing function `f` growing more slowly than the fourth iterated logarithm,
`card_totient_sigma_ge_div_isBigO` bounds the count of positive integers up to `x` satisfying
`φ(σ(n)) ≥ n / f(n)` and shows that this count is `o(x)`.

For each small prime `p ≡ 3 mod 4`, a character estimate gives a lower bound for the sum of
reciprocals of primes `r ≡ -1 mod p`. When such an `r` divides `n` exactly once,
`p` divides `σ(n)`. The Pollack–Pomerance sieve bounds the count of integers avoiding these
primes `r`, and summing over square divisors bounds the other exceptions. Outside the exceptional
set, the small prime divisors bound `φ(σ(n)) / σ(n)` from above. Summing `σ(n) / n` then gives
the counting bound.

## References

* A. B. Dixit and S. Bhattacharjee, *On the Distribution of φ(σ(n))*, INTEGERS 24 (2024),
  Article A65, Theorem 2 (Theorem 1.2 in [the preprint](https://arxiv.org/abs/2408.01936)).
* P. Pollack and C. Pomerance, *Phi, primorials, and Poisson*, Illinois J. Math. 64 (2020),
  319–330, Lemma 3 ([preprint](https://arxiv.org/abs/2001.06727)).
-/

open Filter Finset Complex MeasureTheory Asymptotics
open scoped Topology

noncomputable section

namespace MetaMathlibExt.card_totient_sigma_ge_div_isBigO

private lemma char_partial_sums {q : ℕ} [NeZero q] [Fact (1 < q)] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ Icc 1 n, χ k‖ ≤ q := by
  have hperiod (i j : ℕ) : χ (↑(q * i + j) : ZMod q) = χ j := by
    simp
  have hsum : ∑ k ∈ range q, χ k = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact (Fintype.sum_equiv (ZMod.finEquiv q) _ _ (by
      intro i
      apply congrArg (fun j : ZMod q => χ j)
      have hv : ((ZMod.finEquiv q) i).val = i.val := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
        rfl
      exact hv ▸ ZMod.natCast_zmod_val ((ZMod.finEquiv q) i))).trans
      (MulChar.sum_eq_zero_of_ne_one hχ)
  have hblocks (a : ℕ) : ∑ k ∈ range (q * a), χ k = 0 := by
    induction a with
    | zero => simp
    | succ a ih =>
      simp only [Nat.mul_succ, sum_range_add, ih, hperiod, hsum, add_zero]
  have heq : ∑ k ∈ Icc 1 n, χ k = ∑ k ∈ range (n + 1), χ k := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.cast_zero, MulChar.map_zero, add_zero, Nat.add_comm 1]
  rw [heq, ← Nat.div_add_mod (n + 1) q, sum_range_add, hblocks, zero_add]
  -- The shifted remainder has fewer than q terms, each of norm at most one.
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun i _ => χ.norm_le_one _)).trans (by
    simpa using (Nat.cast_le (α := ℝ)).mpr (Nat.mod_lt (n + 1) q.pos_of_neZero).le))

private lemma char_integral {q : ℕ} [NeZero q] [Fact (1 < q)] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℝ} (hs : 1 < s) :
    LSeries (fun n : ℕ => χ n) (s : ℂ) =
      ∫ t : ℝ in Set.Ioi 1,
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * ((s * t ^ (-(s + 1)) : ℝ) : ℂ) := by
  have hb : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] (fun n ↦ (n : ℝ) ^ (0 : ℝ)) :=
    Asymptotics.IsBigO.of_bound q (Eventually.of_forall fun n ↦
      by simpa using char_partial_sums χ hχ n)
  rw [LSeries_eq_mul_integral _ (r := 0) le_rfl (by simpa using zero_lt_one.trans hs)
    (χ.LSeriesSummable_of_one_lt_re (by simpa)) hb, ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := zero_le_one.trans (le_of_lt ht)
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0]
  push_cast
  ring

private lemma norm_char_series_le {q : ℕ} [NeZero q] [Fact (1 < q)] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℝ} (hs : 1 < s) :
    ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖ ≤ q := by
  rw [char_integral χ hχ hs]
  have hi := (integrableOn_Ioi_rpow_of_lt (show -(s + 1) < -1 by linarith)
    (show (0 : ℝ) < 1 by norm_num)).const_mul ((q : ℝ) * s)
  have hb := norm_integral_le_of_norm_le (f := fun t : ℝ =>
    (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * ((s * t ^ (-(s + 1)) : ℝ) : ℂ)) hi
    (ae_restrict_mem (μ := volume) measurableSet_Ioi |>.mono fun t ht => by
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [norm_mul, norm_real, Real.norm_of_nonneg (by positivity), mul_assoc]
      exact mul_le_mul_of_nonneg_right (char_partial_sums χ hχ _) (by positivity))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
    Real.one_rpow] at hb
  convert hb using 1
  field_simp [show s ≠ 0 by linarith]
  ring

private lemma norm_char_series_sub_le {q : ℕ} [NeZero q] [Fact (1 < q)]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s u : ℝ} (hs : 1 < s) (hsu : s ≤ u) :
    ‖LSeries (fun n : ℕ => χ n) (s : ℂ) - LSeries (fun n : ℕ => χ n) (u : ℂ)‖ ≤
      2 * q * (u - s) := by
  have hu := hs.trans_le hsu
  let A (c t : ℝ) := t ^ (-(c + 1))
  have hA {c : ℝ} (hc : 1 < c) : IntegrableOn (A c) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hval {c : ℝ} (hc : 1 < c) : ∫ t in Set.Ioi 1, A c t = c⁻¹ := by
    simp only [A, integral_Ioi_rpow_of_lt (show -(c + 1) < -1 by linarith) zero_lt_one,
      Real.one_rpow]
    rw [show -(c + 1) + 1 = -c by ring]
    simp
  let S (t : ℝ) : ℂ := ∑ k ∈ Icc 1 ⌊t⌋₊, χ k
  have hS : Measurable S := (Measurable.of_discrete : Measurable
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k)).comp Nat.measurable_floor
  have hkernel {c : ℝ} (hc : 1 < c) :
      IntegrableOn (fun t ↦ S t * ((c * A c t : ℝ) : ℂ)) (Set.Ioi 1) := by
    refine ((hA hc).const_mul ((q : ℝ) * c)).mono' ?_ ?_
    · exact (hS.mul (Complex.measurable_ofReal.comp
        (measurable_const.mul (measurable_id.pow_const _)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [norm_mul, norm_real, Real.norm_of_nonneg (by dsimp [A]; positivity), mul_assoc]
      exact mul_le_mul_of_nonneg_right (char_partial_sums χ hχ _) (by dsimp [A]; positivity)
  rw [char_integral χ hχ hs, char_integral χ hχ hu]
  change ‖(∫ t in Set.Ioi 1, S t * ((s * A s t : ℝ) : ℂ)) -
    (∫ t in Set.Ioi 1, S t * ((u * A u t : ℝ) : ℂ))‖ ≤ _
  rw [← integral_sub (hkernel hs) (hkernel hu)]
  have hupper := norm_integral_le_of_norm_le
    ((((hA hu).const_mul (u - s)).add (((hA hs).sub (hA hu)).const_mul s)).const_mul (q : ℝ))
    (f := fun t ↦ S t * ((s * A s t : ℝ) : ℂ) - S t * ((u * A u t : ℝ) : ℂ))
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := (show t ∈ Set.Ioi (1 : ℝ) from ht).le
      have hBA : A u t ≤ A s t := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      have h₁ : 0 ≤ s * (A s t - A u t) := by
        exact mul_nonneg (by linarith) (sub_nonneg.mpr hBA)
      have h₂ : 0 ≤ (u - s) * A u t := by
        exact mul_nonneg (sub_nonneg.mpr hsu) (Real.rpow_nonneg (by linarith) _)
      rw [← mul_sub, ← ofReal_sub, norm_mul, norm_real, Real.norm_eq_abs,
        show s * A s t - u * A u t = s * (A s t - A u t) - (u - s) * A u t by ring]
      exact (mul_le_mul (char_partial_sums χ hχ _) ((abs_sub _ _).trans_eq
        (by rw [abs_of_nonneg h₁, abs_of_nonneg h₂]; simp only [Pi.add_apply, Pi.sub_apply]; ring))
        (abs_nonneg _) (Nat.cast_nonneg q)))
  refine hupper.trans ?_
  rw [integral_const_mul]
  let B t := (u - s) * A u t
  let C t := s * (A s t - A u t)
  change (q : ℝ) * (∫ t in Set.Ioi 1, (B + C) t) ≤ _
  have hInt : (∫ t in Set.Ioi 1, (B + C) t) =
      (u - s) * u⁻¹ + s * (s⁻¹ - u⁻¹) := calc
    _ = (∫ t in Set.Ioi 1, B t) + (∫ t in Set.Ioi 1, C t) :=
      integral_add ((hA hu).const_mul (u - s)) (((hA hs).sub (hA hu)).const_mul s)
    _ = _ := by
      change (∫ t in Set.Ioi 1, (u - s) * A u t) +
        (∫ t in Set.Ioi 1, s * (A s - A u) t) = _
      rw [integral_const_mul, integral_const_mul]
      rw [show (∫ t in Set.Ioi 1, (A s - A u) t) =
        (∫ t in Set.Ioi 1, A s t) - (∫ t in Set.Ioi 1, A u t) from integral_sub (hA hs) (hA hu)]
      rw [hval hs, hval hu]
  rw [hInt]
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by linarith
  have heq : (u - s) * u⁻¹ + s * (s⁻¹ - u⁻¹) = 2 * (u - s) * u⁻¹ := by
    field_simp
    ring
  rw [heq]
  calc
    (q : ℝ) * (2 * (u - s) * u⁻¹) ≤ q * (2 * (u - s) * 1) := by
      gcongr
      exact inv_le_one_of_one_le₀ hu.le
    _ = _ := by ring

private lemma zeta_sum_bounds {s : ℝ} (hs : 1 < s) :
    (s - 1)⁻¹ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) ∧
      ∑' n : ℕ, (n : ℝ) ^ (-s) ≤ 1 + (s - 1)⁻¹ := by
  have hsneg : -s < -1 := by linarith
  have hS := Real.summable_nat_rpow.mpr hsneg
  have ha : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici (1 : ℝ)) := by
    intro a ha b _ hab
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one ha) hab (by linarith)
  have hI := integrableOn_Ioi_rpow_of_lt hsneg zero_lt_one
  have hIval : ∫ x in Set.Ioi 1, x ^ (-s) = (s - 1)⁻¹ := by
    rw [integral_Ioi_rpow_of_lt hsneg zero_lt_one, Real.one_rpow,
      show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg, one_div]
  have hano : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici ((1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_one] using ha
  have hnon (t : ℝ) (ht : t ∈ Set.Ioi ((1 : ℕ) : ℝ)) : 0 ≤ t ^ (-s) :=
    Real.rpow_nonneg (zero_le_one.trans (le_of_lt (by simpa only [Nat.cast_one, Set.mem_Ioi]
      using ht))) _
  have hI' : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi ((1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_one] using hI
  have hlo := AntitoneOn.integral_le_tsum_comp_add 1 hano hS hnon
  have hup := AntitoneOn.tsum_comp_add_le_integral 1 hano hI' hnon
  rw [Nat.cast_one, hIval] at hlo hup
  have hlo' : (s - 1)⁻¹ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-s) := hlo
  have hup' : ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-s) ≤ (s - 1)⁻¹ := hup
  have hz : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hS.tsum_eq_zero_add, Nat.cast_zero, hz, zero_add]
    exact hlo'
  · rw [← hS.sum_add_tsum_nat_add 2, sum_range_succ, sum_range_succ]
    simpa only [sum_range_zero, Nat.cast_zero, hz, Nat.cast_one, Real.one_rpow, zero_add]
      using add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hup'

private lemma norm_series_le_zeta_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℝ} (hs : 1 < s) :
    ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := by
  have hb (n : ℕ) : ‖LSeries.term (fun n : ℕ => χ n) (s : ℂ) n‖ ≤ (n : ℝ) ^ (-s) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [Real.zero_rpow (show -s ≠ 0 by linarith)]
    rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← cpow_neg, norm_mul,
      norm_natCast_cpow_of_pos hn, neg_re, ofReal_re]
    simpa using mul_le_mul_of_nonneg_right (χ.norm_le_one n) (Real.rpow_nonneg (by positivity) _)
  have hS := Real.summable_nat_rpow.mpr (show -s < -1 by linarith)
  have hterm := hS.of_nonneg_of_le (fun n => norm_nonneg _) hb
  exact norm_tsum_le_tsum_norm hterm |>.trans (hterm.tsum_le_tsum hb hS)

/-- The bound from the Euler product transfers to all real exponents just above one. -/
private lemma norm_even_series_lower {q : ℕ} [NeZero q] [Fact (1 < q)]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    {s : ℝ} (hs : 1 < s) :
    ((16 : ℝ) * q)⁻¹ ^ 8 ≤ ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖ := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast q.pos_of_neZero
  let a : ℝ := 16 * q
  have ha : 16 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  let t : ℝ := a⁻¹ ^ 8
  have ht : 0 < t := by positivity
  have hta : t ≤ 1 / 2 := by
    dsimp [t]
    have hi : a⁻¹ ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) ha
    have hle : a⁻¹ ^ 7 ≤ 1 := pow_le_one₀ (by positivity) (hi.trans (by norm_num))
    rw [show (8 : ℕ) = 7 + 1 by decide, pow_succ']
    exact (mul_le_of_le_one_right (by positivity) hle).trans (hi.trans (by norm_num))
  let u := s + t
  have hu : 1 < u := by dsimp [u]; linarith
  have huv : 1 + (u - 1)⁻¹ ≤ 2 * t⁻¹ := by
    have h₁ := inv_anti₀ ht (show t ≤ u - 1 by dsimp [u]; linarith)
    have h₂ := one_le_inv₀ (show 0 < t from ht) |>.2 (by linarith)
    linarith
  have htriv := (norm_series_le_zeta_sum (1 : DirichletCharacter ℂ q) hu).trans
    ((zeta_sum_bounds hu).2.trans huv)
  have hquad := norm_char_series_le (χ ^ 2) hχ2 hu
  have hprod := χ.norm_LSeries_product_ge_one (x := u - 1) (by linarith) 0
  have he : (1 : ℂ) + (↑(u - 1) : ℂ) = u := by push_cast; ring
  simp only [ofReal_zero, mul_zero, add_zero, he, norm_mul, norm_pow] at hprod
  apply le_of_not_gt
  intro hlt
  change ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖ < t at hlt
  have hdiff := norm_char_series_sub_le χ hχ hs (show s ≤ u by dsimp [u]; linarith)
  rw [show u - s = t by dsimp [u]; ring] at hdiff
  have hul : ‖LSeries (fun n : ℕ => χ n) (u : ℂ)‖ ≤ a * t := calc
    _ ≤ ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖ +
          ‖LSeries (fun n : ℕ => χ n) (s : ℂ) - LSeries (fun n : ℕ => χ n) (u : ℂ)‖ :=
      norm_le_insert (LSeries (fun n : ℕ => χ n) (s : ℂ))
        (LSeries (fun n : ℕ => χ n) (u : ℂ))
    _ ≤ t + 2 * q * t := add_le_add hlt.le hdiff
    _ = (1 + 2 * (q : ℝ)) * t := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [a]; linarith) ht.le
  have hr : (2 * t⁻¹) ^ 3 * (a * t) ^ 4 * (q : ℝ) < 1 := by
    have hta₁ : t ≠ 0 := ht.ne'
    have hta₂ : t * a ^ 8 = 1 := by dsimp [t]; rw [← mul_pow, inv_mul_cancel₀ ha0.ne', one_pow]
    have hq' : (8 : ℝ) * q < a ^ 4 := by
      have ha₁ : 1 ≤ a := by linarith
      have hpow := (le_self_pow₀ ha₁ (by decide : 4 ≠ 0))
      dsimp [a] at hpow ⊢
      linarith
    have heq : (2 * t⁻¹) ^ 3 * (a * t) ^ 4 * (q : ℝ) = (8 * q) * (a ^ 4 * t) := by
      field_simp [ht.ne']
      ring
    rw [heq]
    calc
      _ < a ^ 4 * (a ^ 4 * t) := mul_lt_mul_of_pos_right hq' (by positivity)
      _ = t * a ^ 8 := by ring
      _ = 1 := hta₂
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) htriv 3
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) hul 4
  have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  exact hr.not_ge (hprod.trans (mul_le_mul h₃ hquad (norm_nonneg _) (by positivity)))

private lemma prime_char_sum_approx {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℝ} (hs : 1 < s) :
    |(∑' p : Nat.Primes, (χ p.val).re * (p.val : ℝ) ^ (-s)) -
      Real.log ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖| ≤
        ∑' p : Nat.Primes, (p.val : ℝ) ^ (-2 : ℝ) := by
  let w (p : Nat.Primes) := (p.val : ℝ) ^ (-s)
  let z (p : Nat.Primes) := χ p.val * (p.val : ℂ) ^ (-(s : ℂ))
  let F (p : Nat.Primes) := -Complex.log (1 - z p)
  have hs' : 1 < (s : ℂ).re := by simpa
  have hnorm (p : Nat.Primes) : ‖z p‖ ≤ w p := by
    simp only [z, norm_mul, norm_natCast_cpow_of_pos p.prop.pos, neg_re, ofReal_re, w]
    exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  have hw (p : Nat.Primes) : w p ≤ (p.val : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_le) (by linarith)
  have hb (p : Nat.Primes) : ‖F p - z p‖ ≤ (p.val : ℝ) ^ (-2 : ℝ) := by
    have hhalf := (hnorm p).trans <| (hw p).trans <|
      inv_anti₀ (show (0 : ℝ) < 2 by norm_num) (by exact_mod_cast p.prop.two_le)
    have hh : ‖z p‖ < 1 := hhalf.trans_lt (by norm_num)
    have H := norm_log_one_sub_inv_sub_self_le hh
    have harg := slitPlane_arg_ne_pi (mem_slitPlane_of_norm_lt_one (z := -z p)
      (by simpa only [norm_neg] using hh))
    rw [Complex.log_inv (1 - z p) (by simpa only [sub_eq_add_neg] using harg)] at H
    refine H.trans ?_
    have h_inv : (1 - ‖z p‖)⁻¹ ≤ 2 :=
      (inv_le_comm₀ (by linarith : 0 < 1 - ‖z p‖) (by norm_num : (0 : ℝ) < 2)).mpr
        (by linarith)
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_two, ← inv_pow]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) ((hnorm p).trans (hw p)) 2
    calc
      ‖z p‖ ^ 2 * (1 - ‖z p‖)⁻¹ / 2 ≤ ((p.val : ℝ)⁻¹ ^ 2) * 2 / 2 := by gcongr
      _ = _ := by ring
  have hwS := Nat.Primes.summable_rpow.mpr (show -s < -1 by linarith)
  have hzS : Summable z := (hwS.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm).of_norm
  have hFS : Summable F := χ.summable_neg_log_one_sub_mul_prime_cpow hs'
  have hR : Real.log ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖ = ∑' p : Nat.Primes, (F p).re := by
    rw [← χ.LSeries_eulerProduct_exp_log hs']
    change Real.log ‖Complex.exp (∑' p, F p)‖ = _
    rw [norm_exp, Real.log_exp, re_tsum hFS]
  have hre (p : Nat.Primes) : (z p).re = (χ p.val).re * w p := by
    have hcast : (p.val : ℂ) ^ (-(s : ℂ)) = (w p : ℂ) := by
      dsimp [w]
      rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_neg, Complex.ofReal_natCast]
    change (χ (p.val : ZMod q) * (p.val : ℂ) ^ (-(s : ℂ))).re =
      (χ (p.val : ZMod q)).re * w p
    rw [hcast]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hZ : (∑' p : Nat.Primes, (χ p.val).re * (p.val : ℝ) ^ (-s)) =
      ∑' p : Nat.Primes, (z p).re :=
    tsum_congr fun p => (hre p).symm
  rw [hZ, hR]
  have hsum := (Nat.Primes.summable_rpow.mpr (show (-2 : ℝ) < -1 by norm_num))
  have hpoint (p : Nat.Primes) : ‖(z p).re - (F p).re‖ ≤ (p.val : ℝ) ^ (-2 : ℝ) := by
    rw [Real.norm_eq_abs, abs_sub_comm, ← sub_re]
    exact (abs_re_le_norm _).trans (hb p)
  have hsumm := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  rw [← (hasSum_re hzS.hasSum).summable.tsum_sub (hasSum_re hFS.hasSum).summable,
    ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_le_tsum hpoint hsum)

private lemma norm_one_series_lower {q r : ℕ} [NeZero q] (hfac : q.primeFactors = {r})
    (hr : r.Prime) {s : ℝ} (hs : 1 < s) :
    (s - 1)⁻¹ / 2 ≤ ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) (s : ℂ)‖ := by
  have hs' : 1 < (s : ℂ).re := by simpa
  have h := DirichletCharacter.LSeries_changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1) hs'
  rw [DirichletCharacter.changeLevel_one, hfac, prod_singleton] at h
  have hz : LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) (s : ℂ) =
      ((∑' n : ℕ, (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [show (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) = (1 : ℕ → ℂ) from
      funext fun n => MulChar.one_apply (isUnit_of_subsingleton _), LSeries_one_eq_riemannZeta hs',
      zeta_eq_tsum_one_div_nat_cpow hs', Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [one_div, ← cpow_neg, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast, Complex.ofReal_neg]
  rw [h, hz, MulChar.one_apply (isUnit_of_subsingleton _), one_mul, norm_mul, norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun _ => by positivity)]
  have hfac' : (1 / 2 : ℝ) ≤ ‖1 - (r : ℂ) ^ (-(s : ℂ))‖ := by
    have H : ‖(r : ℂ) ^ (-(s : ℂ))‖ ≤ (2 : ℝ)⁻¹ := by
      rw [norm_natCast_cpow_of_pos hr.pos, neg_re, ofReal_re]
      have h₁ : (1 : ℝ) ≤ r := by exact_mod_cast hr.one_le
      calc
        _ ≤ (r : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h₁ (by linarith)
        _ ≤ _ := by
          rw [Real.rpow_neg_one]
          exact inv_anti₀ (by norm_num) (by exact_mod_cast hr.two_le)
    have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) ^ (-(s : ℂ)))
    simp only [norm_one] at h
    linarith
  rw [div_eq_mul_one_div]
  exact mul_le_mul (zeta_sum_bounds hs).1 hfac' (by norm_num)
    (tsum_nonneg fun _ => by positivity)

private lemma even_not_quadratic_prime {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (χ : DirichletCharacter ℂ p) (he : χ.Even) (hne : χ ≠ 1) : χ ^ 2 ≠ 1 := by
  intro hquad
  apply hne
  apply MulChar.ext'
  intro j
  by_cases hj : j = 0
  · rw [hj, MulChar.map_zero, MulChar.map_zero]
  have hju := isUnit_iff_ne_zero.mpr hj
  rw [MulChar.one_apply hju]
  have hχ2 : χ j ^ 2 = 1 := by
    rw [← χ.pow_apply' (by decide : (2 : ℕ) ≠ 0), hquad, MulChar.one_apply hju]
  let k := p / 2
  have hk : k * 2 = p - 1 := by dsimp [k]; omega
  have hko : k / 2 * 2 + 1 = k := by dsimp [k]; omega
  have hjsq : (j ^ k) ^ 2 = 1 := by
    rw [← pow_mul, hk, ZMod.pow_card_sub_one_eq_one hj]
  have hjk : χ j ^ k = 1 := by
    rw [← map_pow]
    rcases sq_eq_one_iff.mp hjsq with h | h
    · rw [h, map_one]
    · exact congrArg χ h |>.trans he
  nth_rw 1 [← hko] at hjk
  rw [pow_add, Nat.mul_comm (k / 2) 2, pow_mul, hχ2, one_pow, pow_one, one_mul] at hjk
  exact hjk

private lemma even_not_quadratic_four (χ : DirichletCharacter ℂ 4)
    (he : χ.Even) (hne : χ ≠ 1) : χ ^ 2 ≠ 1 := by
  intro _
  apply hne
  apply MulChar.ext'
  intro j
  let : Fact (1 < 4) := ⟨by decide⟩
  have hcases : ∀ a : ZMod 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = -1 := by decide
  have hj := hcases j
  have htwo : ¬ IsUnit (2 : ZMod 4) := by
    exact fun h => (by decide : ¬ Nat.Coprime 2 4) ((ZMod.isUnit_iff_coprime 2 4).mp h)
  rcases hj with rfl | rfl | rfl | rfl
  · rw [MulChar.map_zero, MulChar.map_zero]
  · rw [map_one, map_one]
  · rw [MulChar.map_nonunit _ htwo, MulChar.map_nonunit _ htwo]
  · exact he.trans (MulChar.one_apply (by simp)).symm

private noncomputable def eulerError : ℝ := ∑' p : Nat.Primes, (p.val : ℝ) ^ (-2 : ℝ)

/-- Odd characters enter with a negative sign at the residue −1, so only the even
nonprincipal characters require a lower bound for their series norms. -/
private lemma progression_series_lower {q r : ℕ} [NeZero q] [Fact (1 < q)]
    (hfac : q.primeFactors = {r}) (hr : r.Prime)
    (hquad : ∀ χ : DirichletCharacter ℂ q, χ.Even → χ ≠ 1 → χ ^ 2 ≠ 1)
    {s : ℝ} (hs : 1 < s) (hs₂ : s ≤ 3 / 2) :
    -Real.log (s - 1) / q - (130 + eulerError) * q ≤
      ∑' p : Nat.Primes, if (p.val : ZMod q) = -1 then (p.val : ℝ) ^ (-s) else 0 := by
  classical
  let w (p : Nat.Primes) := (p.val : ℝ) ^ (-s)
  let F (χ : DirichletCharacter ℂ q) (p : Nat.Primes) := (χ p.val).re * w p
  let a (χ : DirichletCharacter ℂ q) := (χ (-1)).re
  let M := ∑' p : Nat.Primes, if (p.val : ZMod q) = -1 then w p else 0
  let B := 130 + eulerError
  have hE0 : 0 ≤ eulerError := tsum_nonneg fun _ => by positivity
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast q.pos_of_neZero
  have hw := Nat.Primes.summable_rpow.mpr (show -s < -1 by linarith)
  have hF (χ : DirichletCharacter ℂ q) : Summable (F χ) := by
    refine (hw.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_).of_norm
    have hp : 0 ≤ w p := by dsimp [w]; positivity
    change ‖(χ (p.val : ZMod q)).re * w p‖ ≤ w p
    rw [norm_mul, Real.norm_of_nonneg hp, Real.norm_eq_abs]
    exact mul_le_of_le_one_left hp ((abs_re_le_norm _).trans (χ.norm_le_one _))
  have hunit : IsUnit (-1 : ZMod q) := by simp
  have hone : a 1 = 1 := by simp [a, MulChar.one_apply hunit]
  have hterm (χ : DirichletCharacter ℂ q) :
      (if χ = 1 then -Real.log (s - 1) else 0) - B * q ≤ a χ * ∑' p, F χ p := by
    have hE : |(∑' p, F χ p) -
        Real.log ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖| ≤ eulerError :=
      prime_char_sum_approx χ hs
    have hEc : eulerError ≤ B * q - 128 * q := by
      have hle := mul_le_mul_of_nonneg_left hq1 hE0
      dsimp [B]
      nlinarith only [hle, hq1]
    rcases eq_or_ne χ 1 with rfl | hne
    · rw [hone, one_mul, ite_eq_left rfl]
      have h := norm_one_series_lower hfac hr hs
      have hpos : 0 < (s - 1)⁻¹ / 2 := by positivity
      have hL := Real.log_le_log hpos h
      rw [Real.log_div (inv_ne_zero (by linarith)) (by norm_num), Real.log_inv] at hL
      linarith only [(abs_le.mp hE).1, hEc, hL,
        Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num), hq1]
    rw [ite_eq_right hne]
    have hneL : LSeries (fun n : ℕ => χ n) (s : ℂ) ≠ 0 :=
      χ.LSeries_ne_zero_of_one_lt_re (by simpa)
    have hlogn : 0 < ‖LSeries (fun n : ℕ => χ n) (s : ℂ)‖ := norm_pos_iff.mpr hneL
    rcases χ.even_or_odd with he | ho
    · have ha : a χ = 1 := by change (χ (-1)).re = 1; rw [he, one_re]
      rw [ha, one_mul, zero_sub]
      have h := norm_even_series_lower χ hne (hquad χ he hne) hs
      have hq0 : 0 < (q : ℝ) := by linarith
      have hL := Real.log_le_log (by positivity) h
      rw [Real.log_pow, Real.log_inv, Nat.cast_ofNat] at hL
      linarith only [hL, Real.log_le_sub_one_of_pos (show 0 < (16 : ℝ) * q by positivity),
        (abs_le.mp hE).1, hEc]
    · have ha : a χ = -1 := by change (χ (-1)).re = -1; rw [ho, neg_re, one_re]
      rw [ha, neg_one_mul, zero_sub]
      have hL := Real.log_le_log hlogn (norm_char_series_le χ hne hs)
      linarith only [hL, Real.log_le_sub_one_of_pos (x := (q : ℝ)) (by linarith),
        (abs_le.mp hE).2, hEc, hq1]
  have horth (p : Nat.Primes) :
      ∑ χ : DirichletCharacter ℂ q, a χ * F χ p =
        (q.totient : ℝ) * (if (p.val : ZMod q) = -1 then w p else 0) := by
    have H := congrArg Complex.re (DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit
      (p.val : ZMod q))
    change (∑ χ : DirichletCharacter ℂ q, χ (-1 : ZMod q)⁻¹ * χ (p.val : ZMod q)).re =
      (if (-1 : ZMod q) = (p.val : ZMod q) then (q.totient : ℂ) else 0).re at H
    have hinv : (-1 : ZMod q)⁻¹ = -1 := by simp
    simp only [hinv, Complex.re_sum, mul_re] at H
    have him (χ : DirichletCharacter ℂ q) : (χ (-1)).im = 0 := by
      rcases χ.even_or_odd with he | ho
      · rw [he, one_im]
      · rw [ho, neg_im, one_im, neg_zero]
    simp only [him, zero_mul, sub_zero] at H
    rw [show (∑ χ : DirichletCharacter ℂ q, a χ * F χ p) =
      (∑ χ : DirichletCharacter ℂ q, (χ (-1)).re * (χ p.val).re) * w p by
        rw [sum_mul]; simp only [a, F, mul_assoc], H]
    by_cases h : (p.val : ZMod q) = -1 <;> simp [h, eq_comm (a := (-1 : ZMod q))]
  have hsum := sum_le_sum (s := (univ : Finset (DirichletCharacter ℂ q))) fun χ _ => hterm χ
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient :=
    Nat.card_eq_fintype_card.symm.trans
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q)
  rw [sum_sub_distrib, sum_const, card_univ, hcard, nsmul_eq_mul] at hsum
  simp only [sum_ite_eq', mem_univ, ite_true] at hsum
  simp_rw [← tsum_mul_left] at hsum
  rw [← Summable.tsum_finsetSum (fun χ _ => (hF χ).mul_left (a χ))] at hsum
  simp_rw [horth, tsum_mul_left] at hsum
  have hφ : 0 < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr q.pos_of_neZero)
  have hlog : 0 ≤ -Real.log (s - 1) := by
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have hdiv := div_le_div_of_nonneg_left hlog hφ
    (show (q.totient : ℝ) ≤ q by exact_mod_cast Nat.totient_le q)
  apply (sub_le_sub_right hdiv _).trans
  apply le_of_mul_le_mul_right _ hφ
  change (-Real.log (s - 1) / q.totient - B * q) * q.totient ≤ M * _
  rw [sub_mul, div_mul_cancel₀ _ hφ.ne']
  linarith only [hsum]

/-- Truncate the weighted prime sum at `x` to obtain a uniform reciprocal-prime bound. -/
private lemma progression_reciprocal_sum_lower {q r : ℕ} [NeZero q] [Fact (1 < q)]
    (hfac : q.primeFactors = {r}) (hr : r.Prime)
    (hquad : ∀ χ : DirichletCharacter ℂ q, χ.Even → χ ≠ 1 → χ ^ 2 ≠ 1)
    {x : ℝ} (hx : Real.exp 4 ≤ x) :
    Real.log (Real.log x) / (2 * q) - (135 + eulerError) * q ≤
      ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p : ℕ => (p : ZMod q) = -1), (p : ℝ)⁻¹ := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog4 : 4 ≤ Real.log x := by
    rw [← Real.log_exp 4]
    exact Real.log_le_log (Real.exp_pos _) hx
  let z := Real.sqrt (Real.log x)
  have hz : 2 ≤ z := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hz0 : 0 < z := by linarith
  let d := z⁻¹
  have hd0 : 0 < d := inv_pos.mpr hz0
  have hd : d ≤ 1 / 2 := (inv_anti₀ (by norm_num : (0 : ℝ) < 2) hz).trans_eq (by norm_num)
  let s := 1 + d
  have hs : 1 < s := by dsimp [s]; linarith
  have hs' : s ≤ 3 / 2 := by dsimp [s]; linarith
  have hlogd : -Real.log (s - 1) = Real.log (Real.log x) / 2 := by
    rw [show s - 1 = d by dsimp [s]; ring, show d = (Real.sqrt (Real.log x))⁻¹ from rfl,
      Real.log_inv, neg_neg, Real.log_sqrt (by linarith)]
  have h := progression_series_lower hfac hr hquad hs hs'
  rw [hlogd, div_div] at h
  let w (n : ℕ) : ℝ := (n : ℝ) ^ (-s)
  let W (n : ℕ) : ℝ := if n.Prime ∧ (n : ZMod q) = -1 then w n else 0
  have hW : Summable W := (Real.summable_nat_rpow.mpr (show -s < -1 by linarith)).of_nonneg_of_le
    (fun n => by unfold W; split_ifs <;> positivity)
    (fun n => by unfold W w; split_ifs <;> first | exact le_rfl | positivity)
  have hrewrite : (∑' p : Nat.Primes, if (p.val : ZMod q) = -1 then w p.val else 0) =
      ∑' n : ℕ, W n := by
    let G (n : ℕ) : ℝ := if (n : ZMod q) = -1 then w n else 0
    calc
      _ = ∑' n : ℕ, {n | n.Prime}.indicator G n :=
        _root_.tsum_subtype {n : ℕ | n.Prime} G
      _ = _ := by
        apply tsum_congr
        intro n
        by_cases hn : n.Prime <;> simp [Set.indicator, W, G, hn]
  change _ ≤ (∑' p : Nat.Primes, if (p.val : ZMod q) = -1 then w p.val else 0) at h
  rw [hrewrite, ← hW.sum_add_tsum_nat_add (⌊x⌋₊ + 1)] at h
  let v (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 + d / 2))
  have hv : Summable v := Real.summable_nat_rpow.mpr (by linarith)
  have hxpow : x ^ (-(d / 2)) = Real.exp (-(z / 2)) := by
    rw [Real.rpow_def_of_pos hx0, ← show z ^ 2 = Real.log x from Real.sq_sqrt (by linarith)]
    congr 1
    change z ^ 2 * -(z⁻¹ / 2) = -(z / 2)
    field_simp [hz0.ne']
  have htail : (∑' n : ℕ, W (n + (⌊x⌋₊ + 1))) ≤ 5 := by
    have h0 : 0 ≤ x ^ (-(d / 2)) := Real.rpow_nonneg hx0.le _
    have hv' : Summable (fun n : ℕ => v (n + (⌊x⌋₊ + 1))) := (summable_nat_add_iff _).mpr hv
    have hbound (k : ℕ) : W (k + (⌊x⌋₊ + 1)) ≤ x ^ (-(d / 2)) * v (k + (⌊x⌋₊ + 1)) := by
      let n := k + (⌊x⌋₊ + 1)
      have hn : x ≤ (n : ℝ) := (Nat.lt_floor_add_one x).le.trans (by dsimp [n]; push_cast; linarith)
      have hn0 := hx0.trans_le hn
      have hpow := Real.rpow_le_rpow_of_nonpos hx0 hn (show -(d / 2) ≤ 0 by linarith)
      change W n ≤ x ^ (-(d / 2)) * v n
      have hwle : W n ≤ w n := by unfold W w; split_ifs <;> first | exact le_rfl | positivity
      refine hwle.trans ?_
      rw [show w n = (n : ℝ) ^ (-s) from rfl,
        show -s = -(d / 2) + -(1 + d / 2) by dsimp [s]; ring, Real.rpow_add hn0]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    have hsum_v : (∑' n : ℕ, v (n + (⌊x⌋₊ + 1))) ≤ ∑' n : ℕ, v n := by
      rw [← hv.sum_add_tsum_nat_add (⌊x⌋₊ + 1)]
      exact le_add_of_nonneg_left (sum_nonneg fun _ _ => by dsimp [v]; positivity)
    have hvbound : (∑' n : ℕ, v n) ≤ 1 + 2 * z := by
      have hh := (zeta_sum_bounds (s := 1 + d / 2) (by linarith)).2
      rw [show 1 + d / 2 - 1 = d / 2 by ring] at hh
      change _ ≤ 1 + 2 * z
      convert hh using 1
      simp [d, div_eq_mul_inv, mul_comm]
    calc
      _ ≤ ∑' n : ℕ, x ^ (-(d / 2)) * v (n + (⌊x⌋₊ + 1)) :=
        ((summable_nat_add_iff _).mpr hW).tsum_le_tsum hbound (hv'.mul_left _)
      _ ≤ x ^ (-(d / 2)) * (1 + 2 * z) := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hsum_v.trans hvbound) h0
      _ ≤ 5 := by
        rw [hxpow]
        have hh : 1 + 2 * z ≤ 5 * Real.exp (z / 2) := by
          linarith [Real.add_one_le_exp (z / 2)]
        calc
          _ ≤ Real.exp (-(z / 2)) * (5 * Real.exp (z / 2)) :=
            mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
          _ = _ := by rw [Real.exp_neg]; field_simp
  have hhead : (∑ n ∈ range (⌊x⌋₊ + 1), W n) ≤
      ∑ p ∈ (⌊x⌋₊.primesLE).filter (fun p : ℕ => (p : ZMod q) = -1), (p : ℝ)⁻¹ := by
    rw [show (⌊x⌋₊.primesLE).filter (fun p : ℕ => (p : ZMod q) = -1) =
      (range (⌊x⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ (n : ZMod q) = -1) from by
        ext n; simp [Nat.mem_primesLE, and_assoc]]
    rw [sum_filter]
    apply sum_le_sum
    intro n _
    rw [show W n = if n.Prime ∧ (n : ZMod q) = -1 then w n else 0 from rfl]
    split_ifs with hn
    · rw [show w n = (n : ℝ) ^ (-s) from rfl, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.1.one_le) (by linarith)
    · rfl
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast q.pos_of_neZero
  linarith only [h, htail, hhead, hq1]

private abbrev smallPrimes (y : ℝ) : Finset ℕ :=
  (⌊y⌋₊.primesLE).filter fun p : ℕ => (p : ZMod 4) = -1

private abbrev sievePrimes (p : ℕ) (x y : ℝ) : Finset ℕ :=
  (⌊x⌋₊.primesLE).filter fun r : ℕ => (r : ZMod p) = -1 ∧ y < (r : ℝ)

private lemma mem_smallPrimes {y : ℝ} {p : ℕ} (hp : p ∈ smallPrimes y) :
    p ≤ ⌊y⌋₊ ∧ p.Prime ∧ p % 4 = 3 := by
  obtain ⟨hp₀, hp₁⟩ := mem_filter.mp hp
  have he : (3 : ZMod 4) = -1 := by decide
  rw [← he] at hp₁
  exact ⟨(Nat.mem_primesLE.mp hp₀).1, (Nat.mem_primesLE.mp hp₀).2,
    ZMod.natCast_eq_natCast_iff' p 3 4 |>.mp hp₁⟩

private lemma sieve_reciprocals_lower {p : ℕ} {x y : ℝ}
    (hx : Real.exp 4 ≤ x) (hy : 1 ≤ y) (hyx : y ^ 4 = Real.log (Real.log x))
    (hylarge : 2 * (137 + eulerError) ≤ y) (hp : p ∈ smallPrimes y) :
    y ^ 2 ≤ ∑ r ∈ sievePrimes p x y, (r : ℝ)⁻¹ := by
  obtain ⟨hpy, hp, hp4⟩ := mem_smallPrimes hp
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  have H := progression_reciprocal_sum_lower hp.primeFactors hp
    (even_not_quadratic_prime hp4) hx
  let A := (⌊x⌋₊.primesLE).filter fun r : ℕ => (r : ZMod p) = -1
  have heq : sievePrimes p x y = A.filter (fun r : ℕ => y < (r : ℝ)) := by
    rw [filter_filter]
  have hdec := sum_filter_add_sum_filter_not A (fun r : ℕ => y < (r : ℝ))
    (fun r => (r : ℝ)⁻¹)
  have hsmall : ∑ r ∈ A.filter (fun r : ℕ => ¬ y < (r : ℝ)), (r : ℝ)⁻¹ ≤ y := by
    calc
      _ ≤ ∑ _r ∈ A.filter (fun r : ℕ => ¬ y < (r : ℝ)), (1 : ℝ) := by
        apply sum_le_sum
        intro r hr
        exact inv_le_one_of_one_le₀ (by exact_mod_cast
          (Nat.prime_of_mem_primesLE (mem_filter.mp (mem_filter.mp hr).1).1).one_le)
      _ ≤ ∑ _r ∈ Icc 1 ⌊y⌋₊, (1 : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
          (s := A.filter (fun r : ℕ => ¬ y < (r : ℝ)))
          (t := Icc 1 ⌊y⌋₊)
        · intro r hr
          have hrp := Nat.prime_of_mem_primesLE (mem_filter.mp (mem_filter.mp hr).1).1
          exact mem_Icc.mpr ⟨hrp.one_le, (Nat.le_floor_iff (by linarith)).mpr
            (le_of_not_gt (mem_filter.mp hr).2)⟩
        · intro r _ _
          positivity
      _ ≤ _ := by simpa [Nat.card_Icc] using Nat.floor_le (show 0 ≤ y by linarith)
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpy' : (p : ℝ) ≤ y := ((Nat.cast_le (α := ℝ)).mpr hpy).trans (Nat.floor_le (by linarith))
  have hE : 0 ≤ eulerError := tsum_nonneg fun _ => by positivity
  have hb : 0 ≤ 135 + eulerError := by linarith
  have hmain : y ^ 3 / 2 ≤ Real.log (Real.log x) / (2 * p) := by
    rw [← hyx]
    calc
      _ = y ^ 4 / (2 * y) := by field_simp [show y ≠ 0 by linarith]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by linarith)
  have hC := mul_le_mul_of_nonneg_left hpy' hb
  have hly : 0 ≤ y := by linarith
  have hy₁ : y ≤ y ^ 2 := by nlinarith only [mul_nonneg hly (sub_nonneg.mpr hy)]
  have hstep := mul_le_mul_of_nonneg_right hylarge (sq_nonneg y)
  have hstep' := mul_le_mul_of_nonneg_left hy₁ (show 0 ≤ 136 + eulerError by linarith)
  rw [heq]
  change _ ≤ ∑ r ∈ A, (r : ℝ)⁻¹ at H
  linarith only [H, hdec, hsmall, hmain, hC, hstep, hstep']

private lemma square_reciprocals_le {m N : ℕ} (hm : 0 < m) :
    ∑ r ∈ Ioc m N, ((r : ℝ) ^ 2)⁻¹ ≤ (m : ℝ)⁻¹ := by
  let g (t : ℝ) := t ^ (-2 : ℝ)
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have ha : AntitoneOn g (Set.Icc (m : ℝ) (N : ℝ)) := by
    intro u hu v _ huv
    exact Real.rpow_le_rpow_of_nonpos (hm0.trans_le hu.1) huv (by norm_num)
  have hI : IntegrableOn g (Set.Ioi (m : ℝ)) := integrableOn_Ioi_rpow_of_lt (by norm_num) hm0
  have h := AntitoneOn.sum_Ico_le_integral ha hI
    (fun _ ht => Real.rpow_nonneg (hm0.trans ht).le _)
  have he : (∑ r ∈ Ioc m N, ((r : ℝ) ^ 2)⁻¹) =
      ∑ n ∈ Ico m N, g ((n + 1 : ℕ) : ℝ) := by
    symm
    refine sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hl, hu⟩ := mem_Ico.mp hn
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro n _ k _ hnk
      omega
    · intro r hr
      obtain ⟨hl, hu⟩ := mem_Ioc.mp hr
      exact ⟨r - 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n _
      change ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ) = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (by positivity), Real.rpow_two]
  rw [he]
  refine h.trans_eq ?_
  simp only [g, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hm0]
  norm_num [Real.rpow_neg_one]

private lemma dvd_sigma_of_prime_factor {p r n : ℕ} (hr : r.Prime)
    (hmod : (r : ZMod p) = -1) (hdiv : r ∣ n) (hsq : ¬ r ^ 2 ∣ n) :
    p ∣ ArithmeticFunction.sigma 1 n := by
  obtain ⟨m, rfl⟩ := hdiv
  have hcop : r.Coprime m := hr.coprime_iff_not_dvd.mpr fun hm =>
    hsq (by simpa [pow_two] using Nat.mul_dvd_mul_left r hm)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    show ArithmeticFunction.sigma 1 r = r + 1 by
      simpa [sum_range_succ, add_comm] using
        ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hr]
  apply dvd_mul_of_dvd_left
  apply (ZMod.natCast_eq_zero_iff (r + 1) p).mp
  push_cast
  rw [hmod, neg_add_cancel]

open Classical in
private noncomputable def exceptions (x y : ℝ) : Finset ℕ :=
  (Icc 1 ⌊x⌋₊).filter fun n => ∃ p ∈ smallPrimes y, ¬ p ∣ ArithmeticFunction.sigma 1 n

open Classical in
/-- An exception avoids every prime in some sieve set or is divisible by a large square. -/
private lemma card_exceptions_le {C : ℝ}
    (hC : 0 < C)
    (hsieve : ∀ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) → ∀ x : ℝ, 1 < x →
      ((((Icc 1 ⌊x⌋₊).filter fun n => ∀ p ∈ P, ¬ p ∣ n).card : ℕ) : ℝ) ≤
        C * x * Real.exp (-∑ p ∈ (Iic ⌊x⌋₊).filter (· ∈ P), (1 : ℝ) / p))
    {x y : ℝ} (hx : Real.exp 4 ≤ x) (hy : 2 ≤ y) (hyx : y ^ 4 = Real.log (Real.log x))
    (hylarge : 2 * (137 + eulerError) ≤ y) :
    ((exceptions x y).card : ℝ) ≤ (C + 2) * x / y := by
  classical
  have hx1 : 1 < x := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 4)).trans_le hx
  let I := Icc 1 ⌊x⌋₊
  let S p := sievePrimes p x y
  let U p := I.filter (fun n => ∀ r ∈ S p, ¬ r ∣ n)
  let F r := I.filter (fun n => r ^ 2 ∣ n)
  let D := (Ioc ⌊y⌋₊ ⌊x⌋₊).biUnion F
  have hsub : exceptions x y ⊆ (smallPrimes y).biUnion U ∪ D := by
    intro n hn
    obtain ⟨hnI, p, hp, hnp⟩ := mem_filter.mp hn
    by_cases h : ∀ r ∈ S p, ¬ r ∣ n
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hnI, h⟩⟩)
    · push Not at h
      obtain ⟨r, hr, hrd⟩ := h
      obtain ⟨hl, hu⟩ := mem_filter.mp hr
      obtain ⟨hrx, hrp⟩ := Nat.mem_primesLE.mp hl
      have hsq : r ^ 2 ∣ n := by
        by_contra h
        exact hnp (dvd_sigma_of_prime_factor hrp hu.1 hrd h)
      have hry : ⌊y⌋₊ < r := by exact_mod_cast
        (Nat.floor_le (show 0 ≤ y by linarith)).trans_lt hu.2
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨r, mem_Ioc.mpr ⟨hry, hrx⟩, mem_filter.mpr ⟨hnI, hsq⟩⟩)
  have hU (p : ℕ) (hp : p ∈ smallPrimes y) :
      ((U p).card : ℝ) ≤ C * x * Real.exp (-y ^ 2) := by
    have h := hsieve (↑(S p)) (fun r hr => Nat.prime_of_mem_primesLE
      (mem_filter.mp (show r ∈ S p from hr)).1) x hx1
    have he (inst : DecidablePred fun r => r ∈ (↑(S p) : Set ℕ)) :
        @Finset.filter ℕ (· ∈ (↑(S p) : Set ℕ)) inst (Iic ⌊x⌋₊) = S p := by
      ext r
      simp only [mem_filter, mem_Iic, mem_coe]
      exact and_iff_right_of_imp fun hr =>
        Nat.le_of_mem_primesLE ((mem_filter.mp (show r ∈ S p from hr)).1)
    have hUeq (inst : DecidablePred fun n : ℕ => ∀ r ∈ (↑(S p) : Set ℕ), ¬ r ∣ n) :
        @Finset.filter ℕ (fun n => ∀ r ∈ (↑(S p) : Set ℕ), ¬ r ∣ n) inst
            (Icc 1 ⌊x⌋₊) = U p := by
      ext n
      simp only [U, I, mem_filter, mem_coe]
    rw [hUeq, he] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    simp only [one_div]
    exact neg_le_neg (sieve_reciprocals_lower hx (by linarith) hyx hylarge hp)
  have hcard : ((smallPrimes y).card : ℝ) ≤ y := by
    have hh : smallPrimes y ⊆ Icc 1 ⌊y⌋₊ := by
      intro p hp
      obtain ⟨h₁, h₂, _⟩ := mem_smallPrimes hp
      exact mem_Icc.mpr ⟨h₂.one_le, h₁⟩
    have hb : ((smallPrimes y).card : ℝ) ≤ ((Icc 1 ⌊y⌋₊).card : ℝ) := by
      exact_mod_cast card_le_card hh
    exact hb.trans (by simpa [Nat.card_Icc] using Nat.floor_le (show 0 ≤ y by linarith))
  have hcardU : (((smallPrimes y).biUnion U).card : ℝ) ≤ C * x / y := by
    have hsum : (((smallPrimes y).biUnion U).card : ℝ) ≤
        ∑ p ∈ smallPrimes y, ((U p).card : ℝ) := by exact_mod_cast card_biUnion_le
    refine hsum.trans ((sum_le_sum hU).trans ?_)
    rw [sum_const, nsmul_eq_mul]
    have hpos : 0 < y := by linarith
    have he : Real.exp (-y ^ 2) ≤ (y ^ 2)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (sq_pos_of_pos hpos) (by linarith [Real.add_one_le_exp (y ^ 2)])
    calc
      _ ≤ y * (C * x * Real.exp (-y ^ 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ y * (C * x * (y ^ 2)⁻¹) := by gcongr
      _ = _ := by field_simp [hpos.ne']
  have hm : 0 < ⌊y⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hcardD : (D.card : ℝ) ≤ 2 * x / y := by
    have hsum : (D.card : ℝ) ≤ ∑ r ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, ((F r).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have hF (r : ℕ) : ((F r).card : ℝ) ≤ x * ((r : ℝ) ^ 2)⁻¹ := by
      rw [show F r = (Ioc 0 ⌊x⌋₊).filter (fun n => r ^ 2 ∣ n) by
          change (Icc 1 ⌊x⌋₊).filter _ = _
          rw [← Icc_add_one_left_eq_Ioc (0 : ℕ) ⌊x⌋₊]
          simp only [zero_add],
        Nat.Ioc_filter_dvd_card_eq_div]
      refine Nat.cast_div_le.trans ?_
      rw [Nat.cast_pow, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
    refine hsum.trans ((sum_le_sum fun r _ => hF r).trans ?_)
    rw [← mul_sum]
    have hmf : 0 < (⌊y⌋₊ : ℝ) := Nat.cast_pos.mpr hm
    have hyf : y ≤ 2 * (⌊y⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one y]
    calc
      _ ≤ x * (⌊y⌋₊ : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (square_reciprocals_le hm) (by linarith)
      _ ≤ x * (2 / y) := mul_le_mul_of_nonneg_left (by
        apply (le_div_iff₀ (by linarith)).mpr
        calc
          _ ≤ (⌊y⌋₊ : ℝ)⁻¹ * (2 * (⌊y⌋₊ : ℝ)) := by gcongr
          _ = _ := by field_simp [hmf.ne']) (by linarith)
      _ = _ := by ring
  have hle : ((exceptions x y).card : ℝ) ≤
      (((smallPrimes y).biUnion U).card : ℝ) + (D.card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  linarith only [hle, hcardU, hcardD,
    show (C + 2) * x / y = C * x / y + 2 * x / y by ring]

private abbrev logFour (x : ℝ) : ℝ := Real.log (Real.log (Real.log (Real.log x)))

private noncomputable def productConstant : ℝ := 12 * Real.exp (4 * (135 + eulerError))

private lemma prime_product_le {x y : ℝ} (hy : Real.exp 4 ≤ y)
    (hlog : Real.log (Real.log (Real.log x)) = 4 * Real.log y) (hlog₄ : 0 < logFour x) :
    (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)) ≤ productConstant / logFour x := by
  let : Fact (1 < 4) := ⟨by decide⟩
  let u := Real.log y
  have hu : 1 ≤ u := by
    have h := Real.log_le_log (Real.exp_pos (4 : ℝ)) hy
    rw [Real.log_exp] at h
    dsimp [u]
    linarith
  have hu0 : 0 < u := by linarith
  have hfac : (4 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_two
  have h := progression_reciprocal_sum_lower hfac Nat.prime_two even_not_quadratic_four hy
  change Real.log u / (2 * (4 : ℝ)) - (135 + eulerError) * 4 ≤
    ∑ p ∈ smallPrimes y, (p : ℝ)⁻¹ at h
  have hlogle : logFour x ≤ 12 * u ^ (1 / 8 : ℝ) := by
    change Real.log (Real.log (Real.log (Real.log x))) ≤ _
    rw [hlog, Real.log_mul (by norm_num) hu0.ne']
    have hp := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 (1 / 8 : ℝ))
    rw [Real.log_rpow hu0] at hp
    linarith only [hp, Real.one_le_rpow hu (show (0 : ℝ) ≤ 1 / 8 by norm_num),
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  calc
    _ ≤ Real.exp (-∑ p ∈ smallPrimes y, (p : ℝ)⁻¹) := by
      rw [← sum_neg_distrib, Real.exp_sum]
      apply prod_le_prod₀
      · intro p hp
        exact sub_nonneg.mpr (inv_le_one_of_one_le₀
          (by exact_mod_cast (mem_smallPrimes hp).2.1.one_le))
      · intro p _
        simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(p : ℝ)⁻¹)
    _ ≤ Real.exp (4 * (135 + eulerError) + (-(1 / 8 : ℝ)) * Real.log u) := by
      apply Real.exp_le_exp.mpr
      linarith only [h]
    _ = Real.exp (4 * (135 + eulerError)) * (u ^ (1 / 8 : ℝ))⁻¹ := by
      rw [Real.exp_add, mul_comm (-(1 / 8 : ℝ)), ← Real.rpow_def_of_pos hu0,
        Real.rpow_neg hu0.le]
    _ ≤ _ := by
      apply (le_div_iff₀ hlog₄).mpr
      change _ ≤ 12 * Real.exp (4 * (135 + eulerError))
      rw [mul_assoc]
      calc
        _ ≤ Real.exp (4 * (135 + eulerError)) *
            ((u ^ (1 / 8 : ℝ))⁻¹ * (12 * u ^ (1 / 8 : ℝ))) := by gcongr
        _ = _ := by field_simp [Real.rpow_pos_of_pos hu0 (1 / 8 : ℝ) |>.ne']

private lemma totient_le_of_smallPrimes_dvd {y : ℝ} {m : ℕ}
    (hm : ∀ p ∈ smallPrimes y, p ∣ m) :
    (m.totient : ℝ) ≤ m * (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  have H := congrArg (fun a : ℚ => (a : ℝ)) (Nat.totient_eq_mul_prod_factors m)
  push_cast at H
  rw [H]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  apply prod_le_prod_of_subset_of_le_one₀
  · intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_smallPrimes hp).2.1, hm p hp, hm0⟩
  · intro p hp
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast
      (Nat.prime_of_mem_primeFactors hp).one_le))
  · intro p _ _
    exact sub_le_self _ (by positivity)

open Classical in
private lemma filtered_count_le {f : ℝ → ℝ}
    (hpos : ∀ x, 0 < x → 0 < f x) (hmono : MonotoneOn f (Set.Ioi 0))
    {x y C : ℝ} (hx : 1 ≤ x) (hlog : 0 < logFour x)
    (hcard : ((exceptions x y).card : ℝ) ≤ C * (x * f x / logFour x))
    (hprod : (∏ p ∈ smallPrimes y, (1 - (p : ℝ)⁻¹)) ≤ productConstant / logFour x) :
    ((((Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ) ≤
      (C + productConstant * ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2) * (x * f x / logFour x) := by
  let I := Icc 1 ⌊x⌋₊
  let F := I.filter fun n : ℕ => (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)
  let E := exceptions x y
  let A := ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2
  let w := f x * productConstant / logFour x
  have hx0 : 0 < x := by linarith
  have hw : 0 ≤ w := by
    have hfx := hpos x hx0
    dsimp [w, productConstant]
    positivity
  have hsub : F ⊆ E ∪ (F \ E) := fun n hn => by
    by_cases he : n ∈ E
    · exact mem_union_left _ he
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hn, he⟩)
  have hgood (n : ℕ) (hn : n ∈ F \ E) :
      1 ≤ w * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
    obtain ⟨⟨hnI, hnφ⟩, hnE⟩ :=
      And.imp (fun h => mem_filter.mp h) id (mem_sdiff.mp hn)
    have hposn : 0 < (n : ℝ) := by
      exact_mod_cast (zero_lt_one.trans_le (mem_Icc.mp hnI).1)
    have hnx : (n : ℝ) ≤ x :=
      ((Nat.cast_le (α := ℝ)).mpr (mem_Icc.mp hnI).2).trans (Nat.floor_le hx0.le)
    have hf := hpos (n : ℝ) hposn
    have hfx := hmono hposn hx0 hnx
    have hm : ∀ p ∈ smallPrimes y, p ∣ ArithmeticFunction.sigma 1 n := by
      intro p hp
      by_contra h
      exact hnE (mem_filter.mpr ⟨hnI, p, hp, h⟩)
    calc
      _ = f n * ((n : ℝ) / f n) / n := by field_simp [hf.ne', hposn.ne']
      _ ≤ f x * ((ArithmeticFunction.sigma 1 n : ℝ) *
          (productConstant / logFour x)) / n := by
        have hh := (totient_le_of_smallPrimes_dvd hm).trans
          (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _))
        exact div_le_div_of_nonneg_right
          (mul_le_mul hfx (hnφ.trans hh) (by positivity) (hpos x hx0).le) hposn.le
      _ = _ := by dsimp [w]; ring
  have hsum : ((F \ E).card : ℝ) ≤ w * (A * x) := by
    calc
      _ = ∑ _n ∈ F \ E, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ F \ E, w * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := sum_le_sum hgood
      _ ≤ ∑ n ∈ I, w * ((ArithmeticFunction.sigma 1 n : ℝ) / n) :=
        sum_le_sum_of_subset_of_nonneg ((sdiff_subset).trans (filter_subset ..))
          (fun _ _ _ => by positivity)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left
          (MathlibExt.NumberTheory.AmicableWanted.sum_sigma_div_lt x hx).le hw
  have hle : (F.card : ℝ) ≤ (E.card : ℝ) + ((F \ E).card : ℝ) :=
    by exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  change (F.card : ℝ) ≤ (C + productConstant * A) * (x * f x / logFour x)
  have heq : w * (A * x) = productConstant * A * (x * f x / logFour x) := by
    dsimp [w]
    ring
  linarith only [hle, hcard, hsum, heq, add_mul C (productConstant * A) (x * f x / logFour x)]

private lemma eventually_count_le (f : ℝ → ℝ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hmono : MonotoneOn f (Set.Ioi 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop,
      ((((Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ) ≤
        C * (x * f x / logFour x) := by
  obtain ⟨C, hC, hsieve⟩ := card_free_of_prime_set_le_exp_neg_sum_inv
  let t (x : ℝ) := Real.log (Real.log x)
  let y (x : ℝ) := (t x) ^ (1 / 4 : ℝ)
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hy : Tendsto y atTop atTop := (tendsto_rpow_atTop (by norm_num)).comp ht
  have hlog₃ := Real.tendsto_log_atTop.comp ht
  have hlog₄ : Tendsto logFour atTop atTop := Real.tendsto_log_atTop.comp hlog₃
  have hlog_y := ((isLittleO_log_rpow_atTop (r := 1 / 4) (by norm_num)).comp_tendsto ht).bound
    (show (0 : ℝ) < 1 by norm_num)
  let A := ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2
  let B := (C + 2) / f 1
  have h1 := hpos 1 (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 ≤ A := tsum_nonneg fun _ => by positivity
  have hP : 0 < productConstant := by unfold productConstant; positivity
  refine ⟨B + productConstant * A, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (Real.exp 4)), ht.eventually_ge_atTop 1,
    hy.eventually_ge_atTop (max 2 (max (Real.exp 4) (2 * (137 + eulerError)))),
    hlog₃.eventually_gt_atTop 0, hlog₄.eventually_gt_atTop 0, hlog_y] with x hx ht₁ hy₁ h₃ h₄ hly
  have hx1 := (le_max_left _ _).trans hx
  have hx4 := (le_max_right _ _).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have ht0 : 0 < t x := zero_lt_one.trans_le ht₁
  have hy2 := (le_max_left _ _).trans hy₁
  have hy4 := (le_max_left _ _).trans ((le_max_right _ _).trans hy₁)
  have hylarge := (le_max_right _ _).trans ((le_max_right _ _).trans hy₁)
  have hy0 : 0 < y x := by linarith
  have hpow : y x ^ 4 = t x := by
    change ((t x) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = t x
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hlogeq : Real.log (Real.log (Real.log x)) = 4 * Real.log (y x) := by
    change Real.log (t x) = 4 * Real.log ((t x) ^ (1 / 4 : ℝ))
    rw [Real.log_rpow ht0]
    ring
  have hlogyle : logFour x ≤ y x := by
    change ‖Real.log (t x)‖ ≤ 1 * ‖y x‖ at hly
    rw [one_mul, Real.norm_of_nonneg hy0.le] at hly
    have h₃' : 0 < Real.log (t x) := h₃
    change Real.log (Real.log (t x)) ≤ _
    have h := Real.log_le_sub_one_of_pos h₃'
    exact (by linarith : Real.log (Real.log (t x)) ≤ Real.log (t x)).trans
      ((Real.le_norm_self _).trans hly)
  have hcards := card_exceptions_le hC hsieve hx4 hy2 hpow hylarge
  have hcard : ((exceptions x (y x)).card : ℝ) ≤ B * (x * f x / logFour x) := by
    have hC0 : 0 ≤ C + 2 := by linarith
    have hfx : f 1 ≤ f x := hmono (Set.mem_Ioi.mpr zero_lt_one) (Set.mem_Ioi.mpr hx0) hx1
    calc
      _ ≤ (C + 2) * x / y x := hcards
      _ ≤ (C + 2) * x / logFour x :=
        div_le_div_of_nonneg_left (by positivity) h₄ hlogyle
      _ = B * (x * f 1 / logFour x) := by dsimp [B]; field_simp [h1.ne']
      _ ≤ _ := by gcongr
  exact filtered_count_le hpos hmono hx1 h₄ hcard (prime_product_le hy4 hlogeq h₄)

end MetaMathlibExt.card_totient_sigma_ge_div_isBigO

namespace MetaMathlibExt

/-- **How often $\varphi(\sigma(n)) \ge n / f(n)$.** Write $\log_k$ for the $k$-fold iterated
natural logarithm, so $\log_3 x = \log \log \log x$, and let $\varphi$ be Euler's totient function
and $\sigma$ the sum of divisors. Let $f$ be a real function that is positive and non-decreasing
on $(0, \infty)$ with $f(x) = o(\log_4 x)$ as $x \to \infty$, and let $P_f(x)$ be the number of
integers $n$ with $1 \le n \le x$ and $\varphi(\sigma(n)) \ge n / f(n)$. Then, as $x \to \infty$,
$$
P_f(x) = O\left(\frac{x f(x)}{\log_4 x} +
\frac{x \log_3 x}{(\log x)^{1/\log_3 x} \log_4 x}\right)
$$
and $P_f(x) = o(x)$.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Theorem 2 (`integers-2024-A65-thm-2`). -/
public theorem card_totient_sigma_ge_div_isBigO (f : ℝ → ℝ)
    (hpos : ∀ x, 0 < x → 0 < f x) (hmono : MonotoneOn f (Set.Ioi 0))
    (hf : f =o[atTop] fun x => Real.log (Real.log (Real.log (Real.log x)))) :
    ((fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =O[atTop] fun x =>
        x * f x / Real.log (Real.log (Real.log (Real.log x))) +
          x * Real.log (Real.log (Real.log x)) /
            (Real.log x ^ (1 / Real.log (Real.log (Real.log x))) *
              Real.log (Real.log (Real.log (Real.log x))))) ∧
    ((fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =o[atTop] fun x => x) := by
  obtain ⟨C, hC, hbound⟩ :=
    card_totient_sigma_ge_div_isBigO.eventually_count_le f hpos hmono
  have h₂ := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h₃ : Tendsto (fun x => Real.log (Real.log (Real.log x))) atTop atTop :=
    Real.tendsto_log_atTop.comp h₂
  have h₄ : Tendsto (fun x => Real.log (Real.log (Real.log (Real.log x)))) atTop atTop :=
    Real.tendsto_log_atTop.comp h₃
  have hpos₁ := Real.tendsto_log_atTop.eventually_gt_atTop 0
  have hpos₃ := h₃.eventually_gt_atTop 0
  have hpos₄ := h₄.eventually_gt_atTop 0
  constructor
  · apply IsBigO.of_bound C
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ), hpos₁, hpos₃, hpos₄]
      with x hb hx h₁ h₃ h₄
    have hfx := hpos x hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact hb.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hC.le)
  · refine IsLittleO.of_bound fun c hc => ?_
    have hb := hf.bound (div_pos hc hC)
    filter_upwards [hbound, hb, eventually_gt_atTop (0 : ℝ), hpos₄] with x h hx' hx h₄
    have hfx := hpos x hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hx.le]
    rw [Real.norm_of_nonneg hfx.le, Real.norm_of_nonneg h₄.le] at hx'
    have hdiv := (div_le_iff₀ h₄).mpr hx'
    calc
      _ ≤ C * (x * f x / Real.log (Real.log (Real.log (Real.log x)))) := h
      _ = C * x * (f x / Real.log (Real.log (Real.log (Real.log x)))) := by ring
      _ ≤ C * x * (c / C) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = c * x := by field_simp [hC.ne']

end MetaMathlibExt
