/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.DigitSumDirichletConvolution
public import Mathlib.Analysis.Asymptotics.Defs
import MathlibExt.NumberTheory.Digits.DigitSumArithSqPartialSum
import MathlibExt.NumberTheory.Digits.DigitSumPartialSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Partial sums of iterated digit-sum convolutions

For every natural base `q ≥ 2` and convolution order `k ≥ 2`, the partial sum of the
`k`-fold Dirichlet convolution of the base-`q` digit sum has a main term proportional to
`x * log x ^ (2 * k - 1)` and an error `O(x * log x ^ (2 * k - 2))` as real `x` tends to
infinity. `digitConvolutionCoeff` absorbs the factor `1 / (24 * log q ^ 2)` that the paper
leaves outside its recurrence. The proof uses Abel summation on the shifted logarithm
weight and uses the second convolution as the base of the induction.

## References

* Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
  Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
  pp. 1–13, Theorem 3, equation (2), using Theorems 1 and 2 and Abel summation (3).
* H. Delange, *Sur la fonction sommatoire de la fonction « somme des chiffres »*,
  L'Enseignement Mathématique 21 (1975), pp. 31–47, the arbitrary-base digit-sum formula
  underlying Theorem 1 of Wong and Erdenebat.
* J. R. Trollope, *An Explicit Expression for Binary Digital Sums*, Mathematics Magazine
  41 (1968), pp. 21–25, the binary digit-sum formula extended by Delange.
* Teerapat Srichan, *Averages of the Dirichlet convolution of the binary digital sum*,
  Notes on Number Theory and Discrete Mathematics 25 (2019), no. 1, pp. 122–127,
  Theorem 1.3, the binary predecessor discussed in Section 2 of Wong and Erdenebat.
* `MathlibExt.NumberTheory.Digits.DigitSumPartialSum` and
  `MathlibExt.NumberTheory.Digits.DigitSumArithSqPartialSum`, for
  `digitSum_partialSum_trollopeDelange` and `digitSumArith_sq_partialSum_isBigO`, respectively.
-/

namespace MetaMathlibExt

open Filter Asymptotics Real MeasureTheory intervalIntegral

private noncomputable def digit (q n : ℕ) : ℝ := (Nat.digits q n).sum

private noncomputable def slope (q : ℕ) : ℝ := ((q : ℝ) - 1) / (2 * log q)

private noncomputable def digitPartialSum (q : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, digit q n

private noncomputable def model (q : ℕ) (t : ℝ) : ℝ :=
  slope q * (t * (log t - 1) + 1)

private theorem model_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |digitPartialSum q t - model q t| ≤ C * t := by
  obtain ⟨B, hB⟩ := digitSum_reciprocal_fluctuation_sum_le.series_bounded hq
  obtain ⟨F, hF⟩ := digitSum_reciprocal_fluctuation_sum_le.fluctuation_bddAbove hq
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF ⟨0, rfl⟩)
  refine ⟨F + B + 1 + |slope q|, by positivity, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hn : digit q ⌊t⌋₊ ≤ t := by
    have h := Nat.sum_le_ofDigits (Nat.digits q ⌊t⌋₊) (show 1 ≤ q by omega)
    rw [Nat.ofDigits_digits] at h
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le ht0)
  have hstep0 : 0 ≤ 1 + (⌊t⌋₊ : ℝ) - t := by linarith [Nat.lt_floor_add_one t]
  have hstep1 : 1 + (⌊t⌋₊ : ℝ) - t ≤ 1 := by linarith [Nat.floor_le ht0]
  have hdigit : 0 ≤ digit q ⌊t⌋₊ := Nat.cast_nonneg _
  have hEq : digitPartialSum q t - model q t =
      (t * trollopeDelangeFluctuation q (log t / log q) - trollopeDelangeSeries q t) +
        (1 + ⌊t⌋₊ - t) * digit q ⌊t⌋₊ + slope q * (t - 1) := by
    have h := digitSum_partialSum_trollopeDelange q hq t ht
    change digitPartialSum q t = slope q * t * log t + _ - _ +
      (1 + ⌊t⌋₊ - t) * digit q ⌊t⌋₊ at h
    rw [h, model]
    ring
  rw [hEq]
  calc
    |(t * trollopeDelangeFluctuation q (log t / log q) - trollopeDelangeSeries q t) +
        (1 + ⌊t⌋₊ - t) * digit q ⌊t⌋₊ + slope q * (t - 1)| ≤
      (t * F + B) + t + |slope q| * t := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · exact (abs_sub _ _).trans (by
            rw [abs_mul, abs_of_nonneg ht0]
            exact add_le_add (mul_le_mul_of_nonneg_left (hF ⟨_, rfl⟩) ht0) (hB _))
        · rw [abs_of_nonneg (mul_nonneg hstep0 hdigit)]
          exact (mul_le_of_le_one_left hdigit hstep1).trans hn
        · rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht)]
          exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (abs_nonneg _)
    _ ≤ (F + B + 1 + |slope q|) * t := by
      nlinarith only [mul_le_mul_of_nonneg_left ht hB0]

private theorem hasDerivAt_model (q : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (model q) (slope q * log t) t := by
  have h := (((hasDerivAt_id t).mul ((hasDerivAt_log ht.ne').sub_const 1)).add_const 1).const_mul
    (slope q)
  convert h using 1
  · rfl
  · simp only [one_mul, id_eq, mul_inv_cancel₀ ht.ne', sub_add_cancel]

private noncomputable def kernel (m : ℕ) (x t : ℝ) : ℝ := (log x - log t) ^ m / t

private noncomputable def kernelDeriv (m : ℕ) (x t : ℝ) : ℝ :=
  (-((m : ℝ) * (log x - log t) ^ (m - 1)) - (log x - log t) ^ m) / t ^ 2

private theorem hasDerivAt_kernel (m : ℕ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (kernel m x) (kernelDeriv m x t) t := by
  have h := (((hasDerivAt_log ht.ne').const_sub (log x)).pow m).div (hasDerivAt_id t) ht.ne'
  convert h using 1
  · rfl
  · simp only [kernelDeriv, id_eq, Pi.pow_apply]
    field_simp

private theorem kernelDeriv_bound (m : ℕ) {x t : ℝ} (ht : t ∈ Set.Icc 1 x) :
    |kernelDeriv m x t| ≤ ((m : ℝ) + 1) * (1 + log x) ^ m / t ^ 2 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht.1
  have hu : 0 ≤ log x - log t := sub_nonneg.mpr (log_le_log ht0 ht.2)
  have hL : 1 ≤ 1 + log x := le_add_of_nonneg_right (log_nonneg (ht.1.trans ht.2))
  have huL : log x - log t ≤ 1 + log x := by linarith [log_nonneg ht.1]
  have hp (j : ℕ) (hj : j ≤ m) : (log x - log t) ^ j ≤ (1 + log x) ^ m :=
    (pow_le_pow_left₀ hu huL j).trans (pow_le_pow_right₀ hL hj)
  rw [kernelDeriv, abs_div, abs_of_nonneg (sq_nonneg t),
    show -((m : ℝ) * (log x - log t) ^ (m - 1)) - (log x - log t) ^ m =
      -((m : ℝ) * (log x - log t) ^ (m - 1) + (log x - log t) ^ m) by ring,
    abs_neg, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  rw [add_mul, one_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (hp _ (Nat.sub_le ..)) (Nat.cast_nonneg _))
    (hp _ le_rfl)

-- Abel summation for the step function and integration by parts for its smooth model.
private theorem weightedSum_bound (q : ℕ) (hq : 2 ≤ q) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, digit q n * kernel m x n) -
        ∫ t in (1 : ℝ)..x, kernel m x t * (slope q * log t)| ≤ C * (1 + log x) ^ (m + 1) := by
  obtain ⟨C, hC0, hC⟩ := model_bound q hq
  refine ⟨C * ((m : ℝ) + 2), by positivity, fun x hx ↦ ?_⟩
  let g := kernel m x
  let g' := kernelDeriv m x
  let S := digitPartialSum q
  let D := model q
  let L := 1 + log x
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hL : 1 ≤ L := le_add_of_nonneg_right (log_nonneg hx)
  have ht0 {t : ℝ} (ht : t ∈ Set.Icc 1 x) : 0 < t := zero_lt_one.trans_le ht.1
  have hlog : ContinuousOn log (Set.Icc 1 x) :=
    continuousOn_log.mono fun _ ht ↦ (ht0 ht).ne'
  have hl : ContinuousOn (fun t ↦ log x - log t) (Set.Icc 1 x) := continuousOn_const.sub hlog
  have hg' : ContinuousOn g' (Set.Icc 1 x) :=
    ((continuousOn_const.mul (hl.pow _)).neg.sub (hl.pow _)).div
      (continuousOn_id.pow _) fun _ ht ↦ pow_ne_zero _ (ht0 ht).ne'
  have hgAt (t : ℝ) (ht : t ∈ Set.Icc 1 x) : HasDerivAt g (g' t) t :=
    hasDerivAt_kernel m x (ht0 ht)
  have hderiv : Set.EqOn (deriv g) g' (Set.Icc 1 x) := fun t ht ↦ (hgAt t ht).deriv
  have hzero : digit q 0 = 0 := by simp [digit]
  have hsum (t : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, digit q n) = S t := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hzero, zero_add]
    simp only [← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add, S, digitPartialSum]
  have hg'int : IntervalIntegrable g' volume 1 x := hg'.intervalIntegrable_of_Icc hx
  have hgIcc := (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp hg'int
  have hAbel := sum_mul_eq_sub_integral_mul₀ (f := g) (digit q) hzero x
    (fun t ht ↦ (hgAt t ht).differentiableAt)
    (hgIcc.congr_fun (fun _ ht ↦ (hderiv ht).symm) measurableSet_Icc)
  simp only [hsum, ← intervalIntegral.integral_of_le hx] at hAbel
  have hAbel' : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, digit q n * g n) =
      g x * S x - ∫ t in (1 : ℝ)..x, g' t * S t := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊x⌋₊), Finset.sum_cons, hzero, mul_zero,
      zero_add] at hAbel
    simp only [← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add] at hAbel
    have hi : (∫ t in (1 : ℝ)..x, deriv g t * S t) = ∫ t in (1 : ℝ)..x, g' t * S t :=
      intervalIntegral.integral_congr fun t ht ↦ by rw [hderiv (Set.uIcc_of_le hx ▸ ht)]
    rw [hi] at hAbel
    simpa only [mul_comm (digit q _) (g _)] using hAbel
  have hD1 : D 1 = 0 := by simp [D, model]
  have hparts := integral_mul_deriv_eq_deriv_mul
    (u := g) (v := D) (u' := g') (v' := fun t ↦ slope q * log t)
    (fun t ht ↦ hgAt t (Set.uIcc_of_le hx ▸ ht))
    (fun _ ht ↦ hasDerivAt_model q (ht0 (Set.uIcc_of_le hx ▸ ht)))
    hg'int ((continuousOn_const.mul hlog).intervalIntegrable_of_Icc hx)
  rw [hD1, mul_zero, sub_zero] at hparts
  have hSint : IntervalIntegrable (fun t ↦ g' t * S t) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (integrableOn_mul_sum_Icc (digit q) zero_le_one hgIcc)
  have hDint : IntervalIntegrable (fun t ↦ g' t * D t) volume 1 x := by
    have hDc : ContinuousOn D (Set.Icc 1 x) :=
      continuousOn_const.mul ((continuousOn_id.mul (hlog.sub continuousOn_const)).add
        continuousOn_const)
    exact (hg'.mul hDc).intervalIntegrable_of_Icc hx
  have hEq : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, digit q n * g n) -
      (∫ t in (1 : ℝ)..x, g t * (slope q * log t)) =
      g x * (S x - D x) - ∫ t in (1 : ℝ)..x, g' t * (S t - D t) := by
    simp_rw [mul_sub]
    rw [integral_sub hSint hDint, hAbel', hparts]
    ring
  change |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, digit q n * g n) -
      ∫ t in (1 : ℝ)..x, g t * (slope q * log t)| ≤ _
  rw [hEq]
  have hgx : |g x| ≤ L ^ m / x := by
    simp only [g, kernel, sub_self, abs_div, abs_of_nonneg (pow_nonneg (by norm_num :
      (0 : ℝ) ≤ 0) _), abs_of_pos hx0]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ le_rfl (zero_le_one.trans hL) _) hx0.le
  have hboundary : |g x * (S x - D x)| ≤ C * L ^ m := by
    rw [abs_mul]
    calc
      |g x| * |S x - D x| ≤ (L ^ m / x) * (C * x) :=
        mul_le_mul hgx (hC x hx) (abs_nonneg _) (by positivity)
      _ = C * L ^ m := by field_simp
  let K := C * ((m : ℝ) + 1) * L ^ m
  have hcInt : IntervalIntegrable (fun t : ℝ ↦ K * t⁻¹) volume 1 x :=
    (continuousOn_const.mul (continuousOn_inv₀.mono fun _ ht ↦
      (ht0 ht).ne')).intervalIntegrable_of_Icc hx
  have hinv : (∫ t in (1 : ℝ)..x, t⁻¹) = log x := by
    rw [integral_inv_of_pos zero_lt_one hx0, div_one]
  have hI : |∫ t in (1 : ℝ)..x, g' t * (S t - D t)| ≤ K * log x := by
    rw [← hinv, ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hx
      (Eventually.of_forall fun t ht ↦ ?_) hcInt
    have ht' := Set.Ioc_subset_Icc_self ht
    have hpos := ht0 ht'
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |g' t| * |S t - D t| ≤ (((m : ℝ) + 1) * L ^ m / t ^ 2) * (C * t) :=
        mul_le_mul (kernelDeriv_bound m ht') (hC t ht'.1) (abs_nonneg _) (by positivity)
      _ = K * t⁻¹ := by dsimp [K]; field_simp
  refine (abs_sub _ _).trans ((add_le_add hboundary hI).trans ?_)
  rw [pow_succ]
  dsimp only [K]
  calc
    C * L ^ m + C * ((m : ℝ) + 1) * L ^ m * log x
        ≤ C * L ^ m * L + C * ((m : ℝ) + 1) * L ^ m * L :=
      add_le_add (le_mul_of_one_le_right (by positivity) hL)
        (mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) (by positivity))
    _ = C * ((m : ℝ) + 2) * (L ^ m * L) := by ring

private noncomputable def binomialFactor (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (-1) ^ j / ((j : ℝ) + 2)

private theorem integral_log_moment {x : ℝ} (hx : 1 ≤ x) (j : ℕ) :
    (∫ t in (1 : ℝ)..x, log t ^ (j + 1) / t) = log x ^ (j + 2) / ((j : ℝ) + 2) := by
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun u : ℝ ↦ log u ^ (j + 2) / ((j : ℝ) + 2)) (log t ^ (j + 1) / t) t := by
    convert ((hasDerivAt_log ht.ne').pow (j + 2)).div_const ((j : ℝ) + 2) using 1
    push_cast
    field_simp
  rw [integral_eq_sub_of_hasDerivAt (fun t ht ↦
    hderiv t (zero_lt_one.trans_le (Set.uIcc_of_le hx ▸ ht).1))]
  · simp
  · have hlog : ContinuousOn log (Set.Icc 1 x) :=
      continuousOn_log.mono fun _ ht ↦ (zero_lt_one.trans_le ht.1).ne'
    exact ((hlog.pow _).div continuousOn_id fun _ ht ↦
      (zero_lt_one.trans_le ht.1).ne').intervalIntegrable_of_Icc hx

private theorem integral_kernel (q m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, kernel m x t * (slope q * log t)) =
      slope q * binomialFactor m * log x ^ (m + 2) := by
  let a (j : ℕ) : ℝ := slope q * log x ^ (m - j) * (m.choose j : ℝ) * (-1) ^ j
  have h_expand (t : ℝ) : kernel m x t * (slope q * log t) =
      ∑ j ∈ Finset.range (m + 1), a j * (log t ^ (j + 1) / t) := by
    rw [kernel, sub_eq_add_neg, add_comm, add_pow, Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [← neg_one_mul (log t), mul_pow, pow_succ]
    dsimp only [a]
    ring
  simp_rw [h_expand]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_log_moment hx]
    rw [binomialFactor, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
    rw [show m + 2 = (m - j) + (j + 2) by omega, pow_add]
    dsimp only [a]
    ring
  · intro j _
    have hlog : ContinuousOn log (Set.Icc 1 x) :=
      continuousOn_log.mono fun _ ht ↦ (zero_lt_one.trans_le ht.1).ne'
    exact (continuousOn_const.mul ((hlog.pow _).div continuousOn_id fun _ ht ↦
      (zero_lt_one.trans_le ht.1).ne')).intervalIntegrable_of_Icc hx

private noncomputable def weightedSum (q m : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, digit q n * kernel m x n

private theorem weighted_bound (q : ℕ) (hq : 2 ≤ q) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |weightedSum q m x - slope q * binomialFactor m * log x ^ (m + 2)| ≤
        C * (1 + log x) ^ (m + 1) := by
  obtain ⟨C, hC0, hC⟩ := weightedSum_bound q hq m
  refine ⟨C, hC0, fun x hx ↦ ?_⟩
  simpa only [integral_kernel q m hx, weightedSum] using hC x hx

private theorem reciprocal_upper (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → weightedSum q 0 x ≤ C * (1 + log x) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := weighted_bound q hq 0
  let A := slope q * binomialFactor 0
  refine ⟨C + |A|, by positivity, fun x hx ↦ ?_⟩
  have hL : 1 ≤ (1 + log x) := le_add_of_nonneg_right (log_nonneg hx)
  have hLsq : 1 + log x ≤ (1 + log x) ^ 2 := by nlinarith
  have hlogSq : log x ^ 2 ≤ (1 + log x) ^ 2 :=
    pow_le_pow_left₀ (log_nonneg hx) (by linarith) _
  have h0 : weightedSum q 0 x - A * log x ^ 2 ≤ C * (1 + log x) := by
    simpa only [Nat.zero_add, pow_one] using (abs_le.mp (hC x hx)).2
  calc
    weightedSum q 0 x ≤ C * (1 + log x) + A * log x ^ 2 := by linarith
    _ ≤ C * (1 + log x) ^ 2 + |A| * (1 + log x) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hLsq hC0)
        (mul_le_mul (le_abs_self _) hlogSq (sq_nonneg _) (abs_nonneg _))
    _ = (C + |A|) * (1 + log x) ^ 2 := by ring

private noncomputable def convolutionSum (q k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ k) n : ℝ)

private theorem convolutionSum_succ (q k : ℕ) (x : ℝ) :
    convolutionSum q (k + 1) x =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, digit q d * convolutionSum q k (x / d) := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (digitSumArith q) (digitSumArith q ^ k) ⌊x⌋₊
  simp only [← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add] at h
  rw [convolutionSum, pow_succ', ← Nat.cast_sum, h, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
  have hfloor : ⌊x⌋₊ / d = ⌊x / (d : ℝ)⌋₊ := by
    have h := Nat.mul_cast_floor_div_cancel hd0 (x / (d : ℝ))
    rwa [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hd0)] at h
  rw [Nat.cast_mul, Nat.cast_sum, hfloor, digitSumArith_apply]
  rfl

private theorem square_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |convolutionSum q 2 x - digitConvolutionCoeff q 2 * x * log x ^ 3| ≤
        C * (x * (1 + log x) ^ 2) := by
  let a := digitConvolutionCoeff q 2
  obtain ⟨D, hD⟩ := (digitSumArith_sq_partialSum_isBigO q hq).bound
  obtain ⟨b, hb⟩ := eventually_atTop.mp hD
  let B := max 1 b
  refine ⟨|D| + convolutionSum q 2 B + |a| * B * log B ^ 3, ?_, fun x hx ↦ ?_⟩
  · have hB : 1 ≤ B := le_max_left _ _
    have hsum : 0 ≤ convolutionSum q 2 B := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    have hlog := log_nonneg hB
    positivity
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog := log_nonneg hx
  have hB : 1 ≤ B := le_max_left _ _
  have hlogB := log_nonneg hB
  have hsum : 0 ≤ convolutionSum q 2 B := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hC : |D| ≤ |D| + convolutionSum q 2 B + |a| * B * log B ^ 3 := by
    have : 0 ≤ |a| * B * log B ^ 3 := by positivity
    linarith
  rcases le_or_gt B x with hbx | hxb
  · have h := hb x ((le_max_right _ _).trans hbx)
    have heq : ((q : ℝ) - 1) ^ 2 * x * log x ^ 3 / (24 * log q ^ 2) = a * x * log x ^ 3 := by
      rw [show a = ((q : ℝ) - 1) ^ 2 / (24 * log q ^ 2) from digitConvolutionCoeff_two q]
      ring
    simp only [heq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0.le (sq_nonneg (log x)))] at h
    exact h.trans (mul_le_mul (le_abs_self D |>.trans hC)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog (by linarith) 2) hx0.le)
        (by positivity) (le_trans (abs_nonneg _) hC))
  · have hs : convolutionSum q 2 x ≤ convolutionSum q 2 B := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxb.le))
      exact fun _ _ _ ↦ Nat.cast_nonneg _
    have hmain : |a * x * log x ^ 3| ≤ |a| * B * log B ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_pos hx0, abs_of_nonneg (pow_nonneg hlog _)]
      gcongr
    have hscale : 1 ≤ x * (1 + log x) ^ 2 :=
      one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ (le_add_of_nonneg_right hlog))
    calc
      |convolutionSum q 2 x - a * x * log x ^ 3| ≤
          convolutionSum q 2 B + |a| * B * log B ^ 3 := by
        refine (abs_sub _ _).trans (add_le_add ?_ hmain)
        rwa [abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)]
      _ ≤ (|D| + convolutionSum q 2 B + |a| * B * log B ^ 3) := by linarith [abs_nonneg D]
      _ ≤ (|D| + convolutionSum q 2 B + |a| * B * log B ^ 3) * (x * (1 + log x) ^ 2) :=
        le_mul_of_one_le_right (le_trans (abs_nonneg _) hC) hscale

private theorem convolution_bound (q : ℕ) (hq : 2 ≤ q) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |convolutionSum q k x - digitConvolutionCoeff q k * x * log x ^ (2 * k - 1)| ≤
        C * (x * (1 + log x) ^ (2 * k - 2)) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using square_bound q hq
  | succ k hk ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨R, hR0, hR⟩ := reciprocal_upper q hq
    let m := 2 * k - 1
    let p := 2 * k - 2
    let a := digitConvolutionCoeff q k
    obtain ⟨W, hW0, hW⟩ := weighted_bound q hq m
    have hm : m + 2 = 2 * (k + 1) - 1 := by dsimp [m]; omega
    have hp : p + 2 = 2 * (k + 1) - 2 := by dsimp [p]; omega
    have hmp : m + 1 = p + 2 := by dsimp [m, p]; omega
    have hcoeff : digitConvolutionCoeff q (k + 1) = a * slope q * binomialFactor m := by
      rw [digitConvolutionCoeff_succ q hk, binomialFactor, show 2 * (k + 1) - 3 = m by
        dsimp [m]; omega]
      rfl
    refine ⟨C * R + |a| * W, by positivity, fun x hx ↦ ?_⟩
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    let L := 1 + log x
    have hL : 0 ≤ L := by dsimp [L]; linarith [log_nonneg hx]
    let E (t : ℝ) := convolutionSum q k t - a * t * log t ^ m
    let I := Finset.Icc 1 ⌊x⌋₊
    have hdBounds {d : ℕ} (hd : d ∈ I) : (1 : ℝ) ≤ d ∧ (d : ℝ) ≤ x :=
      ⟨by exact_mod_cast (Finset.mem_Icc.mp hd).1,
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hd).2).trans (Nat.floor_le hx0.le)⟩
    have hlogDiv {d : ℕ} (hd : d ∈ I) : log (x / (d : ℝ)) = log x - log d :=
      log_div hx0.ne' (zero_lt_one.trans_le (hdBounds hd).1).ne'
    have hdecompose : convolutionSum q (k + 1) x -
        digitConvolutionCoeff q (k + 1) * x * log x ^ (2 * (k + 1) - 1) =
        (∑ d ∈ I, digit q d * E (x / d)) + a * x *
          (weightedSum q m x - slope q * binomialFactor m * log x ^ (m + 2)) := by
      rw [convolutionSum_succ, hcoeff, ← hm, mul_sub, weightedSum, Finset.mul_sum, ← add_sub_assoc,
        ← Finset.sum_add_distrib]
      have heq : (∑ d ∈ I, (digit q d * E (x / d) +
          a * x * (digit q d * kernel m x d))) =
          ∑ d ∈ I, digit q d * convolutionSum q k (x / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        dsimp only [E]
        rw [kernel, ← hlogDiv hd]
        ring
      rw [heq]
      ring
    rw [hdecompose, ← hp]
    have hweighted : |a * x * (weightedSum q m x -
        slope q * binomialFactor m * log x ^ (m + 2))| ≤ (|a| * W) * (x * L ^ (p + 2)) := by
      rw [abs_mul, abs_mul, abs_of_pos hx0]
      calc
        |a| * x * |weightedSum q m x - slope q * binomialFactor m * log x ^ (m + 2)|
            ≤ |a| * x * (W * L ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left (hW x hx) (by positivity)
        _ = (|a| * W) * (x * L ^ (p + 2)) := by rw [hmp]; ring
    have hterm (d : ℕ) (hd : d ∈ I) :
        |digit q d * E (x / d)| ≤ (C * x * L ^ p) * (digit q d / d) := by
      obtain ⟨hd1, hdx⟩ := hdBounds hd
      have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
      have hlow : 1 ≤ x / (d : ℝ) := (one_le_div hd0).mpr hdx
      have hhigh : x / (d : ℝ) ≤ x := div_le_self hx0.le hd1
      have hs : 0 ≤ digit q d := Nat.cast_nonneg _
      have hlog := log_nonneg hlow
      have hlog' := log_le_log (div_pos hx0 hd0) hhigh
      have hpow : (1 + log (x / (d : ℝ))) ^ p ≤ L ^ p :=
        pow_le_pow_left₀ (by linarith) (by dsimp [L]; linarith) p
      rw [abs_mul, abs_of_nonneg hs]
      calc
        digit q d * |E (x / d)| ≤ digit q d * (C * (x / d * (1 + log (x / d)) ^ p)) :=
          mul_le_mul_of_nonneg_left (hC _ hlow) hs
        _ ≤ digit q d * (C * (x / d * L ^ p)) := by gcongr
        _ = (C * x * L ^ p) * (digit q d / d) := by ring
    have herror : |∑ d ∈ I, digit q d * E (x / d)| ≤ (C * R) * (x * L ^ (p + 2)) := by
      have hsum : |∑ d ∈ I, digit q d * E (x / d)| ≤ (C * x * L ^ p) * weightedSum q 0 x := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp only [weightedSum, kernel, pow_zero, one_div, ← div_eq_mul_inv, Finset.mul_sum]
        exact Finset.sum_le_sum hterm
      refine hsum.trans ((mul_le_mul_of_nonneg_left (hR x hx) (by positivity)).trans_eq ?_)
      rw [pow_add]
      ring
    exact (abs_add_le _ _).trans ((add_le_add herror hweighted).trans_eq (by ring))

/-- **Partial sums of the iterated digit-sum convolutions.** Let $q \ge 2$ be an integer, let
$s_q(n)$ be the sum of the base-$q$ digits of $n$, let $s_q^{(k)}$ be the $k$-fold Dirichlet
convolution $s_q * \cdots * s_q$, and let $a(k)$ be the base-$q$ digit-convolution coefficients.
For every integer $k \ge 2$,
$$\sum_{1 \le n \le x} s_q^{(k)}(n) = a(k) \, x \log^{2k-1} x + O(x \log^{2k-2} x)$$
as $x \to \infty$ through the reals.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3 (`integers-2026-A43-thm-3`), equation (2). -/
public theorem digitSumArith_pow_partialSum_isBigO (q : ℕ) (hq : 2 ≤ q) (k : ℕ)
    (hk : 2 ≤ k) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ k) n : ℝ) -
        digitConvolutionCoeff q k * x * log x ^ (2 * k - 1)) =O[atTop]
      (fun x => x * log x ^ (2 * k - 2)) := by
  obtain ⟨C, hC0, hC⟩ := convolution_bound q hq k hk
  let p := 2 * k - 2
  refine IsBigO.of_bound (C * 2 ^ p) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), tendsto_log_atTop.eventually_ge_atTop 1] with x hx hl
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hl0 : 0 ≤ log x := zero_le_one.trans hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 (pow_nonneg hl0 _))]
  refine (hC x hx).trans ?_
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + log x)
    (by linarith : 1 + log x ≤ 2 * log x) p
  change C * (x * (1 + log x) ^ p) ≤ C * 2 ^ p * (x * log x ^ p)
  calc
    C * (x * (1 + log x) ^ p) ≤ C * (x * (2 * log x) ^ p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hx0) hC0
    _ = C * 2 ^ p * (x * log x ^ p) := by rw [mul_pow]; ring

end MetaMathlibExt
