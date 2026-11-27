/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitTotientFormula
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Average order of the square-splitting totient function

`MetaMathlibExt.squareSplitTotient_sum_asymptotic` gives the absolutely convergent Euler product
and the average order from Champak Talukdar and Helen K. Saikia,
*A Square-Splitting A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 8.
-/

namespace MetaMathlibExt

open Asymptotics Filter Topology

private lemma primeCorrection_le (p : Nat.Primes) :
    |-(1 / ((p : ℕ) : ℝ) ^ 2) + (((p : ℕ) : ℝ) - 1) ^ 2 /
      ((p : ℕ) : ℝ) ^ 5| ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by
  have hp : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
  have hpow : ((p : ℕ) : ℝ) ^ 2 ≤ ((p : ℕ) : ℝ) ^ 3 := by
    exact pow_le_pow_right₀ (by linarith) (by decide)
  have hsq : (((p : ℕ) : ℝ) - 1) ^ 2 ≤ ((p : ℕ) : ℝ) ^ 3 := by
    nlinarith
  have hratio : (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5 ≤
      1 / ((p : ℕ) : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hp0 5) (pow_pos hp0 2)).mpr
    calc
      _ ≤ ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = _ := by ring
  apply abs_le.mpr
  constructor
  · have : 0 ≤ (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5 := by positivity
    linarith
  · have : 0 ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by positivity
    linarith

private lemma primeCorrection_summable :
    Summable (fun p : Nat.Primes =>
      |-(1 / ((p : ℕ) : ℝ) ^ 2) + (((p : ℕ) : ℝ) - 1) ^ 2 /
        ((p : ℕ) : ℝ) ^ 5|) := by
  exact ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).subtype
    Nat.Prime).of_nonneg_of_le (fun _ => abs_nonneg _) primeCorrection_le

private noncomputable def inverseId : ArithmeticFunction ℤ :=
  ArithmeticFunction.pmul ArithmeticFunction.moebius ArithmeticFunction.id

private lemma inverseId_multiplicative : inverseId.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.pmul ArithmeticFunction.isMultiplicative_id.natCast

private lemma inverseId_mul_id :
    inverseId * (ArithmeticFunction.id : ArithmeticFunction ℤ) = 1 := by
  ext n
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => inverseId a * (ArithmeticFunction.id : ArithmeticFunction ℤ) b)]
  have he (d : ℕ) (hd : d ∈ n.divisors) :
      inverseId d * (ArithmeticFunction.id : ArithmeticFunction ℤ) (n / d) =
        (n : ℤ) * ArithmeticFunction.moebius d := by
    simp only [inverseId, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply]
    rw [mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    ring
  rw [Finset.sum_congr rfl he, ← Finset.mul_sum]
  have hμ := ArithmeticFunction.moebius_mul_coe_zeta
  have hsum : ∑ d ∈ n.divisors, ArithmeticFunction.moebius d =
      (1 : ArithmeticFunction ℤ) n := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, hμ]
  rw [hsum]
  by_cases hn : n = 1 <;> simp [hn]

private lemma phi_prime_pow (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p : ℕ) (hp : p.Prime) :
    φ p = (p : ℤ) - 1 ∧ φ (p ^ 2) = (p : ℤ) ^ 2 - 1 ∧
      φ (p ^ 3) = ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 1) ∧
      ∀ k, φ (p ^ (k + 4)) = (p : ℤ) ^ 2 * φ (p ^ (k + 2)) := by
  obtain ⟨_, _, hpp, _⟩ := squareSplitTotient_formula φ hφ
  obtain ⟨h₁, hb⟩ := hpp p hp
  refine ⟨h₁, by simpa using (hb 1 le_rfl).1, by simpa using (hb 1 le_rfl).2, fun k => ?_⟩
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m + 4 = 2 * (m + 2) by omega, show m + m + 2 = 2 * (m + 1) by omega,
      (hb (m + 2) (by omega)).1, (hb (m + 1) (by omega)).1,
      show 2 * (m + 2) - 2 = 2 * m + 2 by omega, show 2 * (m + 1) - 2 = 2 * m by omega]
    ring
  · rw [show 2 * m + 1 + 4 = 2 * (m + 2) + 1 by omega,
      show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega,
      (hb (m + 2) (by omega)).2, (hb (m + 1) (by omega)).2,
      show 2 * (m + 2) - 2 = 2 * m + 2 by omega, show 2 * (m + 1) - 2 = 2 * m by omega]
    ring

private noncomputable def correction (φ : ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  φ * inverseId

private lemma correction_multiplicative (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) : (correction φ).IsMultiplicative :=
  (squareSplitTotient_formula φ hφ).1.mul inverseId_multiplicative

private lemma eq_id_mul_correction (φ : ArithmeticFunction ℤ) :
    φ = (ArithmeticFunction.id : ArithmeticFunction ℤ) * correction φ := by
  rw [correction, mul_left_comm, mul_comm (ArithmeticFunction.id : ArithmeticFunction ℤ),
    inverseId_mul_id, mul_one]

private lemma correction_prime_pow_succ (φ : ArithmeticFunction ℤ) (p k : ℕ) (hp : p.Prime) :
    correction φ (p ^ (k + 1)) = φ (p ^ (k + 1)) - (p : ℤ) * φ (p ^ k) := by
  rw [correction, mul_comm φ inverseId, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => inverseId a * φ b),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz (i : ℕ) : inverseId (p ^ (i + 2)) = 0 := by
    simp [inverseId, ArithmeticFunction.moebius_apply_prime_pow hp (by omega : i + 2 ≠ 0)]
  have ht : ∑ i ∈ Finset.range k,
      inverseId (p ^ (i + 1 + 1)) * φ (p ^ (k + 1) / p ^ (i + 1 + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show i + 1 + 1 = i + 2 by omega, hz, zero_mul]
  have hdiv : p ^ (k + 1) / p = p ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [ht]
  simp [inverseId, ArithmeticFunction.moebius_apply_prime hp, hdiv, sub_eq_add_neg, add_comm]

private lemma correction_prime (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p : ℕ) (hp : p.Prime) :
    correction φ p = -1 := by
  obtain ⟨_, hone, _, _⟩ := squareSplitTotient_formula φ hφ
  have h := correction_prime_pow_succ φ p 0 hp
  simp only [zero_add, pow_one, pow_zero] at h
  rw [h, (phi_prime_pow φ hφ p hp).1, hone]
  ring

private lemma correction_square (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p : ℕ) (hp : p.Prime) :
    correction φ (p ^ 2) = (p : ℤ) - 1 := by
  obtain ⟨h₁, h₂, _, _⟩ := phi_prime_pow φ hφ p hp
  have h := correction_prime_pow_succ φ p 1 hp
  simp only [Nat.reduceAdd, pow_one] at h
  rw [h, h₂, h₁]
  ring

private lemma correction_prime_pow_tail (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p k : ℕ) (hp : p.Prime) :
    correction φ (p ^ (k + 3)) = (-(p : ℤ)) ^ k * (1 - (p : ℤ) ^ 2) := by
  obtain ⟨_, h₂, h₃, hstep⟩ := phi_prime_pow φ hφ p hp
  induction k with
  | zero =>
    rw [show 0 + 3 = 2 + 1 by rfl, correction_prime_pow_succ φ p 2 hp]
    change φ (p ^ 3) - (p : ℤ) * φ (p ^ 2) = (-(p : ℤ)) ^ 0 * (1 - (p : ℤ) ^ 2)
    rw [h₃, h₂]
    ring
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by omega, correction_prime_pow_succ φ p (k + 3) hp,
      show k + 3 + 1 = k + 4 by omega, hstep k, show k + 3 = (k + 2) + 1 by omega]
    have hh := correction_prime_pow_succ φ p (k + 2) hp
    rw [show k + 2 + 1 = k + 3 by omega, ih] at hh
    rw [pow_succ (-(p : ℤ)) k]
    change (p : ℤ) ^ 2 * φ (p ^ (k + 2)) - (p : ℤ) *
      φ (p ^ (k + 3)) = (-(p : ℤ)) ^ k * -(p : ℤ) * (1 - (p : ℤ) ^ 2)
    linear_combination (p : ℤ) * hh

private lemma correction_prime_pow_bound (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (p k : ℕ) (hp : p.Prime)
    (hk : k ≠ 0) : |(correction φ (p ^ k) : ℝ)| ≤ (p : ℝ) ^ (k - 1) := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp₀ : (0 : ℝ) ≤ p := by positivity
  rcases k with _ | _ | _ | k
  · exact (hk rfl).elim
  · change |(correction φ (p ^ 1) : ℝ)| ≤ (p : ℝ) ^ 0
    rw [pow_one, correction_prime φ hφ p hp]
    norm_num
  · change |(correction φ (p ^ 2) : ℝ)| ≤ (p : ℝ) ^ 1
    rw [correction_square φ hφ p hp]
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, pow_one]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [correction_prime_pow_tail φ hφ p k hp]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast, Int.cast_sub,
      Int.cast_one, abs_mul, abs_pow, abs_neg, abs_of_nonneg hp₀,
      show k + 3 - 1 = k + 2 by omega, pow_add]
    have hsq : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
    rw [abs_sub_comm, abs_of_nonneg hsq]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)


private lemma correction_weighted_summable (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (s : ℝ)
    (hs : 1 < s) :
    Summable (fun n : ℕ => |(correction φ n : ℝ)| / (n : ℝ) ^ s) := by
  let f (n : ℕ) : ℝ := |(correction φ n : ℝ)| / (n : ℝ) ^ s
  let A (p : ℕ) : ℝ := (p : ℝ) ^ (-s)
  let r : ℝ := 2 ^ (1 - s)
  let B (k : ℕ) : ℝ := r ^ (k - 1)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hA : Summable A := Real.summable_nat_rpow.mpr (by linarith : -s < -1)
  have hB : Summable B := by
    apply (summable_nat_add_iff 1).mp
    simpa [B] using summable_geometric_of_lt_one hr.le hr₁
  have hAB := hA.mul_of_nonneg hB (fun p => by dsimp [A]; positivity)
    (fun k => by dsimp [B]; positivity)
  have hprod := summable_finsetProd_of_summable_nonneg (fun i => by
    dsimp [A, B]
    positivity) hAB
  let graph (m : ℕ) := (m + 1).factorization.graph
  have hinj : Function.Injective graph := by
    intro m n h
    have he := Nat.factorization_inj (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)
      (Finsupp.graph_inj.mp h)
    exact Nat.succ.inj he
  have hmul (m n : ℕ) (h : m.Coprime n) : f (m * n) = f m * f n := by
    dsimp [f]
    rw [(correction_multiplicative φ hφ).map_mul_of_coprime h, Int.cast_mul, abs_mul,
      Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
    exact mul_div_mul_comm _ _ _ _
  have hone : f 1 = 1 := by simp [f, (correction_multiplicative φ hφ).1]
  have hlocal (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) : f (p ^ k) ≤ A p * B k := by
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have he : (p : ℝ) ^ (k - 1) / ((p : ℝ) ^ k) ^ s =
        (p : ℝ) ^ (-s) * ((p : ℝ) ^ (1 - s)) ^ (k - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp₀.le,
        ← Real.rpow_sub hp₀, ← Real.rpow_mul_natCast hp₀.le,
        ← Real.rpow_add hp₀]
      congr 1
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk), Nat.cast_one]
      ring
    calc
      f (p ^ k) ≤ (p : ℝ) ^ (k - 1) / ((p : ℝ) ^ k) ^ s := by
        dsimp [f]
        rw [Nat.cast_pow]
        exact div_le_div_of_nonneg_right (correction_prime_pow_bound φ hφ p k hp hk) (by positivity)
      _ = (p : ℝ) ^ (-s) * ((p : ℝ) ^ (1 - s)) ^ (k - 1) := he
      _ ≤ A p * B k := by
        dsimp [A, B, r]
        have hpr : (p : ℝ) ^ (1 - s) ≤ (2 : ℝ) ^ (1 - s) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp₂ (by linarith)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_nonneg hp₀.le _) hpr _) (by positivity)
  change Summable f
  apply (summable_nat_add_iff 1).mp
  apply (hprod.comp_injective hinj).of_nonneg_of_le (fun _ => by dsimp [f]; positivity)
  intro m
  rw [Nat.multiplicative_factorization f hmul hone (Nat.succ_ne_zero m)]
  simp only [Finsupp.prod, Function.comp_apply, graph, Finsupp.graph, Finset.prod_map]
  apply Finset.prod_le_prod₀ (fun _ _ => by dsimp [f]; positivity)
  intro p hp
  exact hlocal p ((m + 1).factorization p) (Nat.prime_of_mem_primeFactors hp)
    (Finsupp.mem_support_iff.mp hp)


private lemma correction_euler_product (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    (∑' n : ℕ, (correction φ n : ℝ) / (n : ℝ) ^ 2) =
      ∏' p : Nat.Primes,
        (1 - 1 / ((p : ℕ) : ℝ) ^ 2 + (((p : ℕ) : ℝ) - 1) ^ 2 /
          ((p : ℕ) : ℝ) ^ 5) := by
  let f (n : ℕ) : ℝ := (correction φ n : ℝ) / (n : ℝ) ^ 2
  have hnorm : Summable (fun n => ‖f n‖) := by
    simpa only [f, norm_div, norm_pow, Real.norm_natCast, Real.norm_eq_abs, Nat.abs_cast,
      Real.rpow_two] using correction_weighted_summable φ hφ 2 (by norm_num)
  have hone : f 1 = 1 := by simp [f, (correction_multiplicative φ hφ).1]
  have hzero : f 0 = 0 := by simp [f]
  have hmul {m n : ℕ} (h : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, (correction_multiplicative φ hφ).map_mul_of_coprime h, Int.cast_mul,
      Nat.cast_mul, mul_pow]
    exact mul_div_mul_comm _ _ _ _
  rw [← EulerProduct.eulerProduct_tprod hone hmul hnorm hzero]
  apply tprod_congr
  intro p
  rcases p with ⟨p, hp⟩
  change (∑' k : ℕ, f (p ^ k)) =
    1 - 1 / (p : ℝ) ^ 2 + ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ 5
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hseries : Summable (fun k : ℕ => f (p ^ k)) :=
    hnorm.of_norm.comp_injective (Nat.pow_right_injective hp.two_le)
  rw [← hseries.sum_add_tsum_nat_add 3]
  have htail (k : ℕ) : f (p ^ (k + 3)) =
      (1 - (p : ℝ) ^ 2) / (p : ℝ) ^ 6 *
        (-(1 / (p : ℝ))) ^ k := by
    dsimp only [f]
    rw [correction_prime_pow_tail φ hφ _ k hp]
    simp only [Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_natCast, Int.cast_sub, Int.cast_one, Nat.cast_pow, Nat.cast_mul,
      pow_add,
      mul_pow]
    rw [neg_pow (p : ℝ) k, neg_pow (1 / (p : ℝ)) k]
    simp only [div_pow, one_pow]
    field_simp
  simp_rw [htail]
  have hr : ‖-(1 / (p : ℝ))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one hp₀).mpr (by linarith)
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, f, Nat.pow_zero, Nat.pow_one,
    (correction_multiplicative φ hφ).1, correction_prime φ hφ _ hp, correction_square φ hφ _ hp,
    Int.cast_one, Int.cast_neg, Int.cast_sub, Int.cast_natCast, zero_add,
    Nat.cast_pow]
  field_simp
  ring


private lemma sum_id (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (n : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private lemma phi_partial_sum (φ : ArithmeticFunction ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (φ n : ℝ)) =
      ∑ d ∈ Finset.Ioc 0 N, (correction φ d : ℝ) *
        ((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (correction φ)
    (ArithmeticFunction.id : ArithmeticFunction ℤ) N
  rw [mul_comm (correction φ), ← eq_id_mul_correction φ] at h
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_sum, Int.cast_mul, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply, Int.cast_natCast, sum_id] at hcast
  simpa only [mul_div_assoc, mul_assoc] using hcast

private lemma sum_id_floor_error (y : ℝ) (hy : 1 ≤ y) :
    |(⌊y⌋₊ : ℝ) * ((⌊y⌋₊ : ℝ) + 1) / 2 - y ^ 2 / 2| ≤ 2 * y := by
  have hy₀ : 0 ≤ y := by linarith
  have hq₀ : (0 : ℝ) ≤ ⌊y⌋₊ := by positivity
  have hq := Nat.floor_le hy₀
  have hq' := Nat.lt_floor_add_one y
  have hs₁ : (⌊y⌋₊ : ℝ) ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hq₀ hy₀).mpr hq
  have hs₂ : (y - 1) ^ 2 ≤ (⌊y⌋₊ : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith) hq₀).mpr (by linarith)
  apply abs_le.mpr
  constructor <;> nlinarith


private lemma phi_sum_bound (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) (ε : ℝ)
    (hε : 0 < ε) (hε₁ : ε < 1) :
    (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (φ n : ℝ)) -
      (∑' n : ℕ, (correction φ n : ℝ) / (n : ℝ) ^ 2) / 2 * x ^ 2)
      =O[Filter.atTop] fun x => x ^ (1 + ε) := by
  let a (n : ℕ) : ℝ := |(correction φ n : ℝ)| / (n : ℝ) ^ (1 + ε)
  let w (n : ℕ) : ℝ := (correction φ n : ℝ) / (n : ℝ) ^ 2
  let C : ℝ := ∑' n, a n
  have ha : Summable a := correction_weighted_summable φ hφ (1 + ε) (by linarith)
  have ha₀ (n : ℕ) : 0 ≤ a n := by dsimp [a]; positivity
  have hC : 0 ≤ C := tsum_nonneg ha₀
  have hw : Summable (fun n => ‖w n‖) := by
    simpa only [w, norm_div, norm_pow, Real.norm_natCast, Real.norm_eq_abs, Nat.abs_cast,
      Real.rpow_two] using correction_weighted_summable φ hφ 2 (by norm_num)
  apply Asymptotics.IsBigO.of_bound (3 * C)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  have hx₀ : 0 < x := by linarith
  let S := Finset.Ioc 0 ⌊x⌋₊
  let q (d : ℕ) : ℝ := ((⌊x⌋₊ / d : ℕ) : ℝ)
  let e (d : ℕ) : ℝ := (correction φ d : ℝ) *
    (q d * (q d + 1) / 2 - (x / (d : ℝ)) ^ 2 / 2)
  have hxpow : x * x ^ ε = x ^ (1 + ε) := by
    rw [Real.rpow_add hx₀, Real.rpow_one]
  have hxtail : x ^ 2 / 2 * x ^ (ε - 1) = x ^ (1 + ε) / 2 := by
    rw [← Real.rpow_two, div_mul_eq_mul_div, ← Real.rpow_add hx₀]
    congr 2
    ring
  have hinside (d : ℕ) (hd : d ∈ S) : ‖e d‖ ≤ 2 * x ^ (1 + ε) * a d := by
    obtain ⟨hd₀, hdn⟩ := Finset.mem_Ioc.mp hd
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd₀
    have hdx : (d : ℝ) ≤ x :=
      (show (d : ℝ) ≤ (⌊x⌋₊ : ℝ) from by exact_mod_cast hdn).trans (Nat.floor_le hx₀.le)
    have hxy : 1 ≤ x / (d : ℝ) := (le_div_iff₀ hd').mpr (by simpa using hdx)
    have hq : q d = (⌊x / (d : ℝ)⌋₊ : ℝ) := by
      dsimp only [q]
      rw [← Nat.floor_div_natCast x d]
    have hpow : (d : ℝ) ^ ε ≤ x ^ ε := Real.rpow_le_rpow hd'.le hdx hε.le
    have he : |(correction φ d : ℝ)| * (2 * (x / (d : ℝ))) =
        2 * x * (d : ℝ) ^ ε * a d := by
      dsimp [a]
      rw [Real.rpow_add hd', Real.rpow_one]
      field_simp
    calc
      ‖e d‖ = |(correction φ d : ℝ)| *
          |q d * (q d + 1) / 2 - (x / (d : ℝ)) ^ 2 / 2| := by
        dsimp only [e]
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |(correction φ d : ℝ)| * (2 * (x / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left (by rw [hq]; exact sum_id_floor_error _ hxy) (abs_nonneg _)
      _ = 2 * x * (d : ℝ) ^ ε * a d := he
      _ ≤ 2 * x * x ^ ε * a d := by gcongr
      _ = 2 * x ^ (1 + ε) * a d := by rw [mul_assoc 2 x (x ^ ε), hxpow]
  have hfinite : ‖∑ d ∈ S, e d‖ ≤ 2 * x ^ (1 + ε) * C := by
    calc
      _ ≤ ∑ d ∈ S, ‖e d‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ S, 2 * x ^ (1 + ε) * a d := Finset.sum_le_sum hinside
      _ = 2 * x ^ (1 + ε) * ∑ d ∈ S, a d := (Finset.mul_sum ..).symm
      _ ≤ 2 * x ^ (1 + ε) * C :=
        mul_le_mul_of_nonneg_left (ha.sum_le_tsum S (fun d _ => ha₀ d)) (by positivity)
  have houtside (d : {d : ℕ // d ∉ S}) : ‖w d‖ ≤ x ^ (ε - 1) * a d := by
    rcases eq_or_ne (d : ℕ) 0 with hd | hd
    · simp [w, a, hd]
    have hd₀ : (0 : ℝ) < (d : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hdn : ⌊x⌋₊ < (d : ℕ) := by
      have h := d.property
      simp only [S, Finset.mem_Ioc, not_and] at h
      exact lt_of_not_ge (h (Nat.pos_of_ne_zero hd))
    have hxd : x ≤ (d : ℕ) := (Nat.lt_of_floor_lt hdn).le
    have hpow : ((d : ℕ) : ℝ) ^ (ε - 1) ≤ x ^ (ε - 1) :=
      Real.rpow_le_rpow_of_nonpos hx₀ hxd (by linarith)
    have he : ‖w d‖ = ((d : ℕ) : ℝ) ^ (ε - 1) * a d := by
      dsimp only [w, a]
      change |(correction φ d : ℝ) / ((d : ℕ) : ℝ) ^ 2| = _
      rw [abs_div, abs_pow, abs_of_pos hd₀]
      rw [show 1 + ε = (ε - 1) + 2 by ring, Real.rpow_add hd₀, Real.rpow_two]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hpow (ha₀ d)
  have htail : ‖∑' d : {d : ℕ // d ∉ S}, w d‖ ≤ x ^ (ε - 1) * C := by
    have haTail := ha.subtype (fun d => d ∉ S)
    have he := ha.sum_add_tsum_subtype_compl S
    have htailC : ∑' d : {d : ℕ // d ∉ S}, a d ≤ C := by
      dsimp [C]
      have hs₀ : 0 ≤ ∑ d ∈ S, a d := Finset.sum_nonneg (fun d _ => ha₀ d)
      linarith
    calc
      _ ≤ ∑' d : {d : ℕ // d ∉ S}, ‖w d‖ :=
        norm_tsum_le_tsum_norm (hw.subtype (fun d => d ∉ S))
      _ ≤ ∑' d : {d : ℕ // d ∉ S}, x ^ (ε - 1) * a d :=
        (hw.subtype (fun d => d ∉ S)).tsum_le_tsum houtside (haTail.mul_left _)
      _ = x ^ (ε - 1) * ∑' d : {d : ℕ // d ∉ S}, a d := tsum_mul_left
      _ ≤ x ^ (ε - 1) * C := mul_le_mul_of_nonneg_left htailC (by positivity)
  have hsplit : (∑ n ∈ S, (φ n : ℝ)) - (∑' n, w n) / 2 * x ^ 2 =
      (∑ d ∈ S, e d) - x ^ 2 / 2 * ∑' d : {d : ℕ // d ∉ S}, w d := by
    rw [hw.of_norm.sum_add_tsum_subtype_compl S |>.symm]
    dsimp [S]
    rw [phi_partial_sum φ]
    dsimp [e, q, w]
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← mul_assoc]
    have heq : ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, (correction φ d : ℝ) * (x / (d : ℝ)) ^ 2 / 2 =
        (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, (correction φ d : ℝ) / (d : ℝ) ^ 2) * x ^ 2 / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d _
      rw [div_pow]
      ring
    rw [heq]
    ring
  change ‖(∑ n ∈ S, (φ n : ℝ)) - (∑' n, w n) / 2 * x ^ 2‖ ≤
    3 * C * ‖x ^ (1 + ε)‖
  rw [hsplit]
  calc
    _ ≤ ‖∑ d ∈ S, e d‖ + ‖x ^ 2 / 2 * ∑' d : {d : ℕ // d ∉ S}, w d‖ := norm_sub_le _ _
    _ ≤ 2 * x ^ (1 + ε) * C + x ^ 2 / 2 * (x ^ (ε - 1) * C) := by
      rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ x ^ 2 / 2 by positivity)]
      exact add_le_add hfinite (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = (2 + 1 / 2) * C * x ^ (1 + ε) := by rw [← mul_assoc, hxtail]; ring
    _ ≤ 3 * C * ‖x ^ (1 + ε)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [Real.rpow_pos_of_pos hx₀ (1 + ε)]


/-- **Average order of the square-splitting totient function.** Let $A(n)$ be the set of
square-splitting divisors of $n$, and let $\varphi_\star$ be any integer-valued arithmetic function
with $\sum_{d \in A(n)} \varphi_\star(d) = n$ for every $n \ge 1$. Then the product
$M = \prod_p \left(1 - \frac{1}{p^2} + \frac{(p-1)^2}{p^5}\right)$ converges absolutely, that is,
$\sum_p \left|\frac{(p-1)^2}{p^5} - \frac{1}{p^2}\right| < \infty$, and for every
$0 < \varepsilon < 1/2$,
$$\sum_{1 \le n \le x} \varphi_\star(n) = \frac{M}{2}\,x^2 + O(x^{1+\varepsilon})
\quad (x \to \infty).$$

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 8
(`integers-2026-A56-thm-8`). -/
public theorem squareSplitTotient_sum_asymptotic (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    Summable (fun p : Nat.Primes =>
      |-(1 / ((p : ℕ) : ℝ) ^ 2) + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5|) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (φ n : ℝ) -
        (∏' p : Nat.Primes,
          (1 - 1 / ((p : ℕ) : ℝ) ^ 2 + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5)) / 2 * x ^ 2)
        =O[atTop] fun x => x ^ (1 + ε) := by
  refine ⟨primeCorrection_summable, ?_⟩
  intro ε hε hε₁
  have h := phi_sum_bound φ hφ ε hε (by linarith)
  have hsets (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N :=
    (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) N).symm
  simpa only [hsets, correction_euler_product φ hφ] using h


end MetaMathlibExt
