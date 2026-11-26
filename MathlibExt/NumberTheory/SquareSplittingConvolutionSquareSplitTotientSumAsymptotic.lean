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
import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Algebra.BigOperators.Intervals
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

private theorem split_coords {u v : ℕ} (hu : Squarefree u) (hv : v ≠ 0) :
    squareSplitU (u * v ^ 2) = u ∧ squareSplitV (u * v ^ 2) = v := by
  have hn := mul_ne_zero hu.ne_zero (pow_ne_zero 2 hv)
  have hroot : Nat.floorRoot 2 (u * v ^ 2) = v := by
    apply Nat.eq_of_factorization_eq (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn⟩) hv
    intro p
    rw [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.factorization_mul hu.ne_zero
      (pow_ne_zero 2 hv), Nat.factorization_pow]
    change (u.factorization p + 2 * v.factorization p) / 2 = v.factorization p
    have := hu.natFactorization_le_one p
    omega
  have hV : squareSplitV (u * v ^ 2) = v := by
    simpa [Nat.floorRoot, hn, squareSplitV] using hroot
  have h := squareSplitU_mul_squareSplitV_sq hn
  rw [hV] at h
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero 2 hv)) h, hV⟩

private noncomputable def jordan : ArithmeticFunction ℤ :=
  (ArithmeticFunction.pow 2 : ArithmeticFunction ℤ) * ArithmeticFunction.moebius

private lemma jordan_sum (n : ℕ) : ∑ d ∈ n.divisors, jordan d = (n : ℤ) ^ 2 := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  rw [jordan, ← mul_assoc, mul_comm (ArithmeticFunction.zeta : ArithmeticFunction ℤ),
    mul_assoc, ArithmeticFunction.coe_zeta_mul_moebius, mul_one]
  simp

private noncomputable def candidate : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (Nat.totient (squareSplitU n) : ℤ) *
    jordan (squareSplitV n), by simp⟩

private lemma candidate_sum (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ squareSplitDivisors n, candidate d = (n : ℤ) := by
  obtain ⟨v, u, h, hu⟩ := exists_sq_mul_squarefree n
  have huv : u * v ^ 2 = n := by simpa [mul_comm] using h
  have hv : v ≠ 0 := by intro hv; simp [hv] at huv; exact hn huv.symm
  obtain ⟨hU, hV⟩ := split_coords hu hv
  rw [← huv, squareSplitDivisors, hU, hV]
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2 ^ 2) ↑(u.divisors ×ˢ v.divisors) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    have h₁ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
      (Nat.pos_of_mem_divisors hb).ne'
    have h₂ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors hc))
      (Nat.pos_of_mem_divisors hd).ne'
    change a * b ^ 2 = c * d ^ 2 at he
    rw [he] at h₁
    exact Prod.ext (h₁.1.symm.trans h₂.1) (h₁.2.symm.trans h₂.2)
  rw [Finset.sum_image hinj, Finset.sum_product]
  have he (a : ℕ) (ha : a ∈ u.divisors) (b : ℕ) (hb : b ∈ v.divisors) :
      candidate (a * b ^ 2) = (a.totient : ℤ) * jordan b := by
    obtain ⟨hUa, hVb⟩ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
      (Nat.pos_of_mem_divisors hb).ne'
    simp [candidate, hUa, hVb, mul_ne_zero (Nat.pos_of_mem_divisors ha).ne'
      (pow_ne_zero 2 (Nat.pos_of_mem_divisors hb).ne')]
  simp_rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => he a ha b hb))]
  simp_rw [← Finset.mul_sum, jordan_sum, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_totient]
  simp

private lemma determined_by_sum (φ ψ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n)
    (hψ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, ψ d = n) : φ = ψ := by
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    obtain ⟨_, hmem, hdvd⟩ := squareSplitDivisors_properties.1 n hn
    have he : ∑ d ∈ (squareSplitDivisors n).erase n, φ d =
        ∑ d ∈ (squareSplitDivisors n).erase n, ψ d := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hdn, hd⟩ := Finset.mem_erase.mp hd
      exact ih d (lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hdvd d hd)) hdn)
    have h₁ := hφ n hn
    have h₂ := hψ n hn
    rw [← Finset.sum_erase_add _ _ hmem] at h₁ h₂
    omega


private lemma jordan_multiplicative : jordan.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_pow.natCast.mul
    ArithmeticFunction.isMultiplicative_moebius

private lemma candidate_multiplicative : candidate.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [candidate, squareSplitU_one, squareSplitV_one, jordan]
  intro m n hm hn h
  have hprod (F : ℕ → ℕ → ℕ) :
      (m * n).factorization.prod F = m.factorization.prod F * n.factorization.prod F := by
    rw [Nat.factorization_mul_of_coprime h]
    exact Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors F
  have hu : squareSplitU (m * n) = squareSplitU m * squareSplitU n := hprod _
  have hv : squareSplitV (m * n) = squareSplitV m * squareSplitV n := hprod _
  have hUm : squareSplitU m ∣ m := by
    conv_rhs => rw [← squareSplitU_mul_squareSplitV_sq hm]
    exact Nat.dvd_mul_right _ _
  have hUn : squareSplitU n ∣ n := by
    conv_rhs => rw [← squareSplitU_mul_squareSplitV_sq hn]
    exact Nat.dvd_mul_right _ _
  have hVm : squareSplitV m ∣ m := by
    conv_rhs => rw [← squareSplitU_mul_squareSplitV_sq hm]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _
  have hVn : squareSplitV n ∣ n := by
    conv_rhs => rw [← squareSplitU_mul_squareSplitV_sq hn]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _
  simp only [candidate, ArithmeticFunction.coe_mk, ite_eq_right hm, ite_eq_right hn,
    ite_eq_right (mul_ne_zero hm hn), hu, hv, Nat.totient_mul (h.of_dvd hUm hUn), Nat.cast_mul,
    jordan_multiplicative.map_mul_of_coprime (h.of_dvd hVm hVn)]
  ring

private lemma split_prime_pow (p k : ℕ) (hp : p.Prime) :
    squareSplitU (p ^ k) = p ^ (k % 2) ∧ squareSplitV (p ^ k) = p ^ (k / 2) := by
  constructor <;> simp [squareSplitU, squareSplitV, hp.factorization_pow]

private lemma jordan_prime_pow_succ (p b : ℕ) (hp : p.Prime) :
    jordan (p ^ (b + 1)) = (p : ℤ) ^ (2 * b) * ((p : ℤ) ^ 2 - 1) := by
  have h₀ := jordan_sum (p ^ b)
  have h₁ := jordan_sum (p ^ (b + 1))
  rw [Nat.sum_divisors_prime_pow hp] at h₀
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, h₀] at h₁
  have he : (p : ℤ) ^ (2 * b) * ((p : ℤ) ^ 2 - 1) =
      ((p : ℤ) ^ (b + 1)) ^ 2 - ((p : ℤ) ^ b) ^ 2 := by
    rw [pow_succ (p : ℤ) b, mul_pow]
    simp only [pow_mul, mul_comm 2 b]
    ring
  rw [he]
  simp only [Nat.cast_pow] at h₁
  omega

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

private noncomputable def correction : ArithmeticFunction ℤ := candidate * inverseId

private lemma correction_multiplicative : correction.IsMultiplicative :=
  candidate_multiplicative.mul inverseId_multiplicative

private lemma candidate_eq_id_mul_correction :
    candidate = (ArithmeticFunction.id : ArithmeticFunction ℤ) * correction := by
  rw [correction, mul_left_comm, mul_comm (ArithmeticFunction.id : ArithmeticFunction ℤ),
    inverseId_mul_id, mul_one]


private lemma candidate_even (p b : ℕ) (hp : p.Prime) :
    candidate (p ^ (2 * b)) = jordan (p ^ b) := by
  obtain ⟨hu, hv⟩ := split_prime_pow p (2 * b) hp
  have hu' : 2 * b % 2 = 0 := by omega
  have hv' : 2 * b / 2 = b := by omega
  simp [candidate, hp.ne_zero, hu, hv, hu', hv']

private lemma candidate_odd (p b : ℕ) (hp : p.Prime) :
    candidate (p ^ (2 * b + 1)) = ((p : ℤ) - 1) * jordan (p ^ b) := by
  obtain ⟨hu, hv⟩ := split_prime_pow p (2 * b + 1) hp
  have hu' : (2 * b + 1) % 2 = 1 := by omega
  have hv' : (2 * b + 1) / 2 = b := by omega
  simp [candidate, hp.ne_zero, hu, hv, hu', hv', Nat.totient_prime hp,
    Nat.cast_sub hp.one_le]

private lemma candidate_prime_pow_step (p k : ℕ) (hp : p.Prime) :
    candidate (p ^ (k + 4)) = (p : ℤ) ^ 2 * candidate (p ^ (k + 2)) := by
  have hj (b : ℕ) : jordan (p ^ (b + 2)) = (p : ℤ) ^ 2 * jordan (p ^ (b + 1)) := by
    rw [show b + 2 = (b + 1) + 1 by omega, jordan_prime_pow_succ p (b + 1) hp,
      jordan_prime_pow_succ p b hp, show 2 * (b + 1) = 2 + 2 * b by omega, pow_add]
    ring
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨b, rfl⟩ := hk
    rw [show b + b + 4 = 2 * (b + 2) by omega,
      show b + b + 2 = 2 * (b + 1) by omega,
      candidate_even p (b + 2) hp, candidate_even p (b + 1) hp, hj b]
  · obtain ⟨b, rfl⟩ := hk
    rw [show 2 * b + 1 + 4 = 2 * (b + 2) + 1 by omega,
      show 2 * b + 1 + 2 = 2 * (b + 1) + 1 by omega,
      candidate_odd p (b + 2) hp, candidate_odd p (b + 1) hp, hj b]
    ring

private lemma correction_prime_pow_succ (p k : ℕ) (hp : p.Prime) :
    correction (p ^ (k + 1)) = candidate (p ^ (k + 1)) - (p : ℤ) * candidate (p ^ k) := by
  rw [correction, mul_comm candidate inverseId, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => inverseId a * candidate b),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz (i : ℕ) : inverseId (p ^ (i + 2)) = 0 := by
    simp [inverseId, ArithmeticFunction.moebius_apply_prime_pow hp (by omega : i + 2 ≠ 0)]
  have ht : ∑ i ∈ Finset.range k,
      inverseId (p ^ (i + 1 + 1)) * candidate (p ^ (k + 1) / p ^ (i + 1 + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show i + 1 + 1 = i + 2 by omega, hz, zero_mul]
  have hdiv : p ^ (k + 1) / p = p ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [ht]
  simp [inverseId, ArithmeticFunction.moebius_apply_prime hp, hdiv, sub_eq_add_neg, add_comm]


private lemma correction_prime_pow_tail (p k : ℕ) (hp : p.Prime) :
    correction (p ^ (k + 3)) = (-(p : ℤ)) ^ k * (1 - (p : ℤ) ^ 2) := by
  induction k with
  | zero =>
    rw [show 0 + 3 = 2 + 1 by rfl, correction_prime_pow_succ p 2 hp]
    change candidate (p ^ 3) - (p : ℤ) * candidate (p ^ 2) =
      (-(p : ℤ)) ^ 0 * (1 - (p : ℤ) ^ 2)
    have he₃ : 3 = 2 * 1 + 1 := rfl
    have he₂ : 2 = 2 * 1 := rfl
    rw [he₃, he₂, candidate_odd p 1 hp, candidate_even p 1 hp,
      show 1 = 0 + 1 by rfl, jordan_prime_pow_succ p 0 hp]
    ring
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by omega, correction_prime_pow_succ p (k + 3) hp,
      show k + 3 + 1 = k + 4 by omega, candidate_prime_pow_step p k hp,
      show k + 3 = (k + 2) + 1 by omega]
    have hh := correction_prime_pow_succ p (k + 2) hp
    rw [show k + 2 + 1 = k + 3 by omega, ih] at hh
    rw [pow_succ (-(p : ℤ)) k]
    change (p : ℤ) ^ 2 * candidate (p ^ (k + 2)) - (p : ℤ) *
      candidate (p ^ (k + 3)) = (-(p : ℤ)) ^ k * -(p : ℤ) * (1 - (p : ℤ) ^ 2)
    linear_combination (p : ℤ) * hh

private lemma correction_prime_pow_bound (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    |(correction (p ^ k) : ℝ)| ≤ (p : ℝ) ^ (k - 1) := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp₀ : (0 : ℝ) ≤ p := by positivity
  rcases k with _ | _ | _ | k
  · exact (hk rfl).elim
  · change |(correction (p ^ 1) : ℝ)| ≤ (p : ℝ) ^ 0
    rw [show 1 = 0 + 1 by rfl, correction_prime_pow_succ p 0 hp]
    have he₁ : 1 = 2 * 0 + 1 := rfl
    rw [he₁, candidate_odd p 0 hp]
    simp [candidate, squareSplitU_one, squareSplitV_one, jordan]
  · change |(correction (p ^ 2) : ℝ)| ≤ (p : ℝ) ^ 1
    rw [show 2 = 1 + 1 by rfl, correction_prime_pow_succ p 1 hp]
    change |((candidate (p ^ 2) - (p : ℤ) * candidate (p ^ 1) : ℤ) : ℝ)| ≤ (p : ℝ) ^ 1
    have he₂ : 2 = 2 * 1 := rfl
    have he₁ : 1 = 2 * 0 + 1 := rfl
    rw [he₂, candidate_even p 1 hp, show 1 = 0 + 1 by rfl,
      jordan_prime_pow_succ p 0 hp, he₁, candidate_odd p 0 hp]
    simp only [Nat.pow_zero]
    have hj : jordan 1 = 1 := jordan_multiplicative.1
    rw [hj]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_one]
    norm_num only [Nat.mul_zero, Nat.zero_add, pow_zero, one_mul, mul_one, pow_one]
    have he : (p : ℝ) ^ 2 - 1 - (p : ℝ) * ((p : ℝ) - 1) = p - 1 := by ring
    rw [he, abs_of_nonneg (by linarith)]
    linarith
  · rw [correction_prime_pow_tail p k hp]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast, Int.cast_sub,
      Int.cast_one, abs_mul, abs_pow, abs_neg, abs_of_nonneg hp₀,
      show k + 3 - 1 = k + 2 by omega, pow_add]
    have hsq : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
    rw [abs_sub_comm, abs_of_nonneg hsq]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)


private lemma correction_weighted_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => |(correction n : ℝ)| / (n : ℝ) ^ s) := by
  let f (n : ℕ) : ℝ := |(correction n : ℝ)| / (n : ℝ) ^ s
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
    rw [correction_multiplicative.map_mul_of_coprime h, Int.cast_mul, abs_mul,
      Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
    exact mul_div_mul_comm _ _ _ _
  have hone : f 1 = 1 := by simp [f, correction_multiplicative.1]
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
        exact div_le_div_of_nonneg_right (correction_prime_pow_bound p k hp hk) (by positivity)
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


private lemma correction_prime (p : ℕ) (hp : p.Prime) : correction p = -1 := by
  have h := correction_prime_pow_succ p 0 hp
  rw [show 0 + 1 = 2 * 0 + 1 by rfl, candidate_odd p 0 hp] at h
  simpa [candidate, squareSplitU_one, squareSplitV_one, jordan] using h

private lemma correction_square (p : ℕ) (hp : p.Prime) :
    correction (p ^ 2) = (p : ℤ) - 1 := by
  have h := correction_prime_pow_succ p 1 hp
  norm_num only [Nat.reduceAdd] at h
  have hc₂ : candidate (p ^ 2) = (p : ℤ) ^ 2 - 1 := by
    simpa using (candidate_even p 1 hp).trans (jordan_prime_pow_succ p 0 hp)
  have hc₁ : candidate p = (p : ℤ) - 1 := by
    simpa [candidate, squareSplitU_one, squareSplitV_one, jordan] using candidate_odd p 0 hp
  rw [pow_one, hc₂, hc₁] at h
  linarith

private lemma correction_euler_product :
    (∑' n : ℕ, (correction n : ℝ) / (n : ℝ) ^ 2) =
      ∏' p : Nat.Primes,
        (1 - 1 / ((p : ℕ) : ℝ) ^ 2 + (((p : ℕ) : ℝ) - 1) ^ 2 /
          ((p : ℕ) : ℝ) ^ 5) := by
  let f (n : ℕ) : ℝ := (correction n : ℝ) / (n : ℝ) ^ 2
  have hnorm : Summable (fun n => ‖f n‖) := by
    simpa only [f, norm_div, norm_pow, Real.norm_natCast, Real.norm_eq_abs, Nat.abs_cast,
      Real.rpow_two] using correction_weighted_summable 2 (by norm_num)
  have hone : f 1 = 1 := by simp [f, correction_multiplicative.1]
  have hzero : f 0 = 0 := by simp [f]
  have hmul {m n : ℕ} (h : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, correction_multiplicative.map_mul_of_coprime h, Int.cast_mul,
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
    rw [correction_prime_pow_tail _ k hp]
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
    correction_multiplicative.1, correction_prime _ hp, correction_square _ hp,
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

private lemma candidate_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (candidate n : ℝ)) =
      ∑ d ∈ Finset.Ioc 0 N, (correction d : ℝ) *
        ((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1) / 2 := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum correction
    (ArithmeticFunction.id : ArithmeticFunction ℤ) N
  rw [mul_comm correction, ← candidate_eq_id_mul_correction] at h
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

private lemma floor_div (x : ℝ) (d : ℕ) (hd : d ≠ 0) :
    ⌊x⌋₊ / d = ⌊x / (d : ℝ)⌋₊ := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  simpa only [div_mul_cancel₀ x hd'] using
    Nat.mul_cast_floor_div_cancel hd (x / (d : ℝ))


private lemma candidate_sum_bound (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (candidate n : ℝ)) -
      (∑' n : ℕ, (correction n : ℝ) / (n : ℝ) ^ 2) / 2 * x ^ 2)
      =O[Filter.atTop] fun x => x ^ (1 + ε) := by
  let a (n : ℕ) : ℝ := |(correction n : ℝ)| / (n : ℝ) ^ (1 + ε)
  let w (n : ℕ) : ℝ := (correction n : ℝ) / (n : ℝ) ^ 2
  let C : ℝ := ∑' n, a n
  have ha : Summable a := correction_weighted_summable (1 + ε) (by linarith)
  have ha₀ (n : ℕ) : 0 ≤ a n := by dsimp [a]; positivity
  have hC : 0 ≤ C := tsum_nonneg ha₀
  have hw : Summable (fun n => ‖w n‖) := by
    simpa only [w, norm_div, norm_pow, Real.norm_natCast, Real.norm_eq_abs, Nat.abs_cast,
      Real.rpow_two] using correction_weighted_summable 2 (by norm_num)
  apply Asymptotics.IsBigO.of_bound (3 * C)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  have hx₀ : 0 < x := by linarith
  let S := Finset.Ioc 0 ⌊x⌋₊
  let q (d : ℕ) : ℝ := ((⌊x⌋₊ / d : ℕ) : ℝ)
  let e (d : ℕ) : ℝ := (correction d : ℝ) *
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
      rw [floor_div x d hd₀.ne']
    have hpow : (d : ℝ) ^ ε ≤ x ^ ε := Real.rpow_le_rpow hd'.le hdx hε.le
    have he : |(correction d : ℝ)| * (2 * (x / (d : ℝ))) =
        2 * x * (d : ℝ) ^ ε * a d := by
      dsimp [a]
      rw [Real.rpow_add hd', Real.rpow_one]
      field_simp
    calc
      ‖e d‖ = |(correction d : ℝ)| *
          |q d * (q d + 1) / 2 - (x / (d : ℝ)) ^ 2 / 2| := by
        dsimp only [e]
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |(correction d : ℝ)| * (2 * (x / (d : ℝ))) :=
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
      change |(correction d : ℝ) / ((d : ℕ) : ℝ) ^ 2| = _
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
  have hsplit : (∑ n ∈ S, (candidate n : ℝ)) - (∑' n, w n) / 2 * x ^ 2 =
      (∑ d ∈ S, e d) - x ^ 2 / 2 * ∑' d : {d : ℕ // d ∉ S}, w d := by
    rw [hw.of_norm.sum_add_tsum_subtype_compl S |>.symm]
    dsimp [S]
    rw [candidate_partial_sum]
    dsimp [e, q, w]
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← mul_assoc]
    have heq : ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, (correction d : ℝ) * (x / (d : ℝ)) ^ 2 / 2 =
        (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, (correction d : ℝ) / (d : ℝ) ^ 2) * x ^ 2 / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d _
      rw [div_pow]
      ring
    rw [heq]
    ring
  change ‖(∑ n ∈ S, (candidate n : ℝ)) - (∑' n, w n) / 2 * x ^ 2‖ ≤
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
  have hfun : φ = candidate := determined_by_sum φ candidate hφ candidate_sum
  have h := candidate_sum_bound ε hε (by linarith)
  have hsets (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simpa only [hfun, hsets, correction_euler_product] using h


end MetaMathlibExt
