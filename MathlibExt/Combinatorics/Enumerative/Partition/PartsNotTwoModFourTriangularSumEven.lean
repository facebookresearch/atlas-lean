/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Instances.ZMod
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Parity of a triangular sum of partitions with no part congruent to 2 modulo 4

The generating function of the counts $P_2(m)$ times the triangular series
$\sum_{k \ge 0} q^{k(k+1)/2}$ is $1$ modulo $2$: the triangular series is the
Jacobi triple product at $z = q$ with nome $q^2$, and the resulting Euler
products cancel modulo $2$. The main result is
`MetaMathlibExt.partsNotTwoModFour_triangular_sum_even`.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

/-- **Partitions with no part congruent to 2 modulo 4.** For a natural number $n$, $P_2(n)$ is
the number of partitions of $n$ none of whose parts is congruent to $2$ modulo $4$.

Its generating function is $\sum_{n \ge 0} P_2(n) q^n = (q^2; q^4)_\infty / (q; q)_\infty$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `P_2(n)` before Theorem 11). -/
@[expose] public def partsNotTwoModFourCount (n : ℕ) : ℕ :=
  (Nat.Partition.restricted n fun i => i % 4 ≠ 2).card

namespace partsNotTwoModFour_triangular_sum_even

open Analysis.SpecialFunctions.JacobiTripleProduct

/-- The triangular series, as an integer power series: the coefficient of $q^n$ is $1$
if $n$ is triangular and $0$ otherwise. -/
private noncomputable def triangularSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n ∈ (Finset.range (n + 1)).image (fun k => k * (k + 1) / 2) then 1 else 0

private theorem coeff_triangularSeries (n : ℕ) :
    triangularSeries.coeff n =
      if n ∈ (Finset.range (n + 1)).image (fun k => k * (k + 1) / 2) then 1 else 0 :=
  PowerSeries.coeff_mk _ _

/-- The exponent $2m^2 + m$ is always nonnegative, as an integer. -/
private theorem two_mul_sq_add_nonneg (m : ℤ) : 0 ≤ 2 * m * m + m := by
  by_cases hm : 0 ≤ m
  · nlinarith [mul_nonneg hm hm]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -m by omega)
      (show (0 : ℤ) ≤ -(2 * m + 1) by omega)]

/-- A triangular number is at least its index. -/
private theorem le_triangular (k : ℕ) : k ≤ k * (k + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact Nat.mul_le_mul_left k (show 2 ≤ k + 1 by omega)

/-- Triangular numbers are distinct. -/
private theorem triangular_injective :
    Function.Injective (fun k : ℕ => k * (k + 1) / 2) := by
  intro a b hab
  dsimp only at hab
  have ha := Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one a)
  have hb := Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one b)
  have h2 : a * (a + 1) = b * (b + 1) := by omega
  have hmono : StrictMono (fun k : ℕ => k * (k + 1)) := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 : k * (k + 1) < (k + 1) * (k + 1) :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self k) (Nat.succ_pos k)
    have h2' : (k + 1) * (k + 1) ≤ (k + 1) * (k + 2) :=
      Nat.mul_le_mul_left _ (Nat.le_succ _)
    exact lt_of_lt_of_le h1 h2'
  exact hmono.injective h2

/-- The exponent $2m^2+m$ is triangular: it is $T_{2m}$ for $m \ge 0$ and $T_{-2m-1}$
for $m < 0$. -/
private theorem triangular_of_two_mul_sq_add (m : ℤ) :
    (2 * m * m + m).toNat ∈
      (Finset.range ((2 * m * m + m).toNat + 1)).image (fun k => k * (k + 1) / 2) := by
  have hcast : ((2 * m * m + m).toNat : ℤ) = 2 * m * m + m :=
    Int.toNat_of_nonneg (two_mul_sq_add_nonneg m)
  by_cases hm : 0 ≤ m
  · have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
    have hval : (2 * m.toNat) * (2 * m.toNat + 1) / 2 = (2 * m * m + m).toNat := by
      apply Nat.cast_injective (R := ℤ)
      rw [hcast]
      have hdvd : 2 ∣ (2 * m.toNat) * (2 * m.toNat + 1) := Nat.two_dvd_mul_add_one _
      have h2 : 2 * ((2 * m.toNat) * (2 * m.toNat + 1) / 2)
          = (2 * m.toNat) * (2 * m.toNat + 1) := Nat.mul_div_cancel' hdvd
      have hprod : ((2 * m.toNat) * (2 * m.toNat + 1) : ℤ) = 2 * (2 * m * m + m) := by
        push_cast [hmn]; ring
      have h2z : (2 : ℤ) * (((2 * m.toNat) * (2 * m.toNat + 1) / 2 : ℕ) : ℤ)
          = ((2 * m.toNat) * (2 * m.toNat + 1) : ℤ) := by exact_mod_cast h2
      omega
    refine Finset.mem_image.mpr ⟨2 * m.toNat, Finset.mem_range.mpr ?_, hval⟩
    have hle := le_triangular (2 * m.toNat)
    omega
  · have hmn : ((-2 * m - 1).toNat : ℤ) = -2 * m - 1 := Int.toNat_of_nonneg (by omega)
    have hval : (-2 * m - 1).toNat * ((-2 * m - 1).toNat + 1) / 2
        = (2 * m * m + m).toNat := by
      apply Nat.cast_injective (R := ℤ)
      rw [hcast]
      have hdvd : 2 ∣ (-2 * m - 1).toNat * ((-2 * m - 1).toNat + 1) :=
        Nat.two_dvd_mul_add_one _
      have h2 : 2 * ((-2 * m - 1).toNat * ((-2 * m - 1).toNat + 1) / 2)
          = (-2 * m - 1).toNat * ((-2 * m - 1).toNat + 1) := Nat.mul_div_cancel' hdvd
      have hprod : (((-2 * m - 1).toNat * ((-2 * m - 1).toNat + 1) : ℕ) : ℤ)
          = 2 * (2 * m * m + m) := by
        push_cast [hmn]; ring
      have h2z : (2 : ℤ) * (((-2 * m - 1).toNat * ((-2 * m - 1).toNat + 1) / 2 : ℕ) : ℤ)
          = (((-2 * m - 1).toNat * ((-2 * m - 1).toNat + 1) : ℕ) : ℤ) := by
        exact_mod_cast h2
      omega
    refine Finset.mem_image.mpr ⟨(-2 * m - 1).toNat, Finset.mem_range.mpr ?_, hval⟩
    have hle := le_triangular (-2 * m - 1).toNat
    omega

/-- Every triangular number is $2m^2+m$ for some integer $m$. -/
private theorem exists_two_mul_sq_add_of_mem_image {n : ℕ}
    (hn : n ∈ (Finset.range (n + 1)).image (fun k => k * (k + 1) / 2)) :
    ∃ m : ℤ, (2 * m * m + m).toNat = n := by
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hn
  by_cases hpar : Even k
  · obtain ⟨t, ht⟩ := hpar
    refine ⟨t, ?_⟩
    have hcast : ((2 * (t : ℤ) * t + t).toNat : ℤ) = 2 * (t : ℤ) * t + t :=
      Int.toNat_of_nonneg (two_mul_sq_add_nonneg t)
    apply Nat.cast_injective (R := ℤ)
    rw [hcast, ← hk]
    have hprod : ((k * (k + 1) : ℕ) : ℤ) = 2 * (2 * (t : ℤ) * t + t) := by
      rw [ht]; push_cast; ring
    have hdvd : 2 ∣ k * (k + 1) := Nat.two_dvd_mul_add_one k
    have h2 : 2 * (k * (k + 1) / 2) = k * (k + 1) := Nat.mul_div_cancel' hdvd
    have h2z : (2 : ℤ) * ((k * (k + 1) / 2 : ℕ) : ℤ) = ((k * (k + 1) : ℕ) : ℤ) := by
      exact_mod_cast h2
    omega
  · have hodd : Odd k := Nat.not_even_iff_odd.mp hpar
    obtain ⟨t, ht⟩ := hodd
    refine ⟨-(t : ℤ) - 1, ?_⟩
    have hcast : ((2 * (-(t : ℤ) - 1) * (-(t : ℤ) - 1) + (-(t : ℤ) - 1)).toNat : ℤ)
        = 2 * (-(t : ℤ) - 1) * (-(t : ℤ) - 1) + (-(t : ℤ) - 1) :=
      Int.toNat_of_nonneg (two_mul_sq_add_nonneg _)
    apply Nat.cast_injective (R := ℤ)
    rw [hcast, ← hk]
    have hprod : ((k * (k + 1) : ℕ) : ℤ)
        = 2 * (2 * (-(t : ℤ) - 1) * (-(t : ℤ) - 1) + (-(t : ℤ) - 1)) := by
      rw [ht]; push_cast; ring
    have hdvd : 2 ∣ k * (k + 1) := Nat.two_dvd_mul_add_one k
    have h2 : 2 * (k * (k + 1) / 2) = k * (k + 1) := Nat.mul_div_cancel' hdvd
    have h2z : (2 : ℤ) * ((k * (k + 1) / 2 : ℕ) : ℤ) = ((k * (k + 1) : ℕ) : ℤ) := by
      exact_mod_cast h2
    omega

private theorem coeff_triangularSeries_of_two_mul_sq_add (m : ℤ) :
    triangularSeries.coeff (2 * m * m + m).toNat = 1 := by
  rw [coeff_triangularSeries]
  split_ifs with h
  · rfl
  · exact absurd (triangular_of_two_mul_sq_add m) h

private theorem coeff_triangularSeries_eq_zero_of_not_range {n : ℕ}
    (hn : ∀ m : ℤ, (2 * m * m + m).toNat ≠ n) :
    triangularSeries.coeff n = 0 := by
  rw [coeff_triangularSeries]
  split_ifs with h
  · obtain ⟨m, hm⟩ := exists_two_mul_sq_add_of_mem_image h
    exact absurd hm (hn m)
  · rfl

/-! ### Euler-function products -/

private lemma norm_pow_lt {q : ℂ} (h : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) h hk

private lemma euler_ne {q : ℂ} (h : ‖q‖ < 1) : eulerFunction q ≠ 0 := by
  rw [eulerFunction_eq_tprod h]
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n he
    have he' : q ^ (n + 1) = 1 := by linear_combination -he
    have := pow_lt_one₀ (norm_nonneg q) h (Nat.succ_ne_zero n)
    rwa [← norm_pow, he', norm_one, lt_self_iff_false] at this
  · simpa [pow_succ, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) h).mul_right ‖q‖

private lemma summable_norm_pow_lin {q : ℂ} (h : ‖q‖ < 1) (a b : ℕ) (ha : a ≠ 0) :
    Summable (fun n : ℕ => ‖q ^ (a * n + b)‖) := by
  have hg := summable_geometric_of_lt_one (norm_nonneg _) (norm_pow_lt h ha)
  refine (hg.mul_right (‖q‖ ^ b)).congr fun n => ?_
  rw [norm_pow, norm_pow, ← pow_mul, ← pow_add]

private lemma multipliable_one_add_pow_lin {q : ℂ} (h : ‖q‖ < 1) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (a b : ℕ) (ha : a ≠ 0) :
    Multipliable (fun n : ℕ => 1 + c * q ^ (a * n + b)) := by
  apply multipliable_one_add_of_summable
  refine (summable_norm_pow_lin h a b ha).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

/-- `∏ (1 - q^{2n+1}) = f(q) / f(q²)`. -/
private lemma odd_minus_prod {q : ℂ} (h : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 - q ^ (2 * n + 1)) (eulerFunction q / eulerFunction (q ^ 2)) := by
  have hm : Multipliable (fun n : ℕ => 1 - q ^ (2 * n + 1)) := by
    simpa [sub_eq_add_neg] using multipliable_one_add_pow_lin h (-1) (by simp) 2 1 two_ne_zero
  have hodd : HasProd (fun k : ℕ => (fun n : ℕ => 1 - q ^ (n + 1)) (2 * k + 1))
      (eulerFunction (q ^ 2)) := by
    refine (hasProd_eulerFunction (norm_pow_lt h two_ne_zero)).congr_fun fun k => ?_
    simp only [← pow_mul]
    ring_nf
  have hall := HasProd.even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1)) hm.hasProd hodd
  have huniq := hall.unique (hasProd_eulerFunction h)
  have hval : eulerFunction q / eulerFunction (q ^ 2) = ∏' n : ℕ, (1 - q ^ (2 * n + 1)) := by
    rw [← huniq, mul_div_assoc, div_self (euler_ne (norm_pow_lt h two_ne_zero)), mul_one]
  rw [hval]
  exact hm.hasProd

/-- `∏ (1 + q^{2n+1}) = f(q²)² / (f(q) f(q⁴))`. -/
private lemma odd_plus_prod {q : ℂ} (h : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 + q ^ (2 * n + 1))
      (eulerFunction (q ^ 2) ^ 2 / (eulerFunction q * eulerFunction (q ^ 4))) := by
  have hm : Multipliable (fun n : ℕ => 1 + q ^ (2 * n + 1)) := by
    simpa using multipliable_one_add_pow_lin h 1 (by simp) 2 1 two_ne_zero
  have hprod := hm.hasProd.mul (odd_minus_prod h)
  have he := (odd_minus_prod (norm_pow_lt h two_ne_zero)).congr_fun
    (g := fun n : ℕ => (1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 1))) fun n => by ring
  have huniq := hprod.unique he
  rw [← pow_mul] at huniq
  have h1 := euler_ne h
  have h2 := euler_ne (norm_pow_lt h two_ne_zero)
  have h4 := euler_ne (norm_pow_lt h (by norm_num : (4 : ℕ) ≠ 0))
  have hval : ∏' n : ℕ, (1 + q ^ (2 * n + 1)) =
      eulerFunction (q ^ 2) ^ 2 / (eulerFunction q * eulerFunction (q ^ 4)) := by
    field_simp
    field_simp at huniq
    linear_combination huniq
  rw [← hval]
  exact hm.hasProd

/-! ### The Jacobi specialization -/

/-- The Jacobi triple product with $z = q$ and nome $q^2$: the triangular series is the
product $\prod_n (1 - q^{4n+4})(1 + q^{4n+3})(1 + q^{4n+1})$. -/
private lemma jacobi_triangular {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ (2 * m * m + m).toNat) =
      ∏' n : ℕ, (1 - q ^ (4 * n + 4)) * (1 + q ^ (4 * n + 3)) * (1 + q ^ (4 * n + 1)) := by
  have hnorm : ‖q ^ 2‖ < 1 := norm_pow_lt hq two_ne_zero
  obtain ⟨-, -, hJ⟩ := jacobi_triple_product q (q ^ 2) hq0 hnorm
  have hterm : ∀ m : ℤ, q ^ m * (q ^ 2) ^ ((m * m).toNat) = q ^ (2 * m * m + m).toNat := by
    intro m
    have hpow : (q ^ 2 : ℂ) ^ (m * m).toNat = q ^ (2 * (m * m).toNat) := by
      rw [← pow_mul]
    rw [hpow, ← zpow_natCast q (2 * (m * m).toNat),
      ← zpow_natCast q ((2 * m * m + m).toNat), ← zpow_add₀ hq0]
    congr 1
    rw [Int.toNat_of_nonneg (two_mul_sq_add_nonneg m)]
    push_cast
    rw [Int.toNat_of_nonneg (mul_self_nonneg m)]
    ring
  have hfactor : ∀ n : ℕ, (1 - (q ^ 2 : ℂ) ^ (2 * n + 2)) *
      (1 + q * (q ^ 2) ^ (2 * n + 1)) * (1 + q⁻¹ * (q ^ 2) ^ (2 * n + 1)) =
      (1 - q ^ (4 * n + 4)) * (1 + q ^ (4 * n + 3)) * (1 + q ^ (4 * n + 1)) := by
    intro n
    have e1 : (q ^ 2 : ℂ) ^ (2 * n + 2) = q ^ (4 * n + 4) := by
      rw [← pow_mul]
      congr 1
      ring
    have e2 : q * (q ^ 2 : ℂ) ^ (2 * n + 1) = q ^ (4 * n + 3) := by
      have h1 : (q ^ 2 : ℂ) ^ (2 * n + 1) = q ^ (4 * n + 2) := by
        rw [← pow_mul]
        congr 1
        ring
      rw [h1]
      conv_rhs => rw [show 4 * n + 3 = (4 * n + 2) + 1 by ring, pow_succ]
      exact mul_comm _ _
    have e3 : q⁻¹ * (q ^ 2 : ℂ) ^ (2 * n + 1) = q ^ (4 * n + 1) := by
      rw [← pow_mul, show 2 * (2 * n + 1) = (4 * n + 1) + 1 by ring, pow_succ']
      rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
    rw [e1, e2, e3]
  calc (∑' m : ℤ, q ^ (2 * m * m + m).toNat)
      = ∑' m : ℤ, q ^ m * (q ^ 2) ^ ((m * m).toNat) := tsum_congr fun m => (hterm m).symm
    _ = ∏' n : ℕ, (1 - (q ^ 2 : ℂ) ^ (2 * n + 2)) *
          (1 + q * (q ^ 2) ^ (2 * n + 1)) * (1 + q⁻¹ * (q ^ 2) ^ (2 * n + 1)) := hJ
    _ = ∏' n : ℕ, (1 - q ^ (4 * n + 4)) * (1 + q ^ (4 * n + 3)) *
          (1 + q ^ (4 * n + 1)) := tprod_congr hfactor

private lemma euler_four_hasProd {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 - q ^ (4 * n + 4)) (eulerFunction (q ^ 4)) := by
  refine (hasProd_eulerFunction (norm_pow_lt hq (by norm_num : (4 : ℕ) ≠ 0))).congr_fun
    fun n => ?_
  simp only [← pow_mul]
  congr 1

/-- Splitting $\prod_n (1 + q^{2n+1})$ into the subsequences $4n+1$ and $4n+3$. -/
private lemma odd_plus_split {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 + q ^ (2 * (2 * n) + 1))) *
      (∏' n : ℕ, (1 + q ^ (2 * (2 * n + 1) + 1))) =
      ∏' n : ℕ, (1 + q ^ (2 * n + 1)) := by
  have hOdd := odd_plus_prod hq
  set f : ℕ → ℂ := fun n => 1 + q ^ (2 * n + 1) with hf_def
  have hBmult : Multipliable (fun k => f (2 * k)) := by
    have heq : (fun k : ℕ => f (2 * k)) = (fun n : ℕ => 1 + q ^ (4 * n + 1)) :=
      funext fun n => by rw [hf_def]; ring
    rw [heq]
    simpa using multipliable_one_add_pow_lin hq 1 (by simp) 4 1
      (by norm_num : (4 : ℕ) ≠ 0)
  have hCmult : Multipliable (fun k => f (2 * k + 1)) := by
    have heq : (fun k : ℕ => f (2 * k + 1)) = (fun n : ℕ => 1 + q ^ (4 * n + 3)) :=
      funext fun n => by rw [hf_def]; ring
    rw [heq]
    simpa using multipliable_one_add_pow_lin hq 1 (by simp) 4 3
      (by norm_num : (4 : ℕ) ≠ 0)
  have hB : HasProd (fun k => f (2 * k)) (∏' k, f (2 * k)) := hBmult.hasProd
  have hC : HasProd (fun k => f (2 * k + 1)) (∏' k, f (2 * k + 1)) := hCmult.hasProd
  exact (HasProd.even_mul_odd hB hC).unique hOdd.multipliable.hasProd

/-- The triple product from the Jacobi specialization has value
$f(q^4) \cdot f(q^2)^2 / (f(q) f(q^4))$. -/
private lemma triple_product_hasProd {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd
      (fun n : ℕ => (1 - q ^ (4 * n + 4)) * (1 + q ^ (4 * n + 3)) * (1 + q ^ (4 * n + 1)))
      (eulerFunction (q ^ 4) *
        (eulerFunction (q ^ 2) ^ 2 / (eulerFunction q * eulerFunction (q ^ 4)))) := by
  have hA := euler_four_hasProd hq
  have hOdd := odd_plus_prod hq
  have hBmult : Multipliable (fun n : ℕ => 1 + q ^ (2 * (2 * n) + 1)) := by
    have heq : (fun n : ℕ => 1 + q ^ (2 * (2 * n) + 1)) =
        (fun n : ℕ => 1 + q ^ (4 * n + 1)) :=
      funext fun n => by rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring]
    rw [heq]
    simpa using multipliable_one_add_pow_lin hq 1 (by simp) 4 1
      (by norm_num : (4 : ℕ) ≠ 0)
  have hCmult : Multipliable (fun n : ℕ => 1 + q ^ (2 * (2 * n + 1) + 1)) := by
    have heq : (fun n : ℕ => 1 + q ^ (2 * (2 * n + 1) + 1)) =
        (fun n : ℕ => 1 + q ^ (4 * n + 3)) :=
      funext fun n => by rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by ring]
    rw [heq]
    simpa using multipliable_one_add_pow_lin hq 1 (by simp) 4 3
      (by norm_num : (4 : ℕ) ≠ 0)
  have hB : HasProd (fun n : ℕ => 1 + q ^ (2 * (2 * n) + 1))
      (∏' n : ℕ, (1 + q ^ (2 * (2 * n) + 1))) := hBmult.hasProd
  have hC : HasProd (fun n : ℕ => 1 + q ^ (2 * (2 * n + 1) + 1))
      (∏' n : ℕ, (1 + q ^ (2 * (2 * n + 1) + 1))) := hCmult.hasProd
  have hsplit := odd_plus_split hq
  have hval : eulerFunction (q ^ 4) *
      (∏' n : ℕ, (1 + q ^ (2 * (2 * n + 1) + 1))) *
      (∏' n : ℕ, (1 + q ^ (2 * (2 * n) + 1))) =
      eulerFunction (q ^ 4) *
        (eulerFunction (q ^ 2) ^ 2 / (eulerFunction q * eulerFunction (q ^ 4))) := by
    calc eulerFunction (q ^ 4) *
        (∏' n : ℕ, (1 + q ^ (2 * (2 * n + 1) + 1))) *
          (∏' n : ℕ, (1 + q ^ (2 * (2 * n) + 1)))
          = eulerFunction (q ^ 4) *
            ((∏' n : ℕ, (1 + q ^ (2 * (2 * n) + 1))) *
              (∏' n : ℕ, (1 + q ^ (2 * (2 * n + 1) + 1)))) := by ring
      _ = eulerFunction (q ^ 4) * (∏' n : ℕ, (1 + q ^ (2 * n + 1))) := by rw [hsplit]
      _ = eulerFunction (q ^ 4) *
          (eulerFunction (q ^ 2) ^ 2 / (eulerFunction q * eulerFunction (q ^ 4))) := by
        rw [hOdd.tprod_eq]
  have hprod := (hA.mul hC).mul hB
  rw [hval] at hprod
  refine hprod.congr_fun fun n => ?_
  rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by ring,
    show 2 * (2 * n) + 1 = 4 * n + 1 by ring]

/-- Multiplying the triangular series by the Euler function gives the square of the
Euler function at $q^2$. -/
private lemma analytic_euler_mul_triangular {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    eulerFunction q * (∑' m : ℤ, q ^ (2 * m * m + m).toNat) = eulerFunction (q ^ 2) ^ 2 := by
  rw [jacobi_triangular hq0 hq, (triple_product_hasProd hq).tprod_eq]
  have h1 := euler_ne hq
  have h4 := euler_ne (norm_pow_lt hq (by norm_num : (4 : ℕ) ≠ 0))
  field_simp

/-! ### Transfer to integer power series -/

section Transfer

open UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam 1

/-- A complex function represented by an integer power series on the punctured unit disk. -/
private def Represents (F : ℤ⟦X⟧) (f : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ ↦ (F.coeff n : ℂ) * 𝕢 τ ^ n) (f (𝕢 τ))

private lemma Represents.mul {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) :
    Represents (F * G) (fun q ↦ f q * g q) := by
  intro τ
  let ι := Int.castRingHom ℂ
  simpa [← map_mul, coeff_map, ι] using
    ModularCurve.hasSum_qParam_mul 1 one_pos (map ι F) (map ι G)
      (fun z ↦ f (𝕢 z)) (fun z ↦ g (𝕢 z))
      (by simpa [coeff_map, ι, Represents] using hf)
      (by simpa [coeff_map, ι, Represents] using hg) τ

private lemma represents_const (c : ℤ) : Represents (C c) (fun _ ↦ (c : ℂ)) := by
  intro τ
  refine (hasSum_ite_eq (0 : ℕ) (c : ℂ)).congr_fun fun n ↦ ?_
  rw [coeff_C]
  split_ifs with h <;> simp_all

private lemma Represents.pow {F : ℤ⟦X⟧} {f : ℂ → ℂ} (hf : Represents F f) (n : ℕ) :
    Represents (F ^ n) (fun q ↦ f q ^ n) := by
  induction n with
  | zero => simpa using represents_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private lemma qEulerProduct_eq_expand (k : ℕ) (hk : k ≠ 0) :
    qEulerProduct k = expand k hk (pentagonalSeries ℤ) := by
  have cont : Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
    · simp [coeff_expand, hd]
  have prod := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) cont
  simpa [qEulerProduct, Function.comp_def, pow_mul] using prod.tprod_eq

private lemma represents_euler (k : ℕ) (hk : k ≠ 0) :
    Represents (qEulerProduct k) (fun q ↦ eulerFunction (q ^ k)) := by
  rw [qEulerProduct_eq_expand k hk]
  intro τ
  have lt1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hk1 : ‖𝕢 τ ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) lt1 hk
  have inj : Function.Injective (k * ·) := mul_right_injective₀ hk
  apply (inj.hasSum_iff ?_).mp
  · refine (hasSum_eulerFunction_pentagonalSeries hk1).congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, coeff_expand_mul, pow_mul]
    congr 1
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨m, rfl⟩ := hn
      simp [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  · intro n hn
    have hd : ¬ k ∣ n := by simpa [dvd_def, eq_comm] using hn
    simp [coeff_expand_of_not_dvd _ _ _ hd]

private lemma Represents.eq_of_eval {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g)
    (heq : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → f q = g q) : F = G := by
  have hzero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
    simp [cuspFunction, Pi.zero_comp, Periodic.cuspFunction_zero]
  have han : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := hzero ▸ analyticAt_const
  let c (m : ℕ) : ℂ := (F.coeff m : ℂ) - G.coeff m
  have hh := hasFPowerSeriesOnBall_cuspFunction (c := c) one_pos han (fun τ ↦ by
    have he := heq _ (Periodic.qParam_ne_zero _) (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
    simpa [c, smul_eq_mul, sub_mul, he] using (hf τ).sub (hg τ))
  rw [hzero] at hh
  have hz := hh.hasFPowerSeriesAt.eq_zero_of_eventually (Filter.EventuallyEq.refl _ _)
  apply PowerSeries.ext
  intro n
  have hc := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp
    (congrFun hz n)
  simpa [c, sub_eq_zero] using hc

private lemma represents_triangular :
    Represents triangularSeries (fun q => ∑' m : ℤ, q ^ (2 * m * m + m).toNat) := by
  intro τ
  have hq1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hsumm : Summable (fun m : ℤ => (𝕢 τ : ℂ) ^ (2 * m * m + m).toNat) := by
    apply Summable.of_norm
    have hgeo : Summable (fun a : ℤ => ‖𝕢 τ‖ ^ a.natAbs) := by
      apply Summable.of_nat_of_neg
      · simpa using summable_geometric_of_lt_one (norm_nonneg _) hq1
      · simpa using summable_geometric_of_lt_one (norm_nonneg _) hq1
    refine hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) fun a => ?_
    rw [norm_pow]
    apply pow_le_pow_of_le_one (norm_nonneg _) hq1.le
    have hcast : ((2 * a * a + a).toNat : ℤ) = 2 * a * a + a :=
      Int.toNat_of_nonneg (two_mul_sq_add_nonneg a)
    have h1 : (a.natAbs : ℤ) ≤ 2 * a * a + a := by
      rw [Int.natCast_natAbs]
      by_cases ha : 0 ≤ a
      · rw [abs_of_nonneg ha]
        nlinarith [mul_nonneg ha ha]
      · rw [abs_of_neg (show a < 0 by omega)]
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ -a by omega)
          (show (0 : ℤ) ≤ -(2 * a + 1) by omega)]
    have hle : a.natAbs ≤ (2 * a * a + a).toNat := by
      rw [← hcast] at h1
      exact_mod_cast h1
    exact_mod_cast hle
  have hs : HasSum (fun m : ℤ => (𝕢 τ : ℂ) ^ (2 * m * m + m).toNat)
      (∑' m : ℤ, (𝕢 τ : ℂ) ^ (2 * m * m + m).toNat) := hsumm.hasSum
  have hw_inj : Function.Injective (fun m : ℤ => (2 * m * m + m).toNat) := by
    intro a b hab
    have hcast : ∀ m : ℤ, ((2 * m * m + m).toNat : ℤ) = 2 * m * m + m :=
      fun m => Int.toNat_of_nonneg (two_mul_sq_add_nonneg m)
    have h := congrArg (Nat.cast (R := ℤ)) hab
    rw [hcast, hcast] at h
    have hfac : (a - b) * (2 * a + 2 * b + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h2
    · omega
    · omega
  have hcomp : HasSum
      ((fun n : ℕ => (triangularSeries.coeff n : ℂ) * 𝕢 τ ^ n) ∘
        fun m : ℤ => (2 * m * m + m).toNat)
      (∑' m : ℤ, (𝕢 τ : ℂ) ^ (2 * m * m + m).toNat) := by
    refine hs.congr_fun fun m => ?_
    simp only [Function.comp_apply, coeff_triangularSeries_of_two_mul_sq_add]
    simp
  have hvan : ∀ n : ℕ, n ∉ Set.range (fun m : ℤ => (2 * m * m + m).toNat) →
      (triangularSeries.coeff n : ℂ) * 𝕢 τ ^ n = 0 := by
    intro n hn
    rw [coeff_triangularSeries_eq_zero_of_not_range (fun m hm => hn ⟨m, hm⟩)]
    simp
  exact (hw_inj.hasSum_iff hvan).mp hcomp

/-- The triangular series times the first Euler product is the square of the second
Euler product, as integer power series. -/
private theorem eulerProduct_mul_triangularSeries :
    qEulerProduct 1 * triangularSeries = qEulerProduct 2 ^ 2 := by
  have h1 := represents_euler 1 one_ne_zero
  simp only [pow_one] at h1
  have h2 := (represents_euler 2 two_ne_zero).pow 2
  exact (h1.mul represents_triangular).eq_of_eval h2 (fun q hq0 hq => by
    have h := analytic_euler_mul_triangular hq0 hq
    simpa [pow_one] using h)

end Transfer

/-! ### Reduction modulo two -/

private noncomputable abbrev pserZMod : (ZMod 2)⟦X⟧ :=
  PowerSeries.mk fun n => (partsNotTwoModFourCount n : ZMod 2)

private noncomputable abbrev triZMod : (ZMod 2)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 2)) triangularSeries

private theorem coeff_pserZMod (n : ℕ) :
    pserZMod.coeff n = (partsNotTwoModFourCount n : ZMod 2) :=
  PowerSeries.coeff_mk _ _

private theorem coeff_triZMod (m : ℕ) :
    triZMod.coeff m =
      if m ∈ (Finset.range (m + 1)).image (fun k => k * (k + 1) / 2) then 1 else 0 := by
  rw [triZMod, PowerSeries.coeff_map, coeff_triangularSeries]
  split_ifs <;> simp

private theorem map_pentagonalSeries_zmod2 :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (pentagonalSeries ℤ) =
      pentagonalSeries (ZMod 2) := by
  ext n
  rw [PowerSeries.coeff_map]
  by_cases hn : ∃ k, pentagonal k = n
  · obtain ⟨k, rfl⟩ := hn
    simp [coeff_pentagonalSeries_pentagonal, Int.castRingHom, Int.negOnePow]
  · rw [coeff_pentagonalSeries_eq_zero ℤ (by simpa using hn),
      coeff_pentagonalSeries_eq_zero (ZMod 2) (by simpa using hn), map_zero]

/-- In characteristic two, squaring a power series doubles every exponent. -/
private theorem sq_eq_expand_two (F : (ZMod 2)⟦X⟧) :
    F ^ 2 = expand 2 two_ne_zero F := by
  have h := PowerSeries.map_frobenius_expand (R := ZMod 2) (p := 2) (hp := two_ne_zero) (f := F)
  rw [← h]
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map]
  have hsq : ∀ a : ZMod 2, a ^ 2 = a := by decide
  change ((expand 2 two_ne_zero F).coeff n) ^ 2 = (expand 2 two_ne_zero F).coeff n
  exact hsq _

/-- The image of the second Euler product is the second expansion of the pentagonal
series modulo two. -/
private theorem map_qEulerProduct_two :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (qEulerProduct 2) =
      expand 2 two_ne_zero (pentagonalSeries (ZMod 2)) := by
  rw [qEulerProduct_eq_expand 2 two_ne_zero, PowerSeries.map_expand, map_pentagonalSeries_zmod2]

/-- In characteristic two, `1 - F = 1 + F` for a power series `F`. -/
private theorem one_sub_eq_one_add (F : (ZMod 2)⟦X⟧) : 1 - F = 1 + F := by
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_neg, PowerSeries.coeff_one, sub_eq_add_neg, CharTwo.neg_eq]

/-- The geometric series times `1 + X ^ k` is `1` in characteristic two. -/
private theorem geom_mul_one_add {k : ℕ} (hk : k ≠ 0) :
    (∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ (k * j)) * (1 + X ^ k) = 1 := by
  have hconst : PowerSeries.constantCoeff (X ^ k : (ZMod 2)⟦X⟧) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_X_pow]
    simp [hk, eq_comm]
  have hgeom := WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hconst
  have hsum : (∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ (k * j)) =
      ∑' j : ℕ, (X ^ k : (ZMod 2)⟦X⟧) ^ j := by
    apply tsum_congr
    intro j
    rw [← pow_mul]
  rw [hsum]
  rw [← one_sub_eq_one_add (X ^ k)]
  exact hgeom

/-- The product of the $P_2$ series with the square of the second Euler product is the
pentagonal series modulo two. -/
private theorem pserZMod_mul_sq_eq_pentagonal :
    pserZMod * (PowerSeries.map (Int.castRingHom (ZMod 2)) (qEulerProduct 2)) ^ 2 =
      pentagonalSeries (ZMod 2) := by
  have hsq : (PowerSeries.map (Int.castRingHom (ZMod 2)) (qEulerProduct 2)) ^ 2 =
      expand 4 (by norm_num : (4 : ℕ) ≠ 0) (pentagonalSeries (ZMod 2)) := by
    rw [map_qEulerProduct_two, sq_eq_expand_two]
    have hexp : expand 4 (by norm_num : (4 : ℕ) ≠ 0) (pentagonalSeries (ZMod 2)) =
        expand 2 two_ne_zero (expand 2 two_ne_zero (pentagonalSeries (ZMod 2))) :=
      congr($(expand_mul_eq_comp (p := 2) (hp := two_ne_zero) (q := 2)
        (hq := two_ne_zero)) (pentagonalSeries (ZMod 2)))
    exact hexp.symm
  have hPser : HasProd
      (fun i => if (i + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j)
        else 1) pserZMod :=
    Nat.Partition.hasProd_powerSeriesMk_card_restricted (ZMod 2) (fun i => i % 4 ≠ 2)
  have hpent : HasProd (fun i => (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1))
      (pentagonalSeries (ZMod 2)) := by
    refine (WithPiTopology.hasProd_one_sub_X_pow (ZMod 2)).congr_fun fun i => ?_
    exact (one_sub_eq_one_add _).symm
  have hexp : HasProd (fun i => (1 : (ZMod 2)⟦X⟧) + X ^ (4 * (i + 1)))
      (expand 4 (by norm_num : (4 : ℕ) ≠ 0) (pentagonalSeries (ZMod 2))) := by
    have cont : Continuous (expand 4 (by norm_num : (4 : ℕ) ≠ 0) :
        (ZMod 2)⟦X⟧ → (ZMod 2)⟦X⟧) := by
      rw [continuous_iff_continuousAt]
      intro F
      rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
      intro n
      by_cases hd : 4 ∣ n
      · simpa [coeff_expand, hd] using
          (WithPiTopology.continuous_coeff (ZMod 2) (n / 4)).tendsto F
      · simp [coeff_expand, hd]
    have hmap := hpent.map (expand 4 (by norm_num : (4 : ℕ) ≠ 0)) cont
    refine hmap.congr_fun fun i => ?_
    simp only [Function.comp_def, map_add, map_one, map_pow, PowerSeries.expand_X,
      ← pow_mul]
  have hsqprod : HasProd
      (fun i => if 4 ∣ (i + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1) else 1)
      (expand 4 (by norm_num : (4 : ℕ) ≠ 0) (pentagonalSeries (ZMod 2))) := by
    have hinj : Function.Injective (fun n : ℕ => 4 * n + 3) := fun a b h => by
      dsimp only at h; omega
    have hside : ∀ x : ℕ, x ∉ Set.range (fun n : ℕ => 4 * n + 3) →
        (if 4 ∣ (x + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (x + 1) else 1) = 1 := by
      intro x hx
      rw [ite_eq_right]
      intro hdvd
      obtain ⟨t, ht⟩ := hdvd
      apply hx
      refine ⟨t - 1, ?_⟩
      dsimp only
      omega
    have hcomp0 : HasProd (fun n : ℕ =>
        (if 4 ∣ ((4 * n + 3) + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ ((4 * n + 3) + 1)
          else 1)) (expand 4 (by norm_num : (4 : ℕ) ≠ 0) (pentagonalSeries (ZMod 2))) := by
      refine hexp.congr_fun fun n => ?_
      have h4 : 4 ∣ ((4 * n + 3) + 1) := ⟨n + 1, by ring⟩
      rw [ite_eq_left h4]
      congr 1
    exact (hinj.hasProd_iff hside).mp hcomp0
  have hcomb : HasProd (fun i =>
      (if (i + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j) else 1) *
        (if 4 ∣ (i + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1) else 1))
      (pserZMod * expand 4 (by norm_num : (4 : ℕ) ≠ 0) (pentagonalSeries (ZMod 2))) :=
    hPser.mul hsqprod
  have hodd : HasProd (fun i => if ¬ Even (i + 1) then
      ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j) else 1)
      (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) :=
    Nat.Partition.hasProd_powerSeriesMk_card_restricted (ZMod 2) (fun i => ¬ Even i)
  have hodd' : HasProd (fun k => ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 1) * j))
      (pentagonalSeries (ZMod 2)) := by
    have hodd2 : HasProd (fun k => ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 1) * j))
        (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) := by
      have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun a b h => by
        dsimp only at h; omega
      have hside : ∀ x : ℕ, x ∉ Set.range (fun n : ℕ => 2 * n) →
          (if ¬ Even (x + 1) then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((x + 1) * j)
            else 1) = 1 := by
        intro x hx
        rw [ite_eq_right]
        intro hev
        apply hx
        exact ⟨x / 2, by
          change 2 * (x / 2) = x
          have h2 : (x + 1) % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hev)
          omega⟩
      have hcomp := (hinj.hasProd_iff hside).mpr hodd
      refine hcomp.congr_fun fun n => ?_
      simp only [Function.comp_def]
      rw [ite_eq_left (Nat.not_even_iff_odd.mpr ⟨n, rfl⟩ : ¬ Even (2 * n + 1))]
    have hdist : (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) =
        pentagonalSeries (ZMod 2) := by
      have hcard : (PowerSeries.mk fun n => ((Nat.Partition.odds n).card : ZMod 2)) =
          PowerSeries.mk fun n => ((Nat.Partition.distincts n).card : ZMod 2) := by
        ext n
        simp [Nat.Partition.card_odds_eq_card_distincts]
      have hdistprod : HasProd (fun i => (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1))
          (PowerSeries.mk fun n => ((Nat.Partition.countRestricted n 2).card : ZMod 2)) := by
        refine (Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 2)
          (by norm_num : 0 < 2)).congr_fun fun i => ?_
        simp [Finset.sum_range_succ]
      rw [hcard]
      simp only [← Nat.Partition.countRestricted_two]
      exact (hdistprod.tprod_eq.symm.trans hpent.tprod_eq)
    rw [hdist] at hodd2
    exact hodd2
  have heven : HasProd (fun k =>
      (if (2 * k + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 1) * j)
        else 1) *
        (if 4 ∣ (2 * k + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (2 * k + 1) else 1))
      (pentagonalSeries (ZMod 2)) := by
    refine hodd'.congr_fun fun k => ?_
    have hmod : (2 * k + 1) % 4 ≠ 2 := by omega
    have hdiv : ¬ 4 ∣ (2 * k + 1) := by omega
    rw [ite_eq_left hmod, ite_eq_right hdiv, mul_one]
  have hoddsub : HasProd (fun k =>
      (if (2 * k + 2) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((2 * k + 2) * j)
        else 1) *
        (if 4 ∣ (2 * k + 2) then (1 : (ZMod 2)⟦X⟧) + X ^ (2 * k + 2) else 1)) 1 := by
    refine hasProd_one.congr_fun fun k => ?_
    symm
    by_cases h4 : 4 ∣ (2 * k + 2)
    · have hmod : (2 * k + 2) % 4 ≠ 2 := by
        obtain ⟨t, ht⟩ := h4; omega
      rw [ite_eq_left hmod, ite_eq_left h4]
      exact (geom_mul_one_add (k := 2 * k + 2) (by omega)).symm
    · have hmod : (2 * k + 2) % 4 = 2 := by
        have h2 : 2 ∣ 2 * k + 2 := ⟨k + 1, by ring⟩
        omega
      rw [ite_eq_right (by omega : ¬ (2 * k + 2) % 4 ≠ 2), ite_eq_right h4, mul_one]
  have hsplit := HasProd.even_mul_odd (f := fun i =>
      (if (i + 1) % 4 ≠ 2 then ∑' j : ℕ, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j) else 1) *
        (if 4 ∣ (i + 1) then (1 : (ZMod 2)⟦X⟧) + X ^ (i + 1) else 1)) heven hoddsub
  have hval : (pentagonalSeries (ZMod 2)) * 1 =
      pserZMod * expand 4 (by norm_num : (4 : ℕ) ≠ 0) (pentagonalSeries (ZMod 2)) :=
    hsplit.tprod_eq.symm.trans hcomb.tprod_eq
  rw [hsq]
  exact hval.symm.trans (mul_one _)

/-- The $P_2$ series times the triangular series is $1$ modulo two. -/
private theorem pserZMod_mul_triZMod :
    pserZMod * triZMod = 1 := by
  have hmap : PowerSeries.map (Int.castRingHom (ZMod 2)) (qEulerProduct 1 * triangularSeries)
      = PowerSeries.map (Int.castRingHom (ZMod 2)) (qEulerProduct 2 ^ 2) :=
    congrArg _ eulerProduct_mul_triangularSeries
  rw [map_mul, map_pow, qEulerProduct_one, map_pentagonalSeries_zmod2] at hmap
  have hcoeff : (pentagonalSeries (ZMod 2)).coeff 0 = 1 := by
    have h1 := coeff_pentagonalSeries_pentagonal (R := ZMod 2) (0 : ℤ)
    have h0 : pentagonal (0 : ℤ) = 0 := by simp [pentagonal_def]
    rw [h0] at h1
    simpa using h1
  have hunit : IsUnit (pentagonalSeries (ZMod 2)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff]
    exact isUnit_one
  have key : (pserZMod * triZMod) * pentagonalSeries (ZMod 2) =
      1 * pentagonalSeries (ZMod 2) := by
    rw [mul_assoc, mul_comm triZMod, hmap, pserZMod_mul_sq_eq_pentagonal, one_mul]
  exact hunit.mul_right_cancel key

end partsNotTwoModFour_triangular_sum_even

/-- **Parity of a triangular sum of partitions with no part congruent to 2 modulo 4.** Write
$P_2(m)$ for the number of partitions of $m$ with no part congruent to $2$ modulo $4$. For every
positive integer $n$, the sum $\sum_{k \ge 0,\ k(k+1)/2 \le n} P_2(n - k(k+1)/2)$ is even.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 3 (`integers-2026-A60-cor-3`). -/
public theorem partsNotTwoModFour_triangular_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      partsNotTwoModFourCount (n - k * (k + 1) / 2)) := by
  have hconv : (partsNotTwoModFour_triangular_sum_even.pserZMod *
      partsNotTwoModFour_triangular_sum_even.triZMod).coeff n =
      ∑ k ∈ Finset.range (n + 1),
        partsNotTwoModFour_triangular_sum_even.pserZMod.coeff (n - k) *
          partsNotTwoModFour_triangular_sum_even.triZMod.coeff k := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_range_reflect
      (fun k => partsNotTwoModFour_triangular_sum_even.pserZMod.coeff (n - k) *
        partsNotTwoModFour_triangular_sum_even.triZMod.coeff k) (n + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have h1 : n + 1 - 1 - k = n - k := by omega
    rw [h1, Nat.sub_sub_self hk']
  have hTri : ∀ k ∈ Finset.range (n + 1),
      partsNotTwoModFour_triangular_sum_even.triZMod.coeff k =
        (if k ∈ (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2) then
          (1 : ZMod 2) else 0) := by
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [partsNotTwoModFour_triangular_sum_even.coeff_triZMod]
    by_cases hkm : k ∈ (Finset.range (k + 1)).image (fun t => t * (t + 1) / 2)
    · obtain ⟨t, ht, htk⟩ := Finset.mem_image.mp hkm
      have ht' : t ≤ k := by
        rw [Finset.mem_range] at ht
        omega
      have hmem2 : t * (t + 1) / 2 ∈
          (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2) :=
        Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
      rw [ite_eq_left hkm, ← htk, ite_eq_left hmem2]
    · have hnot2 : k ∉ (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2) := by
        intro hmem
        obtain ⟨t, ht, htk⟩ := Finset.mem_image.mp hmem
        exact hkm (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by
          have hle := partsNotTwoModFour_triangular_sum_even.le_triangular t
          omega), htk⟩)
      rw [ite_eq_right hkm, ite_eq_right hnot2]
  have htarget : (∑ k ∈ Finset.range (n + 1),
        partsNotTwoModFour_triangular_sum_even.pserZMod.coeff (n - k) *
          partsNotTwoModFour_triangular_sum_even.triZMod.coeff k : ZMod 2) =
      ((∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        partsNotTwoModFourCount (n - k * (k + 1) / 2) : ℕ) : ZMod 2) := by
    rw [Nat.cast_sum]
    calc ∑ k ∈ Finset.range (n + 1),
          partsNotTwoModFour_triangular_sum_even.pserZMod.coeff (n - k) *
            partsNotTwoModFour_triangular_sum_even.triZMod.coeff k
        = ∑ k ∈ Finset.range (n + 1),
            partsNotTwoModFour_triangular_sum_even.pserZMod.coeff (n - k) *
              (if k ∈ (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2) then
                (1 : ZMod 2) else 0) :=
          Finset.sum_congr rfl fun k hk => by rw [hTri k hk]
      _ = ∑ k ∈ (Finset.range (n + 1)).filter
            (fun k => k ∈ (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2)),
            partsNotTwoModFour_triangular_sum_even.pserZMod.coeff (n - k) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hkm : k ∈ (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2)
          · rw [ite_eq_left hkm, ite_eq_left hkm, mul_one]
          · rw [ite_eq_right hkm, ite_eq_right hkm, mul_zero]
      _ = ∑ k ∈ (Finset.range (n + 1)).filter
            (fun k => k ∈ (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2)),
            (partsNotTwoModFourCount (n - k) : ZMod 2) :=
          Finset.sum_congr rfl fun k _ =>
            partsNotTwoModFour_triangular_sum_even.coeff_pserZMod _
      _ = ∑ t ∈ (Finset.range (n + 1)).filter (fun t => t * (t + 1) / 2 ≤ n),
            (partsNotTwoModFourCount (n - t * (t + 1) / 2) : ZMod 2) := by
          have hset : (Finset.range (n + 1)).filter
                (fun k => k ∈ (Finset.range (n + 1)).image (fun t => t * (t + 1) / 2))
              = ((Finset.range (n + 1)).filter
                  (fun t => t * (t + 1) / 2 ≤ n)).image (fun t => t * (t + 1) / 2) := by
            ext k
            constructor
            · intro hk
              rw [Finset.mem_filter] at hk
              obtain ⟨hkr, hki⟩ := hk
              obtain ⟨t, htr, rfl⟩ := Finset.mem_image.mp hki
              refine Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htr, ?_⟩, rfl⟩
              rw [Finset.mem_range] at hkr
              have hle := partsNotTwoModFour_triangular_sum_even.le_triangular t
              omega
            · intro hk
              obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
              rw [Finset.mem_filter] at ht
              obtain ⟨htr, htT⟩ := ht
              refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,
                Finset.mem_image.mpr ⟨t, htr, rfl⟩⟩
              rw [Finset.mem_range] at htr
              omega
          rw [hset, Finset.sum_image
            (partsNotTwoModFour_triangular_sum_even.triangular_injective.injOn)]
  have hcoeff : (partsNotTwoModFour_triangular_sum_even.pserZMod *
      partsNotTwoModFour_triangular_sum_even.triZMod).coeff n =
      ((∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        partsNotTwoModFourCount (n - k * (k + 1) / 2) : ℕ) : ZMod 2) :=
    hconv.trans htarget
  rw [partsNotTwoModFour_triangular_sum_even.pserZMod_mul_triZMod] at hcoeff
  have h0 : ((∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      partsNotTwoModFourCount (n - k * (k + 1) / 2) : ℕ) : ZMod 2) = 0 := by
    rw [← hcoeff]
    simp [PowerSeries.coeff_one, hn.ne']
  rw [← ZMod.natCast_eq_zero_iff_even]
  exact h0

end MetaMathlibExt
