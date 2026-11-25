/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.JacobiCubeEulerProduct
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# The Amdeberhan–Sellers–Singh congruences

The coefficients of the generalized cubic partition series satisfy the congruences modulo
seven and eleven. We derive the weighted pentagonal expansion of `f₁⁵ / f₂²` from Jacobi's
cube and triple product identities, then extract coefficients modulo each prime.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Generating function of generalized cubic partitions.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler products. For a natural number $c$, this is
the integer power series $1/(f_1 f_2^{c-1})$ in $q$, the inverse of $f_1 f_2^{c-1}$ (whose
constant term is $1$). For $c \ge 1$ its coefficient of $q^n$ is the number of partitions of
$n$ whose even parts may each come in $c$ colors. For $c = 0$ the exponent $c - 1$ is
truncated to $0$, so the series is then the inverse of $f_1$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionSeries (c : ℕ) : ℤ⟦X⟧ :=
  invOfUnit (𝔣 1 * 𝔣 2 ^ (c - 1)) 1

/-- **Generalized cubic partition numbers.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ be the
Euler products. For natural numbers $c$ and $n$, $a_c(n)$ is the integer coefficient of $q^n$
in the generating function of generalized cubic partitions, the power series
$1/(f_1 f_2^{c-1})$. For $c \ge 1$ it is the number of partitions of $n$ whose even parts may
each come in $c$ colors; $c = 1$ gives the partition numbers and $c = 2$ Chan's cubic
partition numbers. For $c = 0$ the exponent $c - 1$ is truncated to $0$, so $a_0(n)$ is also
the number of partitions of $n$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionCount (c n : ℕ) : ℤ :=
  coeff n (generalizedCubicPartitionSeries c)

/-- **Generating function identity for generalized cubic partition numbers.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler products and $a_c(n)$ the generalized cubic
partition numbers. For every natural number $c$,
$f_1 f_2^{c-1} \sum_{n \ge 0} a_c(n) q^n = 1$ as integer power series in $q$, where for
$c = 0$ the exponent $c - 1$ is truncated to $0$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_generatingFunction (c : ℕ) :
    𝔣 1 * 𝔣 2 ^ (c - 1) * PowerSeries.mk (generalizedCubicPartitionCount c) = 1 := by
  have hmk : PowerSeries.mk (generalizedCubicPartitionCount c) =
      generalizedCubicPartitionSeries c := by
    ext n
    simp [generalizedCubicPartitionCount]
  have hc : constantCoeff (𝔣 1 * 𝔣 2 ^ (c - 1)) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2)]
  rw [hmk, generalizedCubicPartitionSeries, mul_invOfUnit _ _ hc]

/-- **Generalized cubic partitions of zero.** For every natural number $c$, the generalized
cubic partition number $a_c(0)$ equals $1$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_zero (c : ℕ) :
    generalizedCubicPartitionCount c 0 = 1 := by
  have h := congrArg (coeff 0) (generalizedCubicPartitionCount_generatingFunction c)
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    one_pow, one_mul, map_one] at h
  simpa using h

namespace generalizedCubicPartitionCount_seven_eleven

open scoped PowerSeries.WithPiTopology

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

/-- Jacobi's triple product at `z = -1`. -/
private lemma signed_squares {q : ℂ} (h : ‖q‖ < 1) :
    HasSum (fun j : ℤ ↦ (j.negOnePow : ℂ) * q ^ (j * j).toNat)
      (eulerFunction q ^ 2 / eulerFunction (q ^ 2)) := by
  obtain ⟨hs, _, he⟩ :=
    Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product (-1) q (by norm_num) h
  have hA : HasProd (fun n : ℕ ↦ 1 - q ^ (2 * n + 2)) (eulerFunction (q ^ 2)) :=
    (hasProd_eulerFunction (norm_pow_lt h two_ne_zero)).congr_fun fun n ↦ by
      rw [← pow_mul]
      ring_nf
  have hP := (hA.mul (odd_minus_prod h)).mul (odd_minus_prod h)
  simp only [inv_neg, inv_one, neg_one_mul, ← sub_eq_add_neg, hP.tprod_eq] at he
  rw [show eulerFunction q ^ 2 / eulerFunction (q ^ 2) =
      eulerFunction (q ^ 2) * (eulerFunction q / eulerFunction (q ^ 2)) *
      (eulerFunction q / eulerFunction (q ^ 2)) by
    field_simp [euler_ne (norm_pow_lt h two_ne_zero)], ← he]
  simpa only [Int.cast_negOnePow] using hs.hasSum

private def tri (i : ℤ) : ℕ := (i * (i + 1) / 2).toNat

private lemma double_tri (i : ℤ) : 2 * (tri i : ℤ) = i * (i + 1) := by
  have h := Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self i)
  have hn : 0 ≤ i * (i + 1) := by
    rcases le_or_gt 0 i with hi | hi
    · positivity
    · exact mul_nonneg_of_nonpos_of_nonpos hi.le (by omega)
  simp only [tri, Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide : (0 : ℤ) ≤ 2))]
  exact h

private noncomputable def triangularTerm (q : ℂ) (i : ℤ) : ℂ :=
  (i.negOnePow : ℂ) * q ^ tri i

private noncomputable def squareTerm (q : ℂ) (j : ℤ) : ℂ :=
  (j.negOnePow : ℂ) * q ^ (j * j).toNat

private lemma bilateral_cube {q : ℂ} (h : ‖q‖ < 1) :
    HasSum (fun i : ℤ ↦ (2 * (i : ℂ) + 1) * triangularTerm q i)
      (eulerFunction q ^ 3 + eulerFunction q ^ 3) := by
  have hc := QPochhammer.jacobi_cube_euler_product_hasSum q h
  have hp : QPochhammer.qPochhammerInf q q h = eulerFunction q := by
    unfold QPochhammer.qPochhammerInf QPochhammer.qPochhammerInfRaw
    rw [eulerFunction_eq_tprod h]
    exact tprod_congr fun n ↦ by rw [pow_succ']
  rw [hp] at hc
  have ht (n : ℕ) : tri n = n * (n + 1) / 2 := by
    unfold tri
    rw [show (n : ℤ) * (n + 1) = ((n * (n + 1) : ℕ) : ℤ) by push_cast; ring,
      show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
    exact congrArg Int.toNat (Int.natCast_ediv _ 2).symm
  have hr (n : ℕ) : tri (-(n + 1 : ℤ)) = tri n := by
    have := double_tri (-(n + 1 : ℤ))
    have := double_tri (n : ℤ)
    exact_mod_cast (by nlinarith : (tri (-(n + 1 : ℤ)) : ℤ) = tri n)
  apply HasSum.of_nat_of_neg_add_one
  · refine hc.congr_fun fun n ↦ ?_
    simp [triangularTerm, ht]
    ring
  · refine hc.congr_fun fun n ↦ ?_
    simp only [triangularTerm, hr, Int.negOnePow_neg, Int.negOnePow_succ, ht,
      Units.val_neg, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Int.cast_negOnePow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

private lemma summable_triangular {q : ℂ} (h : ‖q‖ < 1) :
    Summable (triangularTerm q) := by
  apply Summable.of_norm
  refine (bilateral_cube h).summable.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun i ↦ ?_
  rw [norm_mul]
  apply le_mul_of_one_le_left (norm_nonneg _)
  have hi : (1 : ℤ) ≤ |2 * i + 1| := by
    rw [le_abs]
    omega
  rw [show 2 * (i : ℂ) + 1 = ((2 * i + 1 : ℤ) : ℂ) by push_cast; ring,
    Complex.norm_intCast]
  exact_mod_cast hi

private lemma summable_weighted_squares {q : ℂ} (h : ‖q‖ < 1) :
    Summable (fun j : ℤ ↦ (j : ℂ) * squareTerm q j) := by
  have hn : Summable (fun n : ℕ ↦ (n : ℝ) * ‖q‖ ^ n) := by
    simpa [norm_mul, norm_pow] using summable_norm_pow_mul_geometric_of_norm_lt_one 1 h
  have hz : Summable (fun j : ℤ ↦ (j.natAbs : ℝ) * ‖q‖ ^ j.natAbs) := by
    apply Summable.of_nat_of_neg <;> simpa using hn
  apply Summable.of_norm
  apply hz.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro j
  have hj : j.natAbs ≤ (j * j).toNat := by
    zify
    rw [Int.toNat_of_nonneg (mul_self_nonneg j)]
    rw [abs_le]
    constructor <;> nlinarith [Int.le_self_sq j, Int.le_self_sq (-j)]
  simpa [squareTerm, norm_mul, norm_pow, Complex.norm_intCast] using
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg q) h.le hj)
      (Nat.cast_nonneg (α := ℝ) j.natAbs)

/-- The three residue classes of `i + 2j`, in coordinates adapted to its quadratic form. -/
private def lattice (r : Fin 3) (a b : ℤ) : ℤ × ℤ :=
  if r = 0 then (a - 2 * b, a + b)
  else if r = 1 then (-(a - 2 * b) - 1, -(a + b))
  else (a + 1 - 2 * b, a + b)

private noncomputable def latticeEquiv : Fin 3 × (ℤ × ℤ) ≃ ℤ × ℤ :=
  Equiv.ofBijective (fun x ↦ lattice x.1 x.2.1 x.2.2) (by
    constructor
    · rintro ⟨r, a, b⟩ ⟨s, c, d⟩ h
      fin_cases r <;> fin_cases s <;> simp_all [lattice, Prod.mk.injEq] <;> omega
    · rintro ⟨i, j⟩
      let a := (i + 2 * j) / 3
      rcases (by omega : (i + 2 * j) % 3 = 0 ∨
          (i + 2 * j) % 3 = 1 ∨ (i + 2 * j) % 3 = 2) with h | h | h
      · exact ⟨⟨0, a, j - a⟩, by simp [lattice, a]; omega⟩
      · exact ⟨⟨2, a, j - a⟩, by simp [lattice, a]; omega⟩
      · exact ⟨⟨1, -a - 1, a + 1 - j⟩, by simp [lattice, a]; omega⟩)

private noncomputable def term (q : ℂ) (y : ℤ × ℤ) : ℂ :=
  ((2 * (y.1 + 2 * y.2) + 1 : ℤ) : ℂ) * ((y.1 + y.2).negOnePow : ℂ) *
    q ^ (tri y.1 + (y.2 * y.2).toNat)

private lemma term_split (q : ℂ) (i j : ℤ) :
    term q (i, j) = ((2 * (i : ℂ) + 1) * triangularTerm q i) * squareTerm q j +
      (4 * triangularTerm q i) * ((j : ℂ) * squareTerm q j) := by
  simp only [term, triangularTerm, squareTerm, Int.negOnePow_add, Units.val_mul, pow_add]
  push_cast
  ring

private lemma sum_term {q : ℂ} (h : ‖q‖ < 1) :
    HasSum (term q) ((eulerFunction q ^ 3 + eulerFunction q ^ 3) *
      (eulerFunction q ^ 2 / eulerFunction (q ^ 2))) := by
  have hs : HasSum (squareTerm q) _ := signed_squares h
  have hj := summable_weighted_squares h
  have hz : ∑' j : ℤ, (j : ℂ) * squareTerm q j = 0 := by
    have he := (Equiv.neg ℤ).tsum_eq (fun j : ℤ ↦ (j : ℂ) * squareTerm q j)
    have he' : -(∑' j : ℤ, (j : ℂ) * squareTerm q j) =
        ∑' j : ℤ, (j : ℂ) * squareTerm q j := by
      simpa [squareTerm, tsum_neg] using he
    linear_combination (-1 / 2 : ℂ) * he'
  have h₁ := (bilateral_cube h).mul hs
    (summable_mul_of_summable_norm (bilateral_cube h).summable.norm hs.summable.norm)
  have ht := (summable_triangular h).mul_left 4
  have h₂ := ht.hasSum.mul hj.hasSum (summable_mul_of_summable_norm ht.norm hj.norm)
  rw [hz, mul_zero] at h₂
  simpa only [add_zero] using (h₁.add h₂).congr_fun (fun ⟨i, j⟩ ↦ term_split q i j)

private noncomputable def weightedTerm (q : ℂ) (a : ℤ) : ℂ :=
  (6 * (a : ℂ) + 1) * q ^ pentagonal (-a)

private noncomputable def eulerTerm (q : ℂ) (b : ℤ) : ℂ :=
  (b.negOnePow : ℂ) * (q ^ 2) ^ pentagonal b

private lemma good_term (q : ℂ) (a b : ℤ) :
    term q (lattice 0 a b) = weightedTerm q a * eulerTerm q b := by
  have he : tri (a - 2 * b) + ((a + b) * (a + b)).toNat =
      pentagonal (-a) + 2 * pentagonal b := by
    zify
    rw [Int.toNat_of_nonneg (mul_self_nonneg _)]
    nlinarith [double_tri (a - 2 * b), two_mul_natCast_pentagonal_neg a,
      two_mul_natCast_pentagonal b]
  change term q (a - 2 * b, a + b) = _
  simp only [term, weightedTerm, eulerTerm, he, pow_add, pow_mul]
  rw [show a - 2 * b + (a + b) = 2 * a - b by ring, Int.negOnePow_sub,
    Int.negOnePow_two_mul, one_mul]
  push_cast
  ring

private lemma reflected_term (q : ℂ) (a b : ℤ) :
    term q (lattice 1 a b) = term q (lattice 0 a b) := by
  let i := a - 2 * b
  let j := a + b
  change term q (-i - 1, -j) = term q (i, j)
  have he : tri (-i - 1) = tri i := by
    zify
    nlinarith [double_tri (-i - 1), double_tri i]
  simp only [term, he, neg_mul_neg]
  rw [show -i - 1 + -j = -(i + j + 1) by ring, Int.negOnePow_neg, Int.negOnePow_succ]
  push_cast
  ring

private lemma bad_term (q : ℂ) (a b : ℤ) :
    term q (lattice 2 a (1 - b)) = -term q (lattice 2 a b) := by
  have he : tri (a + 1 - 2 * (1 - b)) + ((a + (1 - b)) * (a + (1 - b))).toNat =
      tri (a + 1 - 2 * b) + ((a + b) * (a + b)).toNat := by
    zify
    rw [Int.toNat_of_nonneg (mul_self_nonneg _), Int.toNat_of_nonneg (mul_self_nonneg _)]
    nlinarith [double_tri (a + 1 - 2 * (1 - b)), double_tri (a + 1 - 2 * b)]
  have h₀ : (2 : Fin 3) ≠ 0 := by decide
  have h₁ : (2 : Fin 3) ≠ 1 := by decide
  simp only [term, lattice, ite_eq_right h₀, ite_eq_right h₁, he]
  rw [show a + 1 - 2 * (1 - b) + (a + (1 - b)) = 2 * a + b by ring,
    show a + 1 - 2 * b + (a + b) = (2 * a - b) + 1 by ring,
    Int.negOnePow_succ, Int.negOnePow_sub, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]
  push_cast
  ring

private lemma summable_weighted {q : ℂ} (h : ‖q‖ < 1) : Summable (weightedTerm q) := by
  have hi : Function.Injective (fun a : ℤ ↦ lattice 0 a 0) :=
    fun a b hab ↦ by simpa [lattice] using hab
  simpa [Function.comp_def, good_term, eulerTerm, pentagonal_def] using
    (sum_term h).summable.comp_injective hi

/-- The derivative specialization of the quintuple product, grouped by `i + 2j` modulo three. -/
private lemma weighted_identity {q : ℂ} (h : ‖q‖ < 1) :
    (∑' a, weightedTerm q a) * eulerFunction (q ^ 2) ^ 2 = eulerFunction q ^ 5 := by
  let g (z : Fin 3 × (ℤ × ℤ)) := term q (latticeEquiv z)
  have hg : Summable g := (sum_term h).summable.comp_injective latticeEquiv.injective
  have hsum := latticeEquiv.tsum_eq (term q)
  change ∑' z, g z = _ at hsum
  rw [hg.tsum_prod, tsum_fintype, Fin.sum_univ_three, (sum_term h).tsum_eq] at hsum
  have he : HasSum (eulerTerm q) (eulerFunction (q ^ 2)) :=
    hasSum_eulerFunction_pentagonal (norm_pow_lt h two_ne_zero)
  have hgood : ∑' b : ℤ × ℤ, g (0, b) = (∑' a, weightedTerm q a) * eulerFunction (q ^ 2) := by
    change ∑' z : ℤ × ℤ, term q (lattice 0 z.1 z.2) = _
    simp_rw [good_term]
    rw [← he.tsum_eq, tsum_mul_tsum_of_summable_norm (summable_weighted h).norm he.summable.norm]
  have hrefl : ∀ b : ℤ × ℤ, g (1, b) = g (0, b) := fun b ↦ reflected_term q b.1 b.2
  let flip : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun ⟨a, b⟩ ↦ (a, 1 - b)
      invFun := fun ⟨a, b⟩ ↦ (a, 1 - b)
      left_inv := fun ⟨_, _⟩ ↦ by simp
      right_inv := fun ⟨_, _⟩ ↦ by simp }
  have hbad : ∑' b : ℤ × ℤ, g (2, b) = 0 := by
    have H := flip.tsum_eq (fun b ↦ g (2, b))
    have hn (b : ℤ × ℤ) : g (2, flip b) = -g (2, b) := bad_term q b.1 b.2
    simp_rw [hn, tsum_neg] at H
    linear_combination (-1 / 2 : ℂ) * H
  simp_rw [hrefl, hgood, hbad, add_zero] at hsum
  field_simp [euler_ne (norm_pow_lt h two_ne_zero)] at hsum
  exact hsum

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


private noncomputable def weightedSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (Function.extend pentagonal (fun k ↦ 1 - 6 * k) 0)

private lemma coeff_weighted (k : ℤ) :
    coeff (pentagonal k) weightedSeries = 1 - 6 * k := by
  simp [weightedSeries, pentagonal_injective.extend_apply]

private lemma coeff_weighted_zero {n : ℕ} (hn : n ∉ Set.range pentagonal) :
    coeff n weightedSeries = 0 := by
  simp [weightedSeries, Function.extend_apply' _ _ _ (by simpa using hn)]

private lemma represents_weighted : Represents weightedSeries (fun q ↦ ∑' k, weightedTerm q k) := by
  intro τ
  have h := summable_weighted (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
  have hi : Function.Injective (fun a : ℤ ↦ pentagonal (-a)) :=
    pentagonal_injective.comp neg_injective
  apply (hi.hasSum_iff ?_).mp
  · refine h.hasSum.congr_fun fun a ↦ ?_
    simp only [weightedTerm, coeff_weighted, Function.comp_apply, Int.cast_sub, Int.cast_one,
      Int.cast_mul, Int.cast_ofNat, Int.cast_neg]
    ring
  · intro n hn
    have h' : n ∉ Set.range pentagonal := fun ⟨k, hk⟩ ↦ hn ⟨-k, by simpa using hk⟩
    simp [coeff_weighted_zero h']

private lemma weighted_product : weightedSeries * 𝔣 2 ^ 2 = 𝔣 1 ^ 5 := by
  apply (represents_weighted.mul ((represents_euler 2 two_ne_zero).pow 2)).eq_of_eval
    ((represents_euler 1 one_ne_zero).pow 5)
  intro q _ h
  simpa using weighted_identity h

end Transfer

private lemma series_inverse (c : ℕ) :
    𝔣 1 * 𝔣 2 ^ (c - 1) * generalizedCubicPartitionSeries c = 1 := by
  have hm : mk (generalizedCubicPartitionCount c) = generalizedCubicPartitionSeries c := by
    ext n
    simp [generalizedCubicPartitionCount]
  rw [← hm]
  exact generalizedCubicPartitionCount_generatingFunction c

/-- In characteristic `p`, removing a factor `f₁ᵖ` preserves a vanishing residue class. -/
private lemma remove_euler_power (p : ℕ) [Fact p.Prime] (F A : ℤ⟦X⟧)
    (hFA : A * 𝔣 1 ^ p = F)
    (hF : ∀ d : ℕ, 24 * (d : ZMod p) + 2 = 0 → ((coeff d F : ℤ) : ZMod p) = 0)
    (n : ℕ) (hn : 24 * (n : ZMod p) + 2 = 0) : (p : ℤ) ∣ coeff n A := by
  let φ := PowerSeries.map (Int.castRingHom (ZMod p))
  let B := φ (generalizedCubicPartitionSeries 1)
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hu : 𝔣 1 * generalizedCubicPartitionSeries 1 = 1 := by simpa using series_inverse 1
  have hAB : φ A = φ F * B ^ p := by
    rw [← hFA, map_mul, map_pow, mul_assoc, ← mul_pow]
    simp [B, ← map_mul, hu]
  have hfrob := PowerSeries.map_frobenius_expand (f := B) p hp
  rw [ZMod.frobenius_zmod p, PowerSeries.map_id] at hfrob
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change coeff n (φ A) = 0
  rw [hAB, ← hfrob, coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = n := Finset.mem_antidiagonal.mp hab
  by_cases hb : p ∣ b
  · have hb' : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hb
    have ha : (a : ZMod p) = n := by
      simpa [hb'] using congrArg (fun k : ℕ ↦ (k : ZMod p)) hab'
    change ((coeff a F : ℤ) : ZMod p) * _ = 0
    rw [hF a (by rwa [ha]), zero_mul]
  · change coeff a (φ F) * coeff b (expand p hp B) = 0
    rw [coeff_expand_of_not_dvd _ _ _ hb, mul_zero]

private lemma pentagonal_product (p : ℕ) [Fact p.Prime]
    (hsq : ∀ x y : ZMod p, x ^ 2 + y ^ 2 = 0 → x = 0)
    (G : ℤ⟦X⟧) (hG : ∀ d, d ∉ Set.range pentagonal → coeff d G = 0)
    (n : ℕ) (hn : 24 * (n : ZMod p) + 2 = 0) :
    ((coeff n (weightedSeries * G) : ℤ) : ZMod p) = 0 := by
  rw [coeff_mul, Int.cast_sum]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = n := Finset.mem_antidiagonal.mp hab
  by_cases ha : a ∈ Set.range pentagonal
  · obtain ⟨i, rfl⟩ := ha
    by_cases hb : b ∈ Set.range pentagonal
    · obtain ⟨j, rfl⟩ := hb
      have hs (k : ℤ) : (1 - 6 * k) ^ 2 = 24 * (pentagonal k : ℤ) + 1 := by
        nlinarith [two_mul_natCast_pentagonal k]
      have hz (k : ℤ) : (1 - 6 * (k : ZMod p)) ^ 2 = 24 * (pentagonal k : ZMod p) + 1 := by
        simpa using congrArg (Int.castRingHom (ZMod p)) (hs k)
      have hzero : 1 - 6 * (i : ZMod p) = 0 := by
        apply hsq _ (1 - 6 * (j : ZMod p))
        rw [hz, hz]
        rw [← hab', Nat.cast_add] at hn
        linear_combination hn
      simp [coeff_weighted, hzero]
    · simp [hG _ hb]
  · simp [coeff_weighted_zero ha]

end generalizedCubicPartitionCount_seven_eleven

open generalizedCubicPartitionCount_seven_eleven in
/-- **Amdeberhan–Sellers–Singh congruences.** For every natural number $n$, the generalized
cubic partition numbers satisfy $a_3(7n + 4) \equiv 0 \pmod{7}$ and
$a_5(11n + 10) \equiv 0 \pmod{11}$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 1 (quoting Amdeberhan, Sellers, and
Singh), Equations (1) and (2). -/
public theorem generalizedCubicPartitionCount_seven_eleven (n : ℕ) :
    (7 : ℤ) ∣ generalizedCubicPartitionCount 3 (7 * n + 4) ∧
      (11 : ℤ) ∣ generalizedCubicPartitionCount 5 (11 * n + 10) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hW := weighted_product
  constructor
  · apply remove_euler_power 7 (weightedSeries * 𝔣 1)
    · have hc : 𝔣 1 * 𝔣 2 ^ 2 * generalizedCubicPartitionSeries 3 = 1 := series_inverse 3
      linear_combination weightedSeries * 𝔣 1 * hc -
        generalizedCubicPartitionSeries 3 * 𝔣 1 ^ 2 * hW
    · apply pentagonal_product
      · decide
      · intro d hd
        rw [qEulerProduct_one]
        exact coeff_pentagonalSeries_eq_zero _ hd
    · push_cast
      rw [show (7 : ZMod 7) = 0 by decide, zero_mul, zero_add]
      decide
  · apply remove_euler_power 11 (weightedSeries * weightedSeries)
    · have hc : 𝔣 1 * 𝔣 2 ^ 4 * generalizedCubicPartitionSeries 5 = 1 := series_inverse 5
      have hW₂ := congrArg (fun f : ℤ⟦X⟧ ↦ f ^ 2) hW
      linear_combination weightedSeries ^ 2 * hc - generalizedCubicPartitionSeries 5 * 𝔣 1 * hW₂
    · apply pentagonal_product
      · decide
      · exact fun _ ↦ coeff_weighted_zero
    · push_cast
      rw [show (11 : ZMod 11) = 0 by decide, zero_mul, zero_add]
      decide

end

end MetaMathlibExt
