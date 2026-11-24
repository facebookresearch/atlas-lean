/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Three-dissection of Ramanujan's phi function at negated argument

Splitting the bilateral theta series into its three residue classes and applying Jacobi's
triple product gives `ramanujanPhi_neg_dissection` in terms of infinite q-Pochhammer products.
-/

namespace MetaMathlibExt

open QPochhammer Analysis.SpecialFunctions.JacobiTripleProduct

namespace ramanujanPhi_neg_dissection

/-- Product of the factors with exponents `a * n + b`. -/
private noncomputable def progression (q : ℂ) (a b : ℕ) : ℂ :=
  qPochhammerInfRaw (q ^ b) (q ^ a)

private lemma norm_pow_lt {q : ℂ} (h : ‖q‖ < 1) {a : ℕ} (ha : a ≠ 0) : ‖q ^ a‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) h ha

private lemma hasProd_progression {q : ℂ} (h : ‖q‖ < 1) {a : ℕ} (ha : a ≠ 0) (b : ℕ) :
    HasProd (fun n : ℕ ↦ 1 - q ^ (a * n + b)) (progression q a b) := by
  refine (hasProd_qPochhammerInf (q ^ b) (q ^ a) (norm_pow_lt h ha)).congr_fun fun n ↦ ?_
  rw [pow_add, pow_mul, mul_comm]

private lemma progression_ne_zero {q : ℂ} (h : ‖q‖ < 1) {a b : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) : progression q a b ≠ 0 := by
  rw [← (hasProd_progression h ha b).tprod_eq]
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n hn
    have he : q ^ (a * n + b) = 1 := by linear_combination -hn
    have := norm_pow_lt h (show a * n + b ≠ 0 by omega)
    simp [he] at this
  · simpa [pow_add, pow_mul, norm_pow, norm_mul] using
      (summable_geometric_of_lt_one (norm_nonneg _) (norm_pow_lt h ha)).mul_right ‖q ^ b‖

/-- Group a progression by the residue of its index modulo `m`. -/
private lemma progression_split {q : ℂ} (h : ‖q‖ < 1) {a : ℕ} (ha : a ≠ 0) (b m : ℕ)
    [NeZero m] :
    progression q a b = ∏ i : Fin m, progression q (a * m) (a * i + b) := by
  let e := (Equiv.prodComm (Fin m) ℕ).trans (Nat.divModEquiv m).symm
  have hall := e.hasProd_iff.mpr (hasProd_progression h ha b)
  have hrow (i : Fin m) : HasProd (fun n : ℕ ↦ 1 - q ^ (a * (n * m + i) + b))
      (progression q (a * m) (a * i + b)) :=
    (hasProd_progression h (mul_ne_zero ha (NeZero.ne m)) _).congr_fun fun n ↦ by ring_nf
  exact (hall.prod_fiberwise hrow).unique (hasProd_fintype _)

private lemma split_even_odd {q : ℂ} (h : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) :
    progression q k k = progression q (2 * k) k * progression q (2 * k) (2 * k) := by
  simpa [Fin.prod_univ_two, two_mul, mul_two] using progression_split h hk k 2

/-- Summand of the alternating square theta series. -/
private noncomputable def thetaTerm (q : ℂ) (n : ℤ) : ℂ :=
  (-1 : ℂ) ^ n * q ^ (n * n)

private lemma theta_hasSum {q : ℂ} (h : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) :
    HasSum (thetaTerm (q ^ k)) (progression q k k ^ 2 / progression q (2 * k) (2 * k)) := by
  obtain ⟨hs, _, he⟩ := jacobi_triple_product (-1) (q ^ k) (by norm_num) (norm_pow_lt h hk)
  have heven := hasProd_progression h (mul_ne_zero two_ne_zero hk) (2 * k)
  have hodd := hasProd_progression h (mul_ne_zero two_ne_zero hk) k
  have hprod := ((heven.mul hodd).mul hodd).congr_fun
    (g := fun n : ℕ ↦ (1 - (q ^ k) ^ (2 * n + 2)) * (1 + (-1 : ℂ) * (q ^ k) ^ (2 * n + 1)) *
      (1 + (-1 : ℂ)⁻¹ * (q ^ k) ^ (2 * n + 1))) fun n ↦ by
      simp only [inv_neg, inv_one, ← pow_mul]
      ring_nf
  rw [hprod.tprod_eq] at he
  have hsum := hs.hasSum
  rw [he] at hsum
  have hne := progression_ne_zero h (mul_ne_zero two_ne_zero hk) (mul_ne_zero two_ne_zero hk)
  rw [split_even_odd h hk, mul_pow, pow_two (progression q (2 * k) (2 * k))]
  convert hsum.congr_fun (g := thetaTerm (q ^ k)) (fun n ↦ ?_) using 1
  · field_simp
  · rw [thetaTerm, ← zpow_natCast (q ^ k) (n * n).toNat, Int.toNat_of_nonneg (mul_self_nonneg n)]

/-- The two noncentral factors of the shifted triple product run over the exponents
congruent to 3 and 15 modulo 18. -/
private lemma shifted_product {q : ℂ} (h : ‖q‖ < 1) :
    progression q 18 18 * progression q 18 15 * progression q 18 3 =
      progression q 3 3 * progression q 18 18 ^ 2 /
        (progression q 6 6 * progression q 9 9) := by
  have hsplit : progression q 6 3 =
      progression q 18 3 * progression q 18 9 * progression q 18 15 := by
    simpa [Fin.prod_univ_three, mul_assoc] using
      progression_split h (a := 6) (by decide) 3 3
  have h3 := split_even_odd h (k := 3) (by decide)
  have h9 := split_even_odd h (k := 9) (by decide)
  have h6 := progression_ne_zero h (a := 6) (b := 6) (by decide) (by decide)
  have h9' := progression_ne_zero h (a := 9) (b := 9) (by decide) (by decide)
  rw [eq_div_iff (mul_ne_zero h6 h9'), h3, h9, hsplit]
  ring

private lemma sign_three (n : ℤ) : (-1 : ℂ) ^ (3 * n) = (-1 : ℂ) ^ n := by
  rw [zpow_mul]
  norm_num

private lemma pow_zpow (q : ℂ) (a : ℕ) (n : ℤ) : (q ^ a) ^ n = q ^ ((a : ℤ) * n) := by
  rw [← zpow_natCast q a, ← zpow_mul]

private lemma shifted_hasSum {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    HasSum (fun n : ℤ ↦ thetaTerm q (3 * n + 1))
      (-q * (progression q 3 3 * progression q 18 18 ^ 2 /
        (progression q 6 6 * progression q 9 9))) := by
  obtain ⟨hs, _, he⟩ := jacobi_triple_product (-q ^ 6) (q ^ 9) (by simp [hq])
    (norm_pow_lt h (by decide))
  have hp := ((hasProd_progression h (a := 18) (by decide) 18).mul
    (hasProd_progression h (a := 18) (by decide) 15)).mul
    (hasProd_progression h (a := 18) (by decide) 3)
  have hfac (n : ℕ) : (-q ^ 6)⁻¹ * (q ^ 9) ^ (2 * n + 1) = -q ^ (18 * n + 3) := by
    rw [inv_neg, ← pow_mul, show 9 * (2 * n + 1) = 6 + (18 * n + 3) by ring, pow_add]
    field_simp
  have hprod := hp.congr_fun (g := fun n : ℕ ↦
    (1 - (q ^ 9) ^ (2 * n + 2)) * (1 + -q ^ 6 * (q ^ 9) ^ (2 * n + 1)) *
      (1 + (-q ^ 6)⁻¹ * (q ^ 9) ^ (2 * n + 1))) fun n ↦ by
        rw [hfac]
        ring_nf
  rw [hprod.tprod_eq, shifted_product h] at he
  rw [← he]
  refine (hs.hasSum.mul_left (-q)).congr_fun fun n ↦ ?_
  rw [thetaTerm, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one,
    sign_three, show (-q ^ 6) = (-1 : ℂ) * q ^ 6 by ring, mul_zpow,
    ← zpow_natCast (q ^ 9) (n * n).toNat, Int.toNat_of_nonneg (mul_self_nonneg n),
    pow_zpow, pow_zpow]
  push_cast
  rw [show (3 * n + 1) * (3 * n + 1) = 1 + 6 * n + 9 * (n * n) by ring,
    zpow_add₀ hq, zpow_add₀ hq, zpow_one]
  ring

/-- Collect the terms with indices `3n`, `3n+1`, and `3n+2`. -/
private lemma three_classes {f : ℤ → ℂ} {s a b : ℂ} (hs : HasSum f s)
    (hsymm : ∀ n, f (-n) = f n) (h0 : HasSum (fun n : ℤ ↦ f (3 * n)) a)
    (h1 : HasSum (fun n : ℤ ↦ f (3 * n + 1)) b) : s = a + b + b := by
  have h2 : HasSum (fun n : ℤ ↦ f (3 * n + 2)) b := by
    refine ((Equiv.subLeft (-1 : ℤ)).hasSum_iff.mpr h1).congr_fun fun n ↦ ?_
    change f (3 * n + 2) = f (3 * (-1 - n) + 1)
    rw [show 3 * (-1 - n) + 1 = -(3 * n + 2) by ring, hsymm]
  have hall := (Int.divModEquiv 3).symm.hasSum_iff.mpr hs
  have hblock := hall.prod_fiberwise (fun n ↦ hasSum_fintype
    (fun i : Fin 3 ↦ f (n * 3 + i)))
  refine hblock.unique (((h0.add h1).add h2).congr_fun fun n ↦ ?_)
  simp [Fin.sum_univ_three, mul_comm]

end ramanujanPhi_neg_dissection

open ramanujanPhi_neg_dissection

/--
**3-dissection of the product form of Ramanujan's phi function at negated argument.** Let $q$ be
a complex number with $|q| < 1$, and for $k \ge 1$ let
$f_k = (q^k; q^k)_\infty = \prod_{n=0}^{\infty} (1 - q^k (q^k)^n)$ be the raw infinite
q-Pochhammer product. Then
$$\frac{f_1^2}{f_2} = \frac{f_9^2}{f_{18}} - 2q \frac{f_3 f_{18}^2}{f_6 f_9}.$$

Here $f_1^2/f_2$ is the product form of $\varphi(-q)$, where
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ is Ramanujan's theta function.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 5.
-/
public theorem ramanujanPhi_neg_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q ^ 2 / qPochhammerInfRaw (q ^ 2) (q ^ 2) =
      qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2 /
          qPochhammerInfRaw (q ^ 18) (q ^ 18) -
        2 * q * qPochhammerInfRaw (q ^ 3) (q ^ 3) *
            qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2 /
          (qPochhammerInfRaw (q ^ 6) (q ^ 6) *
            qPochhammerInfRaw (q ^ 9) (q ^ 9)) := by
  by_cases hzero : q = 0
  · simp [hzero, qPochhammerInfRaw]
  have hall := theta_hasSum hq (k := 1) one_ne_zero
  simp only [pow_one] at hall
  have h0 := (theta_hasSum hq (k := 9) (by decide)).congr_fun
    (g := fun n : ℤ ↦ thetaTerm q (3 * n)) fun n ↦ by
      rw [thetaTerm, thetaTerm, sign_three, pow_zpow]
      push_cast
      ring_nf
  have heven (n : ℤ) : thetaTerm q (-n) = thetaTerm q n := by
    by_cases hn : Even n <;> simp [thetaTerm, neg_one_zpow_eq_ite, hn]
  have he := three_classes hall heven h0 (shifted_hasSum hzero hq)
  simp only [progression, pow_one, Nat.reduceMul] at he
  linear_combination he

end MetaMathlibExt
