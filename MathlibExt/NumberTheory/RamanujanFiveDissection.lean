/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

/-!
# Ramanujan's five-dissection of Euler's product

The five residue classes of Euler's pentagonal series give a central Euler product and two
bilateral series, evaluated by the two relevant specializations of Watson's quintuple product.
The quintuple evaluations follow by multiplying two Jacobi series and grouping their terms by
an integer linear form modulo three; a sign-reversing involution cancels the third class.

## References

* L. Carlitz and M. V. Subbarao, *A Simple Proof of the Quintuple Product Identity*,
  Proc. Amer. Math. Soc. **32** (1972), no. 1, 42–44, §2, for the product of two Jacobi
  series, the regrouping modulo three, and the sign-reversing reindexing.
* M. D. Hirschhorn, *The Power of q: A Personal Journey*, Developments in Mathematics **49**,
  Springer, Cham, 2017, Chapter 8, pp. 85–92, the reference cited for the five-dissection
  by Harishkumar, Menezes, and Mahadeva Naika.
-/

namespace MetaMathlibExt

open QPochhammer
open Analysis.SpecialFunctions.JacobiTripleProduct

local notation "P" => qPochhammerInfRaw

private lemma norm_pow_lt_one {q : ℂ} (hq : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hk

private lemma poch_ne_zero {a q : ℂ} (ha : ‖a‖ < 1) (hq : ‖q‖ < 1) : P a q ≠ 0 := by
  unfold qPochhammerInfRaw
  simp_rw [sub_eq_add_neg, ← neg_mul]
  apply tprod_one_add_ne_zero_of_summable
  · intro n hn
    have h : a * q ^ n = 1 := by linear_combination -hn
    have hnorm := calc
      ‖a * q ^ n‖ = ‖a‖ * ‖q‖ ^ n := by rw [norm_mul, norm_pow]
      _ ≤ ‖a‖ := mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
      _ < 1 := ha
    simp [h] at hnorm
  · simpa only [norm_mul, norm_neg, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖

private lemma poch_even_odd (a p : ℂ) (hp : ‖p‖ < 1) :
    P a (p ^ 2) * P (a * p) (p ^ 2) = P a p := by
  have h := norm_pow_lt_one hp two_ne_zero
  refine (HasProd.even_mul_odd (f := fun n : ℕ ↦ 1 - a * p ^ n) ?_ ?_).unique
    (hasProd_qPochhammerInf a p hp)
  · exact (hasProd_qPochhammerInf a (p ^ 2) h).congr_fun fun n ↦ by rw [pow_mul]
  · exact (hasProd_qPochhammerInf (a * p) (p ^ 2) h).congr_fun fun n ↦ by
      rw [pow_add, pow_mul, pow_one]
      ring

private lemma poch_mul_neg (a p : ℂ) (hp : ‖p‖ < 1) :
    P a p * P (-a) p = P (a ^ 2) (p ^ 2) := by
  refine ((hasProd_qPochhammerInf a p hp).mul (hasProd_qPochhammerInf (-a) p hp)).unique
    ((hasProd_qPochhammerInf (a ^ 2) (p ^ 2) (norm_pow_lt_one hp two_ne_zero)).congr_fun
      fun n ↦ ?_)
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul]
  ring

private def tri (n : ℤ) : ℤ := n * (n - 1) / 2

private lemma two_mul_tri (n : ℤ) : 2 * tri n = n * (n - 1) := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
  have h : n * (n - 1) = k + k := by linear_combination hk
  unfold tri
  omega

private lemma tri_nonneg (n : ℤ) : 0 ≤ tri n := by
  apply Int.ediv_nonneg _ (by decide)
  rcases le_or_gt n 0 with hn | hn
  · exact mul_nonneg_of_nonpos_of_nonpos hn (by omega)
  · exact mul_nonneg hn.le (by omega)

private noncomputable def thetaTerm (q : ℂ) (k a : ℕ) (s : ℂ) (n : ℤ) : ℂ :=
  s ^ n * q ^ ((k : ℤ) * tri n + (a : ℤ) * n)

/-- The Jacobi product in a form with integral exponents of the original nome. -/
private lemma theta_hasSum {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    {k a : ℕ} (hk : k ≠ 0) (hak : a ≤ k) {s : ℂ} (hs : s ≠ 0) :
    HasSum (thetaTerm q k a s)
      (P (q ^ k) (q ^ k) * P (-(s * q ^ a)) (q ^ k) * P (-(s⁻¹ * q ^ (k - a))) (q ^ k)) := by
  have hqk := norm_pow_lt_one hq hk
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (q ^ k) (n := 2) zero_lt_two
  have hr0 : r ≠ 0 := by
    intro h
    exact pow_ne_zero k hq0 (by simpa [h] using hr.symm)
  have hr1 : ‖r‖ < 1 := by
    apply (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
    rwa [← norm_pow, hr]
  let z := s * q ^ a / r
  have hz : z ≠ 0 := div_ne_zero (mul_ne_zero hs (pow_ne_zero _ hq0)) hr0
  have hzr : z * r = s * q ^ a := by simp [z, hr0]
  have hzri : z⁻¹ * r = s⁻¹ * q ^ (k - a) := by
    calc
      z⁻¹ * r = r ^ 2 / (z * r) := by field_simp
      _ = s⁻¹ * q ^ (k - a) := by
        rw [hzr, hr, show q ^ k = q ^ (k - a) * q ^ a by rw [← pow_add, Nat.sub_add_cancel hak]]
        field_simp
  obtain ⟨hsum, _, hj⟩ := jacobi_triple_product z r hz hr1
  have hp := (((hasProd_qPochhammerInf (q ^ k) (q ^ k) hqk).mul
    (hasProd_qPochhammerInf (-(s * q ^ a)) (q ^ k) hqk)).mul
    (hasProd_qPochhammerInf (-(s⁻¹ * q ^ (k - a))) (q ^ k) hqk)).congr_fun
      (g := fun n : ℕ ↦ (1 - r ^ (2 * n + 2)) * (1 + z * r ^ (2 * n + 1)) *
        (1 + z⁻¹ * r ^ (2 * n + 1))) fun n ↦ by
    have he : r ^ (2 * n + 2) = q ^ k * (q ^ k) ^ n := by
      rw [← hr, ← pow_succ', ← pow_mul, Nat.mul_succ]
    have ho : r ^ (2 * n + 1) = r * (q ^ k) ^ n := by rw [← hr, ← pow_mul, pow_succ']
    simp only [he, ho, ← mul_assoc, hzr, hzri, neg_mul, sub_neg_eq_add]
  rw [hp.tprod_eq] at hj
  refine (hj ▸ hsum.hasSum).congr_fun (g := thetaTerm q k a s) fun n ↦ ?_
  symm
  rw [thetaTerm, show z = s * (q ^ a / r) by simp [z, mul_div_assoc], mul_zpow, div_zpow,
    ← zpow_natCast r, Int.toNat_of_nonneg (mul_self_nonneg n), mul_assoc, div_mul_eq_mul_div,
    mul_div_assoc, ← zpow_sub₀ hr0, show n * n - n = 2 * tri n by
      linear_combination -(two_mul_tri n), zpow_mul, show r ^ (2 : ℤ) = q ^ k by exact_mod_cast hr,
    ← zpow_natCast q a, ← zpow_natCast q k, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq0, add_comm]

local notation "ε" => (-1 : ℂ)

/-- Mathlib's pentagonal number theorem, written using `thetaTerm` and the raw product. -/
private lemma euler_hasSum {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (thetaTerm q 3 1 ε) (P q q) := by
  have hp : eulerFunction q = P q q := by
    rw [eulerFunction_eq_tprod hq, qPochhammerInfRaw]
    exact tprod_congr fun n ↦ by rw [pow_succ']
  rw [← hp]
  refine (hasSum_eulerFunction_pentagonal hq).congr_fun (g := thetaTerm q 3 1 ε) fun n ↦ ?_
  have hn : (pentagonal n : ℤ) = 3 * tri n + n := by
    have h : 2 * ((pentagonal n : ℤ) - (3 * tri n + n)) = 0 := by
      linear_combination two_mul_natCast_pentagonal n - 3 * two_mul_tri n
    omega
  simp only [Int.cast_negOnePow, ← zpow_natCast q (pentagonal n), hn, thetaTerm,
    Nat.cast_ofNat, Nat.cast_one, one_mul]

/-- The theta ratio in the five-dissection comes from the signed Jacobi evaluations. -/
private lemma ramanujan_prod {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    {a b : ℕ} (hab : a + b = 5) :
    ramanujanThetaRaw (-q ^ a) (-q ^ b) =
      P (q ^ 5) (q ^ 5) * P (q ^ a) (q ^ 5) * P (q ^ b) (q ^ 5) := by
  have h := theta_hasSum hq0 hq (k := 5) (a := a) (by decide) (by omega) (s := ε) (by norm_num)
  have hb : 5 - a = b := by omega
  rw [hb] at h
  simp only [inv_neg, inv_one, neg_one_mul, neg_neg] at h
  unfold ramanujanThetaRaw
  refine (h.congr_fun (g := ramanujanThetaTerm (-q ^ a) (-q ^ b)) fun n ↦ ?_).tsum_eq
  have hs : tri (n + 1) = tri n + n := by
    have h1 := two_mul_tri (n + 1)
    have h2 := two_mul_tri n
    have h3 : 2 * tri (n + 1) - 2 * tri n = 2 * n := by linear_combination h1 - h2
    omega
  have hn : (n * (n + 1) / 2) = tri (n + 1) := by
    unfold tri
    rw [show n + 1 - 1 = n by ring, mul_comm]
  rw [ramanujanThetaTerm, hn, show n * (n - 1) / 2 = tri n from rfl,
    ← zpow_natCast (-q ^ a) (tri (n + 1)).toNat, ← zpow_natCast (-q ^ b) (tri n).toNat,
    Int.toNat_of_nonneg (tri_nonneg (n + 1)), Int.toNat_of_nonneg (tri_nonneg n),
    thetaTerm, neg_eq_neg_one_mul (q ^ a), neg_eq_neg_one_mul (q ^ b),
    mul_zpow (-1) (q ^ a), mul_zpow (-1) (q ^ b),
    ← zpow_natCast q a, ← zpow_natCast q b, ← zpow_mul, ← zpow_mul]
  calc
    _ = (ε ^ tri (n + 1) * ε ^ tri n) * (q ^ ((a : ℤ) * tri (n + 1)) * q ^ ((b : ℤ) * tri n)) :=
      by ring
    _ = _ := by
      rw [← zpow_add₀ (by norm_num : ε ≠ 0), ← zpow_add₀ hq0, hs]
      have hsign : ε ^ (tri n + n + tri n) = ε ^ n := by
        rw [show tri n + n + tri n = 2 * tri n + n by ring, zpow_add₀ (by norm_num : ε ≠ 0),
          zpow_mul, show ε ^ (2 : ℤ) = 1 by norm_num, one_zpow, one_mul]
      have hab' : (a : ℤ) + b = 5 := by exact_mod_cast hab
      rw [hsign, show (a : ℤ) * (tri n + n) + b * tri n = (5 : ℤ) * tri n + a * n by
        linear_combination tri n * hab']
      norm_cast

private lemma int_eq_of_twice_eq {a b : ℤ} (h : 2 * a = 2 * b) : a = b := by omega

/-! ### Watson's quintuple evaluations at the fifth-power nome -/

/-- The classes of `(a,b)` according to `a + 2b` modulo three. In each class we write
`a + 2b = 3n + r` and `b = n + j`. -/
private def pairClasses : Fin 3 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun x := (x.2.1 + (x.1.val : ℤ) - 2 * x.2.2, x.2.1 + x.2.2)
  invFun y := (⟨((y.1 + 2 * y.2) % 3).toNat, by omega⟩,
    (y.1 + 2 * y.2) / 3, y.2 - (y.1 + 2 * y.2) / 3)
  left_inv := by
    rintro ⟨⟨r, hr⟩, n, j⟩
    have hr' : (r : ℤ) < 3 := by exact_mod_cast hr
    apply Prod.ext
    · apply Fin.ext
      simp only
      omega
    · apply Prod.ext <;> simp only <;> omega
  right_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext <;> simp only <;> omega

private noncomputable def quintOuter (q : ℂ) (i : ℕ) (r n : ℤ) : ℂ :=
  ε ^ n * q ^ (15 * tri n + (5 + 3 * (i : ℤ) + 5 * r) * n + 5 * tri r + i * r)

private noncomputable def quintInner (q : ℂ) (r j : ℤ) : ℂ :=
  ε ^ j * q ^ (15 * j * j + (5 - 10 * r) * j)

private lemma quint_term {q : ℂ} (hq0 : q ≠ 0) (i : ℕ) (r n j : ℤ) :
    thetaTerm q 5 i 1 (n + r - 2 * j) * thetaTerm q 10 (5 + 2 * i) ε (n + j) =
      quintOuter q i r n * quintInner q r j := by
  have he : (5 : ℤ) * tri (n + r - 2 * j) + i * (n + r - 2 * j) +
      (10 * tri (n + j) + (5 + 2 * (i : ℤ)) * (n + j)) =
      (15 * tri n + (5 + 3 * (i : ℤ) + 5 * r) * n + 5 * tri r + i * r) +
        (15 * j * j + (5 - 10 * r) * j) := by
    apply int_eq_of_twice_eq
    linear_combination 5 * two_mul_tri (n + r - 2 * j) + 10 * two_mul_tri (n + j) -
      15 * two_mul_tri n - 5 * two_mul_tri r
  simp only [thetaTerm, one_zpow, one_mul, quintOuter, quintInner, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  rw [zpow_add₀ (by norm_num : ε ≠ 0) n j]
  rw [mul_left_comm, mul_assoc (ε ^ n), ← zpow_add₀ hq0, he, zpow_add₀ hq0]
  ring

private lemma quint_inner_zero {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' j : ℤ, quintInner q 0 j = P (q ^ 10) (q ^ 10) := by
  have h := euler_hasSum (norm_pow_lt_one hq (by decide : (10 : ℕ) ≠ 0))
  rw [← h.tsum_eq, ← (Equiv.neg ℤ).tsum_eq (thetaTerm (q ^ 10) 3 1 ε)]
  refine tsum_congr fun j ↦ ?_
  simp only [quintInner, Equiv.neg_apply, thetaTerm, zpow_neg, ← inv_zpow, inv_neg, inv_one,
    Nat.cast_ofNat, Nat.cast_one, mul_zero, sub_zero, one_mul]
  rw [← zpow_natCast q 10, ← zpow_mul, show 15 * j * j + 5 * j = 10 * (3 * tri (-j) + -j) by
    linear_combination -15 * two_mul_tri (-j)]
  norm_cast

private lemma quint_inner_one {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' j : ℤ, quintInner q 1 j = P (q ^ 10) (q ^ 10) := by
  have h := euler_hasSum (norm_pow_lt_one hq (by decide : (10 : ℕ) ≠ 0))
  refine (tsum_congr fun j ↦ ?_).trans h.tsum_eq
  simp only [quintInner, thetaTerm, Nat.cast_ofNat, Nat.cast_one, mul_one, one_mul]
  rw [← zpow_natCast q 10, ← zpow_mul, show 15 * j * j + (5 - 10) * j = 10 * (3 * tri j + j) by
    linear_combination -15 * two_mul_tri j]
  norm_cast

private lemma quint_inner_two (q : ℂ) : ∑' j : ℤ, quintInner q 2 j = 0 := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun j ↦ 1 - j
      invFun := fun j ↦ 1 - j
      left_inv := by intro j; dsimp; omega
      right_inv := by intro j; dsimp; omega }
  have ht := e.tsum_eq (quintInner q 2)
  have he (j : ℤ) : quintInner q 2 (e j) = -quintInner q 2 j := by
    change quintInner q 2 (1 - j) = -quintInner q 2 j
    unfold quintInner
    rw [zpow_sub₀ (by norm_num : ε ≠ 0), zpow_one, div_eq_mul_inv, ← inv_zpow, inv_neg, inv_one]
    rw [show 15 * (1 - j) * (1 - j) + (5 - 10 * 2) * (1 - j) =
      15 * j * j + (5 - 10 * 2) * j by ring]
    ring
  simp_rw [he, tsum_neg] at ht
  linear_combination -ht / 2

private noncomputable def quintProd (q : ℂ) (i : ℕ) : ℂ :=
  P (q ^ 5) (q ^ 5) * P (-q ^ i) (q ^ 5) * P (-q ^ (5 - i)) (q ^ 5) *
    P (q ^ (5 + 2 * i)) (q ^ 10) * P (q ^ (5 - 2 * i)) (q ^ 10)

/-- The two surviving classes give Watson's quintuple product at `z = -q^i`, `i = 1, 2`. -/
private lemma quintuple_eval {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {i : ℕ} (hi : i ≤ 2) :
    (∑' n : ℤ, quintOuter q i 0 n) + (∑' n : ℤ, quintOuter q i 1 n) = quintProd q i := by
  let f := thetaTerm q 5 i 1
  let g := thetaTerm q 10 (5 + 2 * i) ε
  have hf := theta_hasSum hq0 hq (k := 5) (a := i) (by decide) (by omega) (s := 1) one_ne_zero
  have hg := theta_hasSum hq0 hq (k := 10) (a := 5 + 2 * i) (by decide) (by omega)
    (s := ε) (by norm_num)
  have hf' : Summable (fun n : ℤ ↦ ‖f n‖) := summable_norm_iff.mpr hf.summable
  have hg' : Summable (fun n : ℤ ↦ ‖g n‖) := summable_norm_iff.mpr hg.summable
  let w := fun x : ℤ × ℤ ↦ f x.1 * g x.2
  have hw : Summable w := summable_mul_of_summable_norm hf' hg'
  have hw' := pairClasses.summable_iff.mpr hw
  have hterm (r : Fin 3) (n j : ℤ) : w (pairClasses (r, n, j)) =
      quintOuter q i (r.val : ℤ) n * quintInner q (r.val : ℤ) j :=
    quint_term hq0 i _ n j
  have hsum : (∑' n, f n) * (∑' n, g n) =
      ((∑' n : ℤ, quintOuter q i 0 n) + (∑' n : ℤ, quintOuter q i 1 n)) *
        P (q ^ 10) (q ^ 10) := by
    rw [tsum_mul_tsum_of_summable_norm hf' hg']
    change ∑' x, w x = _
    rw [← pairClasses.tsum_eq w]
    change (∑' x, (w ∘ pairClasses) x) = _
    rw [hw'.tsum_prod, tsum_fintype, Fin.sum_univ_three]
    have hfiber (r : Fin 3) : (∑' y : ℤ × ℤ, w (pairClasses (r, y))) =
        ∑' n : ℤ, ∑' j : ℤ, w (pairClasses (r, n, j)) := (hw'.prod_factor r).tsum_prod
    simp_rw [Function.comp_apply, hfiber, hterm, tsum_mul_left, tsum_mul_right]
    norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    rw [quint_inner_zero hq, quint_inner_one hq, quint_inner_two]
    ring
  have hn := poch_ne_zero (norm_pow_lt_one hq (by decide : (10 : ℕ) ≠ 0))
    (norm_pow_lt_one hq (by decide : (10 : ℕ) ≠ 0))
  apply mul_right_cancel₀ hn
  change (∑' n, thetaTerm q 5 i 1 n) * (∑' n, thetaTerm q 10 (5 + 2 * i) ε n) = _ at hsum
  rw [hf.tsum_eq, hg.tsum_eq] at hsum
  simp only [one_mul, inv_one, inv_neg, neg_one_mul, neg_neg,
    show 10 - (5 + 2 * i) = 5 - 2 * i by omega] at hsum
  unfold quintProd
  linear_combination -hsum

/-! ### From quintuple products to theta ratios -/

private lemma quint_factors {a b c p : ℂ} (hp : ‖p‖ < 1) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hc : b ^ 2 = c * p) :
    P (-a) p * P (-b) p * P (a ^ 2 * p) (p ^ 2) * P c (p ^ 2) =
      (P (a ^ 2) p * P c p) / (P a p * P b p) := by
  apply (eq_div_iff (mul_ne_zero (poch_ne_zero ha hp) (poch_ne_zero hb hp))).2
  calc
    _ = (P a p * P (-a) p * P (a ^ 2 * p) (p ^ 2)) *
        (P b p * P (-b) p * P c (p ^ 2)) := by ring
    _ = _ := by
      rw [poch_mul_neg a p hp, poch_mul_neg b p hp, hc, mul_comm (P (c * p) (p ^ 2)),
        poch_even_odd (a ^ 2) p hp, poch_even_odd c p hp]

private lemma quint_product_one {q : ℂ} (hq : ‖q‖ < 1) : quintProd q 1 =
    P (q ^ 5) (q ^ 5) * ((P (q ^ 2) (q ^ 5) * P (q ^ 3) (q ^ 5)) /
      (P q (q ^ 5) * P (q ^ 4) (q ^ 5))) := by
  have h := quint_factors (c := q ^ 3) (p := q ^ 5) (norm_pow_lt_one hq (by decide))
    hq (norm_pow_lt_one hq (by decide : (4 : ℕ) ≠ 0))
    (show (q ^ 4) ^ 2 = q ^ 3 * q ^ 5 by ring)
  rw [show (q ^ 5) ^ 2 = q ^ 10 by ring, show q ^ 2 * q ^ 5 = q ^ 7 by ring] at h
  unfold quintProd
  norm_num only [pow_one, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul]
  simpa only [mul_assoc] using congrArg (P (q ^ 5) (q ^ 5) * ·) h

private lemma quint_product_two {q : ℂ} (hq : ‖q‖ < 1) : quintProd q 2 =
    P (q ^ 5) (q ^ 5) * ((P q (q ^ 5) * P (q ^ 4) (q ^ 5)) /
      (P (q ^ 2) (q ^ 5) * P (q ^ 3) (q ^ 5))) := by
  have h := quint_factors (c := q) (p := q ^ 5) (norm_pow_lt_one hq (by decide))
    (norm_pow_lt_one hq two_ne_zero) (norm_pow_lt_one hq (by decide : (3 : ℕ) ≠ 0))
    (show (q ^ 3) ^ 2 = q * q ^ 5 by ring)
  rw [show (q ^ 5) ^ 2 = q ^ 10 by ring, show (q ^ 2) ^ 2 = q ^ 4 by ring,
    show q ^ 4 * q ^ 5 = q ^ 9 by ring, mul_comm (P (q ^ 4) (q ^ 5))] at h
  unfold quintProd
  norm_num only [pow_one, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul]
  simpa only [mul_assoc] using congrArg (P (q ^ 5) (q ^ 5) * ·) h

/-! ### The five pentagonal classes -/

/-- Representatives of the five classes of the pentagonal index, oriented to match the two
quintuple series and the Euler series at `q^25`. -/
private def fiveClasses : Fin 5 × ℤ ≃ ℤ where
  toFun x := if x.1 = 0 then -5 * x.2 else if x.1 = 1 then 1 - 5 * x.2 else
    if x.1 = 2 then 5 * x.2 + 2 else if x.1 = 3 then 5 * x.2 + 3 else -5 * x.2 - 1
  invFun n := if n % 5 = 0 then (0, -(n / 5)) else if n % 5 = 1 then (1, -(n / 5)) else
    if n % 5 = 2 then (2, n / 5) else if n % 5 = 3 then (3, n / 5) else (4, -(n / 5) - 1)
  left_inv := by
    rintro ⟨r, n⟩
    fin_cases r <;> norm_num <;> try omega
    have hm : (-(5 * n) - 1) % 5 = 4 := by omega
    have hd : ¬ (5 : ℤ) ∣ -(5 * n) - 1 := by omega
    simp [hm, hd]
    omega
  right_inv := by
    intro n
    have hm : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases hm with h | h | h | h | h <;> simp [h] <;> omega

private lemma sign_neg (n : ℤ) : ε ^ (-n) = ε ^ n := by
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

private lemma sign_five (n r : ℤ) : ε ^ (5 * n + r) = ε ^ n * ε ^ r := by
  rw [zpow_add₀ (by norm_num : ε ≠ 0), zpow_mul]
  norm_num

private lemma pentagonal_class_zero (q : ℂ) (n : ℤ) :
    thetaTerm q 3 1 ε (-5 * n) = quintOuter (q ^ 5) 1 0 n := by
  have h : 3 * tri (-5 * n) + -5 * n = 5 * (15 * tri n + 8 * n) := by
    apply int_eq_of_twice_eq
    linear_combination 3 * two_mul_tri (-5 * n) - 75 * two_mul_tri n
  simp only [thetaTerm, quintOuter, Nat.cast_ofNat, Nat.cast_one, one_mul, mul_zero, add_zero,
    show tri 0 = 0 by decide]
  rw [show -5 * n = 5 * (-n) + 0 by ring, sign_five, sign_neg, zpow_zero, mul_one,
    show 5 * -n + 0 = -5 * n by ring, h, ← zpow_natCast q 5, ← zpow_mul]
  norm_num

private lemma pentagonal_class_one {q : ℂ} (hq0 : q ≠ 0) (n : ℤ) :
    thetaTerm q 3 1 ε (1 - 5 * n) = -q * thetaTerm (q ^ 25) 3 1 ε n := by
  have h : 3 * tri (1 - 5 * n) + (1 - 5 * n) = 25 * (3 * tri n + n) + 1 := by
    apply int_eq_of_twice_eq
    linear_combination 3 * two_mul_tri (1 - 5 * n) - 75 * two_mul_tri n
  simp only [thetaTerm, Nat.cast_ofNat, Nat.cast_one, one_mul]
  rw [h, zpow_add₀ hq0, zpow_one, ← zpow_natCast q 25, ← zpow_mul,
    show 1 - 5 * n = 5 * (-n) + 1 by ring, sign_five, sign_neg, zpow_one]
  norm_num
  ring

private lemma pentagonal_class_two (q : ℂ) (n : ℤ) :
    thetaTerm q 3 1 ε (5 * n + 2) = quintOuter (q ^ 5) 1 1 n := by
  have h : 3 * tri (5 * n + 2) + (5 * n + 2) = 5 * (15 * tri n + 13 * n + 1) := by
    apply int_eq_of_twice_eq
    linear_combination 3 * two_mul_tri (5 * n + 2) - 75 * two_mul_tri n
  simp only [thetaTerm, quintOuter, Nat.cast_ofNat, Nat.cast_one, one_mul, mul_one,
    show tri 1 = 0 by decide, mul_zero, add_zero]
  rw [h, sign_five, ← zpow_natCast q 5, ← zpow_mul]
  norm_num

private lemma pentagonal_class_three {q : ℂ} (hq0 : q ≠ 0) (n : ℤ) :
    thetaTerm q 3 1 ε (5 * n + 3) = -(q ^ 2) * quintOuter (q ^ 5) 2 1 n := by
  have h : 3 * tri (5 * n + 3) + (5 * n + 3) = 5 * (15 * tri n + 16 * n + 2) + 2 := by
    apply int_eq_of_twice_eq
    linear_combination 3 * two_mul_tri (5 * n + 3) - 75 * two_mul_tri n
  simp only [thetaTerm, quintOuter, Nat.cast_ofNat, Nat.cast_one, one_mul, mul_one,
    show tri 1 = 0 by decide, mul_zero, add_zero]
  rw [h, sign_five, zpow_add₀ hq0, zpow_ofNat q 2, ← zpow_natCast q 5, ← zpow_mul]
  norm_num
  ring

private lemma pentagonal_class_four {q : ℂ} (hq0 : q ≠ 0) (n : ℤ) :
    thetaTerm q 3 1 ε (-5 * n - 1) = -(q ^ 2) * quintOuter (q ^ 5) 2 0 n := by
  have h : 3 * tri (-5 * n - 1) + (-5 * n - 1) = 5 * (15 * tri n + 11 * n) + 2 := by
    apply int_eq_of_twice_eq
    linear_combination 3 * two_mul_tri (-5 * n - 1) - 75 * two_mul_tri n
  simp only [thetaTerm, quintOuter, Nat.cast_ofNat, Nat.cast_one, one_mul, mul_zero, add_zero,
    show tri 0 = 0 by decide]
  rw [h, show -5 * n - 1 = 5 * (-n) + (-1) by ring, sign_five, sign_neg,
    zpow_add₀ hq0, zpow_ofNat q 2, ← zpow_natCast q 5, ← zpow_mul]
  norm_num
  ring

private lemma euler_five_classes {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    P q q = quintProd (q ^ 5) 1 - q * P (q ^ 25) (q ^ 25) - q ^ 2 * quintProd (q ^ 5) 2 := by
  have he := euler_hasSum hq
  have hs := fiveClasses.summable_iff.mpr he.summable
  have h5 := norm_pow_lt_one hq (by decide : (5 : ℕ) ≠ 0)
  have hq5 := pow_ne_zero 5 hq0
  have h1 := quintuple_eval hq5 h5 (i := 1) (by decide)
  have h2 := quintuple_eval hq5 h5 (i := 2) (by decide)
  have h25 := euler_hasSum (norm_pow_lt_one hq (by decide : (25 : ℕ) ≠ 0))
  rw [← he.tsum_eq, ← fiveClasses.tsum_eq (thetaTerm q 3 1 ε)]
  change (∑' x, (thetaTerm q 3 1 ε ∘ fiveClasses) x) = _
  rw [hs.tsum_prod, tsum_fintype]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Function.comp_apply]
  change (∑' n, thetaTerm q 3 1 ε (-5 * n)) + ((∑' n, thetaTerm q 3 1 ε (1 - 5 * n)) +
    ((∑' n, thetaTerm q 3 1 ε (5 * n + 2)) + ((∑' n, thetaTerm q 3 1 ε (5 * n + 3)) +
    (∑' n, thetaTerm q 3 1 ε (-5 * n - 1))))) = _
  simp_rw [pentagonal_class_zero, pentagonal_class_one hq0, pentagonal_class_two,
    pentagonal_class_three hq0, pentagonal_class_four hq0, tsum_mul_left, h25.tsum_eq]
  linear_combination h1 - q ^ 2 * h2

private lemma ramanujan_zero : ramanujanThetaRaw 0 0 = 1 := by
  unfold ramanujanThetaRaw
  rw [tsum_eq_single 0, ramanujanThetaTerm_zero]
  intro n hn
  have he : n * (n + 1) / 2 = tri (n + 1) := by
    unfold tri
    rw [show n + 1 - 1 = n by ring, mul_comm]
  rw [ramanujanThetaTerm, he]
  rcases lt_or_gt_of_ne hn with h | h
  · have hpos : 0 < n * (n - 1) := mul_pos_of_neg_of_neg h (by omega)
    have hne : (n * (n - 1) / 2).toNat ≠ 0 := by
      have ht := two_mul_tri n
      unfold tri at ht
      omega
    simp [zero_pow hne]
  · have hpos : 0 < (n + 1) * (n + 1 - 1) := mul_pos (by omega) (by omega)
    have ht := two_mul_tri (n + 1)
    have hne : (tri (n + 1)).toNat ≠ 0 := by omega
    simp [zero_pow hne]

/-- **Ramanujan's 5-dissection of Euler's product.** Let $q$ be a complex number with
$|q| < 1$. For $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{n \ge 0} (1 - q^k q^{kn})$, and
for complex $a$, $b$ with $|a|, |b| < 1$ let $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2}
b^{n(n-1)/2}$ be Ramanujan's general theta function; all these products and series converge,
so the raw infinite product and the raw theta sum take these values. For $|x| < 1$ put
$R(x) = f(-x, -x^4) / f(-x^2, -x^3)$. Then
$f_1 = f_{25} \left( R(q^5)^{-1} - q - q^2 R(q^5) \right)$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 5 (`integers-2025-A69-lem-5`). -/
public theorem qPochhammerInf_five_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    let R : ℂ → ℂ := fun x => ramanujanThetaRaw (-x) (-x ^ 4) / ramanujanThetaRaw (-x ^ 2) (-x ^ 3)
    qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 25) (q ^ 25) * ((R (q ^ 5))⁻¹ - q - q ^ 2 * R (q ^ 5)) := by
  by_cases hq0 : q = 0
  · subst q
    simp [ramanujan_zero, qPochhammerInfRaw]
  let Q := q ^ 5
  have hQ := norm_pow_lt_one hq (by decide : (5 : ℕ) ≠ 0)
  have hQ0 := pow_ne_zero 5 hq0
  have hQ5 := norm_pow_lt_one hQ (by decide : (5 : ℕ) ≠ 0)
  have hn := poch_ne_zero hQ5 hQ5
  have hA := ramanujan_prod hQ0 hQ (a := 1) (b := 4) (by decide)
  have hB := ramanujan_prod hQ0 hQ (a := 2) (b := 3) (by decide)
  let A := P Q (Q ^ 5) * P (Q ^ 4) (Q ^ 5)
  let B := P (Q ^ 2) (Q ^ 5) * P (Q ^ 3) (Q ^ 5)
  have hR : ramanujanThetaRaw (-Q) (-Q ^ 4) / ramanujanThetaRaw (-Q ^ 2) (-Q ^ 3) = A / B := by
    rw [show ramanujanThetaRaw (-Q) (-Q ^ 4) = P (Q ^ 5) (Q ^ 5) * A by
      simpa only [pow_one, mul_assoc] using hA,
      show ramanujanThetaRaw (-Q ^ 2) (-Q ^ 3) = P (Q ^ 5) (Q ^ 5) * B by
        simpa only [mul_assoc] using hB, mul_div_mul_left _ _ hn]
  change P q q = P (q ^ 25) (q ^ 25) *
    ((ramanujanThetaRaw (-Q) (-Q ^ 4) / ramanujanThetaRaw (-Q ^ 2) (-Q ^ 3))⁻¹ - q -
      q ^ 2 * (ramanujanThetaRaw (-Q) (-Q ^ 4) / ramanujanThetaRaw (-Q ^ 2) (-Q ^ 3)))
  rw [hR, inv_div, euler_five_classes hq0 hq]
  change quintProd Q 1 - q * P (q ^ 25) (q ^ 25) - q ^ 2 * quintProd Q 2 = _
  dsimp only [A, B]
  rw [quint_product_one hQ, quint_product_two hQ, show Q ^ 5 = q ^ 25 by dsimp [Q]; ring]
  ring

end MetaMathlibExt
