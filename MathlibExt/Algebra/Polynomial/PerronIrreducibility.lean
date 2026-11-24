/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.Basic

/-!
# Perron's irreducibility criterion

We work with the reciprocal polynomial. Any root in the closed unit disk has norm at most
`1 / 2`. On that smaller disk the divided difference of the higher-order terms is bounded by
their coefficient sum, so the dominant linear term prevents two roots, even with multiplicity.
A positive-degree monic integer factor with nonzero constant coefficient must have a root on
or outside the unit circle, by the product of its roots.
-/

open Polynomial

namespace MetaMathlibExt

/-- The polynomial quotient of `X ^ n - C (z ^ n)` by `X - C z`. -/
private noncomputable def powerQuotient (z : ℂ) : ℕ → ℂ[X]
  | 0 => 0
  | n + 1 => X ^ n + C z * powerQuotient z n

private theorem sub_C_pow_eq_mul_powerQuotient (z : ℂ) (n : ℕ) :
    X ^ n - C (z ^ n) = (X - C z) * powerQuotient z n := by
  induction n with
  | zero => simp [powerQuotient]
  | succ n ih =>
    calc
      X ^ (n + 1) - C (z ^ (n + 1)) =
          (X - C z) * X ^ n + C z * (X ^ n - C (z ^ n)) := by
        rw [pow_succ, pow_succ, map_mul]
        ring
      _ = _ := by rw [ih, powerQuotient]; ring

private theorem norm_pow_succ_le {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖z ^ (n + 1)‖ ≤ ‖z‖ := by
  rw [norm_pow, pow_succ]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

private theorem norm_eval_powerQuotient_le {z w : ℂ} (hz : ‖z‖ ≤ 1 / 2)
    (hw : ‖w‖ ≤ 1 / 2) (n : ℕ) : ‖(powerQuotient z n).eval w‖ ≤ 1 := by
  induction n with
  | zero => simp [powerQuotient]
  | succ n ih =>
    cases n with
    | zero => simp [powerQuotient]
    | succ n =>
      rw [powerQuotient, eval_add, eval_pow, eval_X, eval_mul, eval_C]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have hp := norm_pow_succ_le (hw.trans (by norm_num)) n
      have hm := mul_le_of_le_one_right (norm_nonneg z) ih
      linarith

/-- A reciprocal polynomial written with its constant, linear and higher-order terms separated. -/
private noncomputable def reciprocalForm (k : ℕ) (a : ℂ) (b : ℕ → ℂ) : ℂ[X] :=
  1 + C a * X + ∑ i ∈ Finset.range k, C (b i) * X ^ (i + 2)

private theorem eval_reciprocalForm (k : ℕ) (a : ℂ) (b : ℕ → ℂ) (z : ℂ) :
    (reciprocalForm k a b).eval z = 1 + a * z + ∑ i ∈ Finset.range k, b i * z ^ (i + 2) := by
  simp [reciprocalForm, eval_finsetSum]

private theorem norm_le_half_of_reciprocal_root {k : ℕ} {a : ℂ} {b : ℕ → ℂ}
    (hbig : 2 + ∑ i ∈ Finset.range k, ‖b i‖ ≤ ‖a‖) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hroot : (reciprocalForm k a b).IsRoot z) : ‖z‖ ≤ 1 / 2 := by
  have he := hroot
  rw [IsRoot, eval_reciprocalForm] at he
  have hlin : a * z = -(1 + ∑ i ∈ Finset.range k, b i * z ^ (i + 2)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_assoc, add_left_comm, add_comm] using he
  have htail : ‖∑ i ∈ Finset.range k, b i * z ^ (i + 2)‖ ≤
      (∑ i ∈ Finset.range k, ‖b i‖) * ‖z‖ := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_succ_le hz (i + 1)) (norm_nonneg _)
  have hbalance : ‖a‖ * ‖z‖ ≤ 1 + (∑ i ∈ Finset.range k, ‖b i‖) * ‖z‖ := by
    rw [← norm_mul, hlin, norm_neg]
    have h := norm_add_le (1 : ℂ) (∑ i ∈ Finset.range k, b i * z ^ (i + 2))
    rw [norm_one] at h
    exact h.trans (add_le_add_right htail 1)
  have hscaled := mul_le_mul_of_nonneg_right hbig (norm_nonneg z)
  linarith

private theorem reciprocal_dvd_difference (k : ℕ) (a : ℂ) (b : ℕ → ℂ) (z : ℂ) :
    reciprocalForm k a b - C ((reciprocalForm k a b).eval z) =
      (X - C z) * (C a + ∑ i ∈ Finset.range k, C (b i) * powerQuotient z (i + 2)) := by
  rw [eval_reciprocalForm, reciprocalForm, map_add, map_add, map_one, map_mul, map_sum]
  rw [mul_add, Finset.mul_sum]
  have hsum : (∑ i ∈ Finset.range k, (X - C z) * (C (b i) * powerQuotient z (i + 2))) =
      (∑ i ∈ Finset.range k, C (b i) * X ^ (i + 2)) -
        ∑ i ∈ Finset.range k, C (b i * z ^ (i + 2)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_left_comm, ← sub_C_pow_eq_mul_powerQuotient, mul_sub, map_mul]
  rw [hsum]
  ring

-- Keeping the product of the two linear factors also covers the case `z = w`.
private theorem not_two_reciprocal_roots {k : ℕ} {a : ℂ} {b : ℕ → ℂ}
    (hbig : 2 + ∑ i ∈ Finset.range k, ‖b i‖ ≤ ‖a‖) {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hfac : (X - C z) * (X - C w) ∣ reciprocalForm k a b) : False := by
  obtain ⟨q, hq⟩ := hfac
  have hzroot : (reciprocalForm k a b).IsRoot z := by simp [IsRoot, hq]
  have hwroot : (reciprocalForm k a b).IsRoot w := by simp [IsRoot, hq]
  have hz' := norm_le_half_of_reciprocal_root hbig hz hzroot
  have hw' := norm_le_half_of_reciprocal_root hbig hw hwroot
  have hd := reciprocal_dvd_difference k a b z
  rw [show (reciprocalForm k a b).eval z = 0 from hzroot, map_zero, sub_zero] at hd
  have hquot := mul_left_cancel₀ (X_sub_C_ne_zero z) (hd.symm.trans (hq.trans (mul_assoc _ _ _)))
  have he := congrArg (fun p : ℂ[X] ↦ p.eval w) hquot
  have hlin : a = -(∑ i ∈ Finset.range k, b i * (powerQuotient z (i + 2)).eval w) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [eval_finsetSum] using he
  have htail : ‖∑ i ∈ Finset.range k, b i * (powerQuotient z (i + 2)).eval w‖ ≤
      ∑ i ∈ Finset.range k, ‖b i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_powerQuotient_le hz' hw' _)
  rw [hlin, norm_neg] at hbig
  linarith

private theorem reverse_map_eq_reciprocalForm {f : ℤ[X]} (hf : f.Monic) {k : ℕ}
    (hdeg : f.natDegree = k + 1) :
    f.reverse.map (Int.castRingHom ℂ) =
      reciprocalForm k (f.coeff k : ℂ) (fun i ↦ (f.reverse.coeff (i + 2) : ℂ)) := by
  have hle := (natDegree_map_le (f := Int.castRingHom ℂ) (p := f.reverse)).trans
    (reverse_natDegree_le f)
  rw [hdeg] at hle
  calc
    _ = ∑ i ∈ Finset.range (k + 2), monomial i ((f.reverse.map (Int.castRingHom ℂ)).coeff i) :=
      as_sum_range' _ _ (by omega)
    _ = _ := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hnext : f.reverse.coeff 1 = f.coeff k := by
        rw [coeff_reverse, revAt_le (by omega), hdeg, Nat.add_sub_cancel]
      simp only [reciprocalForm, ← C_mul_X_pow_eq_monomial, coeff_map, coeff_zero_reverse,
        hf.leadingCoeff, Int.coe_castRingHom, Int.cast_one, C_1, pow_zero, mul_one, zero_add,
        add_assoc, Nat.reduceAdd, pow_one, hnext]
      ac_rfl

private theorem norm_prod_roots_lt_one {s : Multiset ℂ} (hs : s ≠ 0)
    (h : ∀ z ∈ s, ‖z‖ < 1) : ‖s.prod‖ < 1 := by
  induction s using Multiset.induction_on with
  | empty => exact (hs rfl).elim
  | cons z s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have hz := h z (Multiset.mem_cons_self _ _)
    have ht : ‖s.prod‖ ≤ 1 := by
      by_cases he : s = 0
      · simp [he]
      · exact (ih he fun w hw ↦ h w (Multiset.mem_cons_of_mem hw)).le
    exact (mul_le_of_le_one_right (norm_nonneg z) ht).trans_lt hz

private theorem exists_large_root_of_monic {g : ℤ[X]} (hg : g.Monic) (hdeg : g.natDegree ≠ 0)
    (h0 : g.coeff 0 ≠ 0) : ∃ z : ℂ, 1 ≤ ‖z‖ ∧ (g.map (Int.castRingHom ℂ)).IsRoot z := by
  let G := g.map (Int.castRingHom ℂ)
  have hm : G.Monic := hg.map _
  have hs : G.Splits := IsAlgClosed.splits _
  have hdegG : G.natDegree ≠ 0 := by simpa only [G, hg.natDegree_map] using hdeg
  by_contra! h
  have hprod := norm_prod_roots_lt_one (hs.roots_ne_zero hdegG) fun z hz ↦
    lt_of_not_ge fun hge ↦ h z hge ((mem_roots hm.ne_zero).mp hz)
  have hcoeff : ‖G.coeff 0‖ < 1 := by
    rw [hs.coeff_zero_eq_prod_roots_of_monic hm, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul]
    exact hprod
  have hone := Int.one_le_abs h0
  rw [show G.coeff 0 = (g.coeff 0 : ℂ) by simp [G], Complex.norm_intCast, ← Int.cast_abs] at hcoeff
  exact (not_lt_of_ge (by exact_mod_cast hone : (1 : ℝ) ≤ _)) hcoeff

private theorem inverse_isRoot_reverse {g : ℤ[X]} {z : ℂ} (hz : z ≠ 0)
    (hroot : (g.map (Int.castRingHom ℂ)).IsRoot z) :
    (g.reverse.map (Int.castRingHom ℂ)).IsRoot z⁻¹ := by
  let _ := invertibleOfNonzero hz
  rw [IsRoot, eval_map] at hroot ⊢
  simpa only [invOf_eq_inv] using (eval₂_reverse_eq_zero_iff (Int.castRingHom ℂ) z g).2 hroot

/-- **Perron's irreducibility criterion.** Let $f = x^n + a_{n-1} x^{n-1} + \cdots + a_0$ be a
monic polynomial in $\mathbb{Z}[x]$ of degree $n \ge 1$ with $a_0 \neq 0$ and
$|a_{n-1}| > 1 + \sum_{i=0}^{n-2} |a_i|$. Then $f$ is irreducible in $\mathbb{Z}[x]$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 1 (Perron's criterion,
quoted from the paper's reference [6]) (`integers-2026-A92-thm-1`). -/
public theorem perron_irreducible {f : ℤ[X]} (hmonic : f.Monic) (hdeg : 1 ≤ f.natDegree)
    (h0 : f.coeff 0 ≠ 0)
    (hbig : 1 + ∑ i ∈ Finset.range (f.natDegree - 1), |f.coeff i| <
      |f.coeff (f.natDegree - 1)|) :
    Irreducible f := by
  classical
  let k := f.natDegree - 1
  have hk : f.natDegree = k + 1 := by omega
  have hnorm (i : ℕ) : ‖(f.coeff i : ℂ)‖ = (|f.coeff i| : ℤ) := by
    rw [Complex.norm_intCast, Int.cast_abs]
  have hsum : (∑ i ∈ Finset.range k, ‖(f.reverse.coeff (i + 2) : ℂ)‖) =
      ((∑ i ∈ Finset.range k, |f.coeff i| : ℤ) : ℝ) := by
    rw [Int.cast_sum, ← Finset.sum_range_reflect (fun i ↦ ((|f.coeff i| : ℤ) : ℝ)) k]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hil := Finset.mem_range.mp hi
    rw [coeff_reverse, revAt_le (by omega), show f.natDegree - (i + 2) = k - 1 - i by omega, hnorm]
  have hbig' : 2 + ∑ i ∈ Finset.range k, ‖(f.reverse.coeff (i + 2) : ℂ)‖ ≤ ‖(f.coeff k : ℂ)‖ := by
    rw [hsum, hnorm]
    have hbigInt : 2 + ∑ i ∈ Finset.range k, |f.coeff i| ≤ |f.coeff k| := by
      change 1 + ∑ i ∈ Finset.range k, |f.coeff i| < |f.coeff k| at hbig
      omega
    exact_mod_cast hbigInt
  refine (hmonic.irreducible_iff_natDegree).2 ⟨?_, ?_⟩
  · rintro rfl
    simp at hdeg
  intro g h hg hh hmul
  by_contra! hne
  have hconst : g.coeff 0 * h.coeff 0 ≠ 0 := by rwa [← mul_coeff_zero, hmul]
  obtain ⟨z, hz, hzroot⟩ := exists_large_root_of_monic hg hne.1 (left_ne_zero_of_mul hconst)
  obtain ⟨w, hw, hwroot⟩ := exists_large_root_of_monic hh hne.2 (right_ne_zero_of_mul hconst)
  have hinv {t : ℂ} (ht : 1 ≤ ‖t‖) : ‖t⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ ht
  have hne_zero {t : ℂ} (ht : 1 ≤ ‖t‖) : t ≠ 0 := by rintro rfl; norm_num at ht
  apply not_two_reciprocal_roots hbig' (hinv hz) (hinv hw)
  rw [← reverse_map_eq_reciprocalForm hmonic hk, ← hmul, reverse_mul_of_domain, Polynomial.map_mul]
  exact mul_dvd_mul (dvd_iff_isRoot.mpr (inverse_isRoot_reverse (hne_zero hz) hzroot))
    (dvd_iff_isRoot.mpr (inverse_isRoot_reverse (hne_zero hw) hwroot))

end MetaMathlibExt
