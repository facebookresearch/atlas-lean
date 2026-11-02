/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Basic

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Carleman's criterion for the Stieltjes moment problem

This file proves that a probability measure on the nonnegative half-line is determined by its
moments when its Stieltjes Carleman series diverges. It also supplies the real-variable
quasi-analytic uniqueness result used in the proof.
-/

set_option autoImplicit false

@[expose] public section

namespace MetaMathlibExt

open Filter MeasureTheory Set
open scoped BigOperators Topology

private lemma carleman_tsum_nat_add_sq_inv_le (k : ℕ) :
    (k + 1 : ℝ) * ∑' n : ℕ, ((n : ℝ) + k + 1) ^ (-2 : ℝ) ≤ 2 := by
  let f : ℝ → ℝ := fun x => x ^ (-2 : ℝ)
  have hanti : AntitoneOn f (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : (-2 : ℝ) ≤ 0)).mono
      (by intro x hx; exact (show (0 : ℝ) < 1 by norm_num).trans_le hx)
  have hanti' : AntitoneOn f (Ici ((1 : ℕ) : ℝ)) := by simpa using hanti
  have hsumf : Summable (fun n : ℕ => f n) :=
    hanti'.summable_of_integrableOn_Ioi (N := 1)
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))
      (by
        intro t ht
        have ht0 : 0 ≤ t := by
          have ht' : (((1 : ℕ) : ℝ)) < t := Set.mem_Ioi.mp ht
          norm_num at ht'
          linarith
        exact Real.rpow_nonneg ht0 _)
  have hsum : Summable (fun n : ℕ => f (n + k + 1)) := by
    convert (summable_nat_add_iff (f := fun n : ℕ => f n) (k + 1)).2 hsumf using 1
    funext n
    congr 1
    push_cast
    ring
  have htail : ∑' n : ℕ, f ((n : ℝ) + (k + 1) + 1) ≤ ((k + 1 : ℕ) : ℝ)⁻¹ := by
    calc
      ∑' n : ℕ, f ((n : ℝ) + (k + 1) + 1) ≤
          ∫ x : ℝ in Ioi (k + 1 : ℝ), f x := by
        have hantiK : AntitoneOn f (Ici (((k + 1 : ℕ) : ℝ))) :=
          (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
            (by
              intro x hx
              have hx' : (((k + 1 : ℕ) : ℝ)) ≤ x := hx
              exact (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity).trans_le hx')
        have hintK : IntegrableOn f (Ioi (((k + 1 : ℕ) : ℝ))) :=
          integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)
        have hnonnegK : ∀ t ∈ Ioi (((k + 1 : ℕ) : ℝ)), 0 ≤ f t := by
          intro t ht
          have ht' : (((k + 1 : ℕ) : ℝ)) < t := Set.mem_Ioi.mp ht
          exact Real.rpow_nonneg
            (le_of_lt ((show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity).trans ht')) _
        have h := AntitoneOn.tsum_comp_add_le_integral (f := f) (N := k + 1)
          hantiK hintK hnonnegK
        convert h using 1 <;> push_cast <;> ring
      _ = ((k + 1 : ℕ) : ℝ)⁻¹ := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) (by positivity)]
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        norm_num
  change (k + 1 : ℝ) * ∑' n : ℕ, f ((n : ℝ) + k + 1) ≤ 2
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add]
  simp_rw [show ∀ n : ℕ, (n : ℝ) + 1 + k + 1 = (n : ℝ) + (k + 1) + 1 by
    intro n
    ring]
  change (k + 1 : ℝ) *
      (f (k + 1) + ∑' n : ℕ, f ((n : ℝ) + (k + 1) + 1)) ≤ 2
  have hfval : f (k + 1) = (((k + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
    unfold f
    push_cast
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [inv_pow]
  calc
    _ ≤ (k + 1 : ℝ) * (((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 + ((k + 1 : ℕ) : ℝ)⁻¹) := by
      rw [hfval]
      gcongr
    _ ≤ 2 := by
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
      push_cast at *
      field_simp
      nlinarith

private lemma carleman_geometric_mean_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1), a k) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤
      Real.exp 1 * (∑ k ∈ Finset.range (n + 1), (k + 1 : ℝ) * a k) /
        (((n + 1 : ℕ) : ℝ) ^ 2) := by
  let N := n + 1
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hamgm :
      (∏ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * a k) ^ ((N : ℝ)⁻¹) ≤
        (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * a k) / (N : ℝ) := by
    simpa using Real.geom_mean_le_arith_mean (Finset.range N) (fun _ => (1 : ℝ))
      (fun k => ((k + 1 : ℕ) : ℝ) * a k)
      (by intro i hi; positivity) (by simp [Nat.pos_of_ne_zero hN0])
      (by intro i hi; exact mul_nonneg (by positivity) (ha i))
  have hprod :
      (∏ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * a k) =
        (N.factorial : ℝ) * ∏ k ∈ Finset.range N, a k := by
    rw [Finset.prod_mul_distrib]
    congr 1
    norm_cast
    exact Finset.prod_range_add_one_eq_factorial N
  have hsqrt : (1 : ℝ) ≤ √(2 * Real.pi * N) := by
    have hN_one : (1 : ℝ) ≤ N := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
    have harg : (1 : ℝ) ≤ 2 * Real.pi * N := by
      have hpi := Real.pi_gt_three
      nlinarith
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi * N), Real.sqrt_nonneg
      (2 * Real.pi * N)]
  have hfac : ((N : ℝ) / Real.exp 1) ^ N ≤ (N.factorial : ℝ) := by
    refine le_trans ?_ (Stirling.le_factorial_stirling N)
    have hp : 0 ≤ ((N : ℝ) / Real.exp 1) ^ N := by positivity
    nlinarith
  have hroot : (N : ℝ) / Real.exp 1 ≤ (N.factorial : ℝ) ^ ((N : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by positivity) hfac (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ (N : ℝ) / Real.exp 1)
      hN0] at h
    exact h
  rw [hprod, Real.mul_rpow (by positivity) (Finset.prod_nonneg fun i hi => ha i)] at hamgm
  have hgeom : 0 ≤ (∏ k ∈ Finset.range N, a k) ^ ((N : ℝ)⁻¹) :=
    Real.rpow_nonneg (Finset.prod_nonneg fun i hi => ha i) _
  have hmul : (N : ℝ) / Real.exp 1 *
      (∏ k ∈ Finset.range N, a k) ^ ((N : ℝ)⁻¹) ≤
        (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * a k) / (N : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hroot hgeom).trans hamgm
  have hfinal : (∏ k ∈ Finset.range N, a k) ^ ((N : ℝ)⁻¹) ≤
      Real.exp 1 * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * a k) /
        (N : ℝ) ^ 2 := by
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    field_simp at hmul ⊢
    nlinarith
  simpa [N, Nat.cast_add, Nat.cast_one] using hfinal

/-- **Carleman's inequality, summability form.** If $(a_n)_{n \ge 0}$ is a summable sequence of
nonnegative real numbers, then the sequence of geometric means $(a_0 a_1 \cdots a_n)^{1/(n+1)}$,
$n \ge 0$, is summable. -/
public theorem summable_geometric_means {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hasum : Summable a) :
    Summable (fun n =>
      (∏ k ∈ Finset.range (n + 1), a k) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) := by
  have hp0 : Summable (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) := by
    simpa only [Real.rpow_two] using
      (Real.summable_nat_rpow_inv (p := 2)).2 (by norm_num)
  have hp : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) 1).2 hp0
    convert h using 1
    funext n
    push_cast
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  let F : ℕ × ℕ → ℝ := fun p =>
    if p.1 ≤ p.2 then
      Real.exp 1 * (((p.1 + 1 : ℕ) : ℝ) * a p.1) * ((p.2 : ℝ) + 1) ^ (-2 : ℝ)
    else 0
  have hF_nonneg : ∀ p, 0 ≤ F p := by
    intro p
    simp only [F]
    split_ifs
    · exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le
        (mul_nonneg (by positivity) (ha p.1))) (Real.rpow_nonneg (by positivity) _)
    · exact le_rfl
  have hinner : ∀ k : ℕ, Summable (fun n : ℕ => F (k, n)) := by
    intro k
    apply Summable.of_nonneg_of_le (fun n => hF_nonneg (k, n))
      (fun n => ?_) (hp.mul_left (Real.exp 1 * (((k + 1 : ℕ) : ℝ) * a k)))
    by_cases hkn : k ≤ n
    · simp only [F, hkn, ↓reduceIte]
      exact le_rfl
    · simp only [F, hkn, ↓reduceIte]
      exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le
        (mul_nonneg (by positivity) (ha k))) (Real.rpow_nonneg (by positivity) _)
  have hinner_bound : ∀ k : ℕ, ∑' n : ℕ, F (k, n) ≤ 2 * Real.exp 1 * a k := by
    intro k
    have hdecomp := (hinner k).sum_add_tsum_nat_add k
    have hzero : ∑ i ∈ Finset.range k, F (k, i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [F, Nat.not_le_of_lt (Finset.mem_range.mp hi)]
    rw [hzero, zero_add] at hdecomp
    have hshift : ∑' n : ℕ, F (k, n) = ∑' n : ℕ, F (k, n + k) := hdecomp.symm
    rw [hshift]
    have hpinv : Summable (fun n : ℕ => ((n : ℝ) + k + 1) ^ (-2 : ℝ)) := by
      have h := (summable_nat_add_iff
        (f := fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) k).2 hp
      convert h using 1
      funext n
      push_cast
      congr 1
    have hcalc :
        (∑' n : ℕ, F (k, n + k)) =
          (Real.exp 1 * (((k + 1 : ℕ) : ℝ) * a k)) *
            ∑' n : ℕ, ((n : ℝ) + k + 1) ^ (-2 : ℝ) := by
      rw [← hpinv.tsum_mul_left]
      apply tsum_congr
      intro n
      simp [F, Nat.le_add_left k n]
    rw [hcalc]
    push_cast
    calc
      _ = Real.exp 1 * a k *
          ((k + 1 : ℝ) * ∑' n : ℕ, ((n : ℝ) + k + 1) ^ (-2 : ℝ)) := by ring
      _ ≤ Real.exp 1 * a k * 2 := by
        exact mul_le_mul_of_nonneg_left (carleman_tsum_nat_add_sq_inv_le k)
          (mul_nonneg (Real.exp_pos 1).le (ha k))
      _ = 2 * Real.exp 1 * a k := by ring
  have houter : Summable (fun k : ℕ => ∑' n : ℕ, F (k, n)) :=
    Summable.of_nonneg_of_le
      (fun k => tsum_nonneg fun n => hF_nonneg (k, n)) hinner_bound
      (hasum.mul_left (2 * Real.exp 1))
  have hdouble : Summable F :=
    (summable_prod_of_nonneg hF_nonneg).2 ⟨hinner, houter⟩
  have hmajor : Summable (fun n : ℕ => ∑' k : ℕ, F (k, n)) := by
    have h := (summable_prod_of_nonneg (fun p => hF_nonneg p.swap)).1 hdouble.prod_symm
    simpa only [Prod.swap_prod_mk] using h.2
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (Finset.prod_nonneg fun i hi => ha i) _)
    (fun n => ?_) hmajor
  calc
    (∏ k ∈ Finset.range (n + 1), a k) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤
        Real.exp 1 * (∑ k ∈ Finset.range (n + 1), (k + 1 : ℝ) * a k) /
          (((n + 1 : ℕ) : ℝ) ^ 2) := carleman_geometric_mean_le a ha n
    _ = ∑' k : ℕ, F (k, n) := by
      rw [tsum_eq_sum (s := Finset.range (n + 1))]
      · calc
          Real.exp 1 * (∑ k ∈ Finset.range (n + 1), (k + 1 : ℝ) * a k) /
                (((n + 1 : ℕ) : ℝ) ^ 2) =
              ∑ k ∈ Finset.range (n + 1),
                Real.exp 1 * (((k + 1 : ℕ) : ℝ) * a k) *
                  ((n : ℝ) + 1) ^ (-2 : ℝ) := by
            rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            rw [Real.rpow_neg (by positivity), Real.rpow_two]
          _ = ∑ k ∈ Finset.range (n + 1), F (k, n) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            simp only [F, hkn, ↓reduceIte]
      · intro k hk
        have hkn : ¬k ≤ n := fun h => hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
        simp [F, hkn]

private lemma carleman_prod_ratios (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n) (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1), M k / M (k + 1)) = M 0 / M (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp [(hMpos (n + 1)).ne', (hMpos (n + 2)).ne']

private lemma carleman_not_summable_ratios (M m : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hMzero : M 0 = 4) (heven : ∀ n, M (2 * (n + 1)) = 4 * m n)
    (hmpos : ∀ n, 0 < m n)
    (hcarleman : ∑' n : ℕ, ENNReal.rpow (ENNReal.ofReal (m n))
      (-1 / (2 * ((n + 1 : ℕ) : ℝ))) = ⊤) :
    ¬Summable (fun n => M n / M (n + 1)) := by
  intro hsum
  have hgeom := summable_geometric_means
    (a := fun n => M n / M (n + 1))
    (fun n => div_nonneg (hMpos n).le (hMpos (n + 1)).le) hsum
  have hsub := hgeom.comp_injective (i := fun n : ℕ => 2 * n + 1) (by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel hab))
  have hterm (n : ℕ) :
      m n ^ (-1 / (2 * ((n + 1 : ℕ) : ℝ))) =
        ((∏ k ∈ Finset.range (2 * n + 1 + 1), M k / M (k + 1)) ^
          (((2 * n + 1 + 1 : ℕ) : ℝ)⁻¹)) := by
    rw [carleman_prod_ratios M hMpos, show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
      hMzero, heven]
    have hm : 0 ≤ m n := (hmpos n).le
    rw [show (4 : ℝ) / (4 * m n) = 1 / m n by field_simp [(hmpos n).ne'],
      Real.div_rpow (by norm_num) hm, Real.one_rpow]
    have hexp : -1 / (2 * ((n + 1 : ℕ) : ℝ)) =
        -(2 * ((n + 1 : ℕ) : ℝ))⁻¹ := by
      field_simp
    rw [hexp, Real.rpow_neg hm, one_div]
    congr 2
    push_cast
    rfl
  have hreal : Summable (fun n => m n ^ (-1 / (2 * ((n + 1 : ℕ) : ℝ)))) := by
    convert hsub using 1
    funext n
    simpa only [Function.comp_apply] using hterm n
  apply hreal.tsum_ofReal_ne_top
  calc
    (∑' n : ℕ, ENNReal.ofReal (m n ^ (-1 / (2 * ((n + 1 : ℕ) : ℝ))))) =
        ∑' n : ℕ, ENNReal.rpow (ENNReal.ofReal (m n))
          (-1 / (2 * ((n + 1 : ℕ) : ℝ))) := by
      apply tsum_congr
      intro n
      exact (ENNReal.ofReal_rpow_of_pos (hmpos n)).symm
    _ = ⊤ := hcarleman

private lemma carleman_ratio_mono (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2)) :
    Monotone (fun n => M (n + 1) / M n) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [div_le_div_iff₀ (hMpos n) (hMpos (n + 1))]
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hlog n

private lemma carleman_div_le_ratio_pow (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2))
    {j k q : ℕ} (hq : 0 < q) (hjk : j + k ≤ q) :
    M (j + k) / M j ≤ (M q / M (q - 1)) ^ k := by
  have hmono := carleman_ratio_mono M hMpos hlog
  induction k with
  | zero =>
      rw [add_zero, div_self (hMpos j).ne']
      simp
  | succ k ih =>
      have hjklt : j + k < q := by omega
      have hjk' : j + k ≤ q - 1 := Nat.le_sub_one_of_lt hjklt
      have hratio : M (j + k + 1) / M (j + k) ≤ M q / M (q - 1) := by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq.ne')] using hmono hjk'
      have hnonneg : 0 ≤ M q / M (q - 1) :=
        div_nonneg (hMpos _).le (hMpos _).le
      calc
        M (j + (k + 1)) / M j =
            (M (j + k) / M j) * (M (j + k + 1) / M (j + k)) := by
              field_simp [(hMpos j).ne', (hMpos (j + k)).ne']
              ring_nf
        _ ≤ (M q / M (q - 1)) ^ k * (M q / M (q - 1)) :=
          mul_le_mul (ih hjklt.le) hratio
            (div_nonneg (hMpos _).le (hMpos _).le) (pow_nonneg hnonneg _)
        _ = (M q / M (q - 1)) ^ (k + 1) := by rw [pow_succ]

private lemma carleman_iteratedDeriv_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (j k : ℕ) :
    iteratedDeriv k (iteratedDeriv j f) = iteratedDeriv (j + k) f := by
  simp only [iteratedDeriv_eq_iterate]
  rw [← Function.iterate_add_apply, Nat.add_comm]

private lemma carleman_contDiff_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (j : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j f) := by
  simpa only [iteratedDeriv_eq_iterate] using hf.iterate_deriv j

private lemma carleman_affine_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (x y t : ℝ) (k : ℕ) :
    iteratedDeriv k (fun u => g (x + (y - x) * u)) t =
      (y - x) ^ k • iteratedDeriv k g (x + (y - x) * t) := by
  let h : ℝ → E := fun z => g (x + z)
  have hh : ContDiff ℝ k h := by
    dsimp [h]
    have hgk : ContDiff ℝ k g := hg.of_le (by simp)
    simpa only [Function.comp_def, id_eq] using hgk.comp (contDiff_const.add contDiff_id)
  have hs := congrFun (iteratedDeriv_comp_const_smul hh (y - x)) t
  rw [show (fun u => g (x + (y - x) * u)) = (fun u => h ((y - x) * u)) by rfl, hs]
  simp only [h]
  rw [iteratedDeriv_comp_const_add]

private lemma carleman_contDiff_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (x y : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => g (x + (y - x) * t)) := by
  fun_prop

private lemma carleman_taylor_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (g : ℝ → E)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (C : ℝ) (r : ℕ) (hr : 0 < r) (x y : ℝ)
    (hC : ∀ t, ‖iteratedDeriv r g t‖ ≤ C) :
    ‖g y - ∑ k ∈ Finset.range r,
        (((k.factorial : ℝ)⁻¹ * (y - x) ^ k) • iteratedDeriv k g x)‖ ≤
      C * |y - x| ^ r / ((r - 1).factorial : ℝ) := by
  let h : ℝ → E := fun t => g (x + (y - x) * t)
  have hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h := carleman_contDiff_affine g hg x y
  have hr_eq : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hwithin (k : ℕ) :
      iteratedDerivWithin k h (Icc (0 : ℝ) 1) 0 = iteratedDeriv k h 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hh.contDiffAt.of_le (by simp)) (by norm_num)
  have hb := taylor_mean_remainder_bound (f := h) (a := 0) (b := 1)
    (C := C * |y - x| ^ r) (x := 1) (n := r - 1) (by norm_num)
    ((hh.of_le (by simp)).contDiffOn) (by norm_num) (fun z hz => ?_)
  · rw [taylor_within_apply] at hb
    simp_rw [hwithin] at hb
    simp only [h] at hb
    simp_rw [carleman_affine_iteratedDeriv g hg x y 0] at hb
    have hxy : x + (y - x) = y := by ring
    have hx0 : x + (y - x) * 0 = x := by ring
    simpa only [mul_one, hxy, hx0, hr_eq, sub_zero, one_pow, smul_smul] using hb
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
        (hh.contDiffAt.of_le (by simp)) hz]
    rw [hr_eq, carleman_affine_iteratedDeriv g hg x y z r]
    rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_sub_comm]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (hC _) (pow_nonneg (abs_nonneg _) _)

private lemma carleman_exp_sum_bound (z : ℝ) (hz : 0 ≤ z) (r : ℕ) (hr : 0 < r) :
    (∑ k ∈ Finset.range r, z ^ k / (k.factorial : ℝ)) +
        z ^ r / ((r - 1).factorial : ℝ) ≤ Real.exp (2 * z) := by
  have hterm_nonneg (k : ℕ) : 0 ≤ z ^ k / (k.factorial : ℝ) := by positivity
  have hrm : r - 1 < r := Nat.sub_lt hr (by omega)
  have hterm : z ^ (r - 1) / ((r - 1).factorial : ℝ) ≤ Real.exp z := by
    calc
      _ ≤ ∑ k ∈ Finset.range r, z ^ k / (k.factorial : ℝ) := by
        exact Finset.single_le_sum (fun k hk => hterm_nonneg k)
          (Finset.mem_range.mpr hrm)
      _ ≤ Real.exp z := Real.sum_le_exp_of_nonneg hz r
  have htail : z ^ r / ((r - 1).factorial : ℝ) ≤ z * Real.exp z := by
    calc
      _ = z * (z ^ (r - 1) / ((r - 1).factorial : ℝ)) := by
        nth_rewrite 1 [← Nat.sub_add_cancel hr]
        rw [pow_succ]
        ring
      _ ≤ z * Real.exp z := mul_le_mul_of_nonneg_left hterm hz
  calc
    _ ≤ Real.exp z + z * Real.exp z :=
      add_le_add (Real.sum_le_exp_of_nonneg hz r) htail
    _ = (z + 1) * Real.exp z := by ring
    _ ≤ Real.exp z * Real.exp z :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp z) (Real.exp_pos z).le
    _ = Real.exp (2 * z) := by rw [← Real.exp_add]; congr 1; ring

private noncomputable def carlemanNormalizedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ‖iteratedDeriv n f x‖ / ((Real.exp 1) ^ n * M n)

private noncomputable def carlemanBangFunction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (x : ℝ) : ℝ :=
  sSup (Set.range fun n => carlemanNormalizedDeriv f M n x)

private lemma carleman_normalizedDeriv_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (n : ℕ) (x : ℝ) : 0 ≤ carlemanNormalizedDeriv f M n x := by
  exact div_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (Real.exp_pos 1).le _)
    (hMpos n).le)

private lemma carleman_normalizedDeriv_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) (n : ℕ) (x : ℝ) :
    carlemanNormalizedDeriv f M n x ≤ ((Real.exp 1) ^ n)⁻¹ := by
  unfold carlemanNormalizedDeriv
  calc
    _ ≤ M n / ((Real.exp 1) ^ n * M n) := by
      exact div_le_div_of_nonneg_right (hbound n x)
        (mul_nonneg (pow_nonneg (Real.exp_pos 1).le _) (hMpos n).le)
    _ = ((Real.exp 1) ^ n)⁻¹ := by
      field_simp [(hMpos n).ne']

private lemma carleman_normalizedDeriv_bddAbove {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) (x : ℝ) :
    BddAbove (Set.range fun n => carlemanNormalizedDeriv f M n x) := by
  use 1
  rintro _ ⟨n, rfl⟩
  have hpow : (1 : ℝ) ≤ (Real.exp 1) ^ n :=
    one_le_pow₀ (Real.one_le_exp (by norm_num))
  exact (carleman_normalizedDeriv_le f M hMpos hbound n x).trans
    (inv_le_one_of_one_le₀ hpow)

private lemma carleman_normalizedDeriv_le_bang {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) (n : ℕ) (x : ℝ) :
    carlemanNormalizedDeriv f M n x ≤ carlemanBangFunction f M x := by
  exact le_csSup (carleman_normalizedDeriv_bddAbove f M hMpos hbound x) ⟨n, rfl⟩

private lemma carleman_iteratedDeriv_le_bang {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n f x‖ ≤
      carlemanBangFunction f M x * ((Real.exp 1) ^ n * M n) := by
  have hden : 0 < (Real.exp 1) ^ n * M n :=
    mul_pos (pow_pos (Real.exp_pos 1) _) (hMpos n)
  exact (div_le_iff₀ hden).mp
    (carleman_normalizedDeriv_le_bang f M hMpos hbound n x)

private lemma carleman_bang_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) (x : ℝ) :
    0 ≤ carlemanBangFunction f M x :=
  (carleman_normalizedDeriv_nonneg f M hMpos 0 x).trans
    (carleman_normalizedDeriv_le_bang f M hMpos hbound 0 x)

private lemma carleman_taylor_sum_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2))
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) {j q : ℕ} (hjq : j < q)
    (x y : ℝ) :
    ‖∑ k ∈ Finset.range (q - j),
        (((k.factorial : ℝ)⁻¹ * (y - x) ^ k) • iteratedDeriv (j + k) f x)‖ ≤
      carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
        ∑ k ∈ Finset.range (q - j),
          (Real.exp 1 * (M q / M (q - 1)) * |y - x|) ^ k /
            (k.factorial : ℝ) := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hklt : k < q - j := Finset.mem_range.mp hk
  have hjk : j + k ≤ q := by omega
  have hratio := carleman_div_le_ratio_pow M hMpos hlog (by omega : 0 < q) hjk
  have hM : M (j + k) ≤ M j * (M q / M (q - 1)) ^ k :=
    by simpa only [mul_comm] using (div_le_iff₀ (hMpos j)).mp hratio
  have hB : 0 ≤ carlemanBangFunction f M x :=
    carleman_bang_nonneg f M hMpos hbound x
  have hcoef :
      ‖((k.factorial : ℝ)⁻¹ * (y - x) ^ k)‖ =
        (k.factorial : ℝ)⁻¹ * |y - x| ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, Nat.abs_cast]
  rw [norm_smul, hcoef]
  calc
    _ ≤ (k.factorial : ℝ)⁻¹ * |y - x| ^ k *
        (carlemanBangFunction f M x * ((Real.exp 1) ^ (j + k) * M (j + k))) :=
      mul_le_mul_of_nonneg_left
        (carleman_iteratedDeriv_le_bang f M hMpos hbound (j + k) x) (by positivity)
    _ ≤ (k.factorial : ℝ)⁻¹ * |y - x| ^ k *
        (carlemanBangFunction f M x *
          ((Real.exp 1) ^ (j + k) * (M j * (M q / M (q - 1)) ^ k))) := by
      gcongr
    _ = carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
        ((Real.exp 1 * (M q / M (q - 1)) * |y - x|) ^ k /
          (k.factorial : ℝ)) := by
      rw [pow_add, mul_pow, mul_pow]
      ring

private lemma carleman_taylor_remainder_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2))
    {j q : ℕ} (hjq : j < q) (x y : ℝ)
    (hthreshold : ((Real.exp 1) ^ q)⁻¹ ≤ carlemanBangFunction f M x) :
    M q * |y - x| ^ (q - j) / ((q - j - 1).factorial : ℝ) ≤
      carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
        ((Real.exp 1 * (M q / M (q - 1)) * |y - x|) ^ (q - j) /
          ((q - j - 1).factorial : ℝ)) := by
  have hq : 0 < q := by omega
  have hjq' : j + (q - j) ≤ q := by omega
  have hratio := carleman_div_le_ratio_pow M hMpos hlog hq hjq'
  have hM : M q ≤ M j * (M q / M (q - 1)) ^ (q - j) := by
    simpa only [Nat.add_sub_of_le hjq.le, mul_comm] using
      (div_le_iff₀ (hMpos j)).mp hratio
  have heq : j + (q - j) = q := Nat.add_sub_of_le hjq.le
  have hBe : 1 ≤ carlemanBangFunction f M x * (Real.exp 1) ^ q :=
    (inv_le_iff_one_le_mul₀ (pow_pos (Real.exp_pos 1) q)).mp hthreshold
  have hR : 0 ≤ M q / M (q - 1) := div_nonneg (hMpos _).le (hMpos _).le
  have hbase :
      0 ≤ M j * (M q / M (q - 1)) ^ (q - j) * |y - x| ^ (q - j) /
        ((q - j - 1).factorial : ℝ) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (hMpos j).le (pow_nonneg hR _))
        (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)
  have hepow : (Real.exp 1) ^ q = (Real.exp 1) ^ j * (Real.exp 1) ^ (q - j) := by
    conv_lhs => rw [← heq]
    rw [pow_add]
  calc
    _ ≤ (M j * (M q / M (q - 1)) ^ (q - j)) * |y - x| ^ (q - j) /
        ((q - j - 1).factorial : ℝ) := by gcongr
    _ ≤ (carlemanBangFunction f M x * (Real.exp 1) ^ q) *
        (M j * (M q / M (q - 1)) ^ (q - j) * |y - x| ^ (q - j) /
          ((q - j - 1).factorial : ℝ)) := le_mul_of_one_le_left hbase hBe
    _ = carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
        ((Real.exp 1 * (M q / M (q - 1)) * |y - x|) ^ (q - j) /
          ((q - j - 1).factorial : ℝ)) := by
      rw [hepow, mul_pow, mul_pow]
      ring

private lemma carleman_normalizedDeriv_growth {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (M : ℕ → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hMpos : ∀ n, 0 < M n)
    (hlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2))
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) {q : ℕ}
    {x y : ℝ} (hthreshold : ((Real.exp 1) ^ q)⁻¹ ≤ carlemanBangFunction f M x)
    (j : ℕ) :
    carlemanNormalizedDeriv f M j y ≤ carlemanBangFunction f M x *
      Real.exp (2 * Real.exp 1 * (M q / M (q - 1)) * |y - x|) := by
  let z := Real.exp 1 * (M q / M (q - 1)) * |y - x|
  have hR : 0 ≤ M q / M (q - 1) := div_nonneg (hMpos _).le (hMpos _).le
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hB : 0 ≤ carlemanBangFunction f M x :=
    carleman_bang_nonneg f M hMpos hbound x
  by_cases hjq : j < q
  · let r := q - j
    have hr : 0 < r := Nat.sub_pos_of_lt hjq
    let S : E := ∑ k ∈ Finset.range r,
      (((k.factorial : ℝ)⁻¹ * (y - x) ^ k) • iteratedDeriv (j + k) f x)
    have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j f) :=
      carleman_contDiff_iteratedDeriv f hf j
    have hCg (t : ℝ) : ‖iteratedDeriv r (iteratedDeriv j f) t‖ ≤ M q := by
      rw [carleman_iteratedDeriv_iteratedDeriv]
      simpa only [r, Nat.add_sub_of_le hjq.le] using hbound q t
    have hTaylor : ‖iteratedDeriv j f y - S‖ ≤
        M q * |y - x| ^ r / ((r - 1).factorial : ℝ) := by
      simpa only [S, carleman_iteratedDeriv_iteratedDeriv] using
        carleman_taylor_bound (iteratedDeriv j f) hg (M q) r hr x y hCg
    have hSum : ‖S‖ ≤ carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
        ∑ k ∈ Finset.range r, z ^ k / (k.factorial : ℝ) := by
      simpa only [S, r, z] using
        carleman_taylor_sum_bound f M hMpos hlog hbound hjq x y
    have hRem : M q * |y - x| ^ r / ((r - 1).factorial : ℝ) ≤
        carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
          (z ^ r / ((r - 1).factorial : ℝ)) := by
      simpa only [r, z] using
        carleman_taylor_remainder_bound f M hMpos hlog hjq x y hthreshold
    have hcommon : 0 ≤ carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) := by
      exact mul_nonneg hB (mul_nonneg (pow_nonneg (Real.exp_pos 1).le _) (hMpos j).le)
    have hnorm : ‖iteratedDeriv j f y‖ ≤
        carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) * Real.exp (2 * z) := by
      calc
        _ ≤ ‖iteratedDeriv j f y - S‖ + ‖S‖ := by
          nth_rewrite 1 [show iteratedDeriv j f y =
            (iteratedDeriv j f y - S) + S by abel]
          exact norm_add_le _ _
        _ ≤ M q * |y - x| ^ r / ((r - 1).factorial : ℝ) + ‖S‖ :=
          add_le_add hTaylor le_rfl
        _ ≤ carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
              (z ^ r / ((r - 1).factorial : ℝ)) +
            carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
              ∑ k ∈ Finset.range r, z ^ k / (k.factorial : ℝ) :=
          add_le_add hRem hSum
        _ = carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
            ((∑ k ∈ Finset.range r, z ^ k / (k.factorial : ℝ)) +
              z ^ r / ((r - 1).factorial : ℝ)) := by ring
        _ ≤ carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
            Real.exp (2 * z) :=
          mul_le_mul_of_nonneg_left (carleman_exp_sum_bound z hz r hr) hcommon
    unfold carlemanNormalizedDeriv
    apply (div_le_iff₀ (mul_pos (pow_pos (Real.exp_pos 1) _) (hMpos j))).2
    have hz_eq : 2 * z = 2 * Real.exp 1 * (M q / M (q - 1)) * |y - x| := by
      dsimp [z]
      ring
    calc
      _ ≤ carlemanBangFunction f M x * ((Real.exp 1) ^ j * M j) *
          Real.exp (2 * z) := hnorm
      _ = (carlemanBangFunction f M x *
          Real.exp (2 * Real.exp 1 * (M q / M (q - 1)) * |y - x|)) *
            ((Real.exp 1) ^ j * M j) := by rw [hz_eq]; ring
  · have hqj : q ≤ j := Nat.le_of_not_gt hjq
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    calc
      carlemanNormalizedDeriv f M j y ≤ ((Real.exp 1) ^ j)⁻¹ :=
        carleman_normalizedDeriv_le f M hMpos hbound j y
      _ ≤ ((Real.exp 1) ^ q)⁻¹ := inv_pow_anti he hqj
      _ ≤ carlemanBangFunction f M x := hthreshold
      _ ≤ carlemanBangFunction f M x * Real.exp (2 * z) :=
        le_mul_of_one_le_right hB (Real.one_le_exp (mul_nonneg (by norm_num) hz))
      _ = carlemanBangFunction f M x *
          Real.exp (2 * Real.exp 1 * (M q / M (q - 1)) * |y - x|) := by
        congr 2
        dsimp [z]
        ring

private lemma carleman_bang_growth {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (M : ℕ → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hMpos : ∀ n, 0 < M n)
    (hlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2))
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) {q : ℕ} {x y : ℝ}
    (hthreshold : ((Real.exp 1) ^ q)⁻¹ ≤ carlemanBangFunction f M x) :
    carlemanBangFunction f M y ≤ carlemanBangFunction f M x *
      Real.exp (2 * Real.exp 1 * (M q / M (q - 1)) * |y - x|) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact carleman_normalizedDeriv_growth f M hf hMpos hlog hbound hthreshold j

private lemma carleman_continuous_normalizedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (n : ℕ) :
    Continuous (carlemanNormalizedDeriv f M n) := by
  unfold carlemanNormalizedDeriv
  have hc : Continuous (iteratedDeriv n f) := hf.continuous_iteratedDeriv n (by simp)
  fun_prop

private lemma carleman_continuous_bangFunction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (M : ℕ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hMpos : ∀ n, 0 < M n) (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n) :
    Continuous (carlemanBangFunction f M) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (carlemanBangFunction f M) (𝓝 x) (𝓝 (carlemanBangFunction f M x))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hegt : (1 : ℝ) < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr zero_lt_one
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
    ((inv_lt_one₀ (lt_trans zero_lt_one hegt)).2 hegt)
  have hevent : ∀ᶠ y in 𝓝 x, ∀ n ∈ Finset.range N,
      dist (carlemanNormalizedDeriv f M n y) (carlemanNormalizedDeriv f M n x) <
        ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact (Metric.tendsto_nhds.1
      (carleman_continuous_normalizedDeriv f M hf n).continuousAt) (ε / 2) (by positivity)
  filter_upwards [hevent] with y hy
  have hxy : carlemanBangFunction f M y ≤ carlemanBangFunction f M x + ε / 2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    by_cases hn : n < N
    · have hd := hy n (Finset.mem_range.mpr hn)
      rw [Real.dist_eq] at hd
      have hbx := carleman_normalizedDeriv_le_bang f M hMpos hbound n x
      have habs := (abs_lt.mp hd).2
      linarith
    · exact le_of_lt <| calc
        carlemanNormalizedDeriv f M n y ≤ ((Real.exp 1) ^ n)⁻¹ :=
          carleman_normalizedDeriv_le f M hMpos hbound n y
        _ ≤ ((Real.exp 1) ^ N)⁻¹ := inv_pow_anti he (Nat.le_of_not_gt hn)
        _ = ((Real.exp 1)⁻¹) ^ N := by rw [inv_pow]
        _ < ε / 4 := hN
        _ ≤ carlemanBangFunction f M x + ε / 2 := by
          have := carleman_bang_nonneg f M hMpos hbound x
          linarith
  have hyx : carlemanBangFunction f M x ≤ carlemanBangFunction f M y + ε / 2 := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    by_cases hn : n < N
    · have hd := hy n (Finset.mem_range.mpr hn)
      rw [Real.dist_eq] at hd
      have hby := carleman_normalizedDeriv_le_bang f M hMpos hbound n y
      have habs := (abs_lt.mp hd).1
      linarith
    · exact le_of_lt <| calc
        carlemanNormalizedDeriv f M n x ≤ ((Real.exp 1) ^ n)⁻¹ :=
          carleman_normalizedDeriv_le f M hMpos hbound n x
        _ ≤ ((Real.exp 1) ^ N)⁻¹ := inv_pow_anti he (Nat.le_of_not_gt hn)
        _ = ((Real.exp 1)⁻¹) ^ N := by rw [inv_pow]
        _ < ε / 4 := hN
        _ ≤ carlemanBangFunction f M y + ε / 2 := by
          have := carleman_bang_nonneg f M hMpos hbound y
          linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private lemma carleman_level_sequence (B : ℝ → ℝ) (hB : Continuous B) (hB0 : B 0 = 0)
    (x : ℝ) (N : ℕ) (hBx : ((Real.exp 1) ^ N)⁻¹ ≤ B x) :
    ∃ t : ℕ → ℝ, (∀ n, t n ∈ Icc 0 1) ∧
      (∀ n, B (t n * x) = ((Real.exp 1) ^ (N + n))⁻¹) ∧
      ∀ n, t (n + 1) ≤ t n := by
  let State : ℕ → Type := fun n =>
    {t : ℝ // t ∈ Icc 0 1 ∧ B (t * x) = ((Real.exp 1) ^ (N + n))⁻¹}
  have hcont : Continuous (fun t : ℝ => B (t * x)) :=
    hB.comp (continuous_id.mul continuous_const)
  have hstart : Nonempty (State 0) := by
    have htarget : ((Real.exp 1) ^ N)⁻¹ ∈
        Icc ((fun t : ℝ => B (t * x)) 0) ((fun t : ℝ => B (t * x)) 1) := by
      rw [mem_Icc]
      simpa only [zero_mul, hB0, one_mul] using
        show 0 ≤ ((Real.exp 1) ^ N)⁻¹ ∧ ((Real.exp 1) ^ N)⁻¹ ≤ B x from
          ⟨inv_nonneg.mpr (pow_nonneg (Real.exp_pos 1).le _), hBx⟩
    rcases intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont.continuousOn
        htarget with ⟨t, ht, heq⟩
    exact ⟨⟨t, ht, by simpa using heq⟩⟩
  have hnext (n : ℕ) (s : State n) :
      Nonempty {u : State (n + 1) // (u : ℝ) ≤ (s : ℝ)} := by
    have hs0 : (0 : ℝ) ≤ s := s.property.1.1
    have hlevel : ((Real.exp 1) ^ (N + (n + 1)))⁻¹ ≤
        ((Real.exp 1) ^ (N + n))⁻¹ := by
      exact inv_pow_anti (Real.one_le_exp (by norm_num)) (by omega)
    have htarget : ((Real.exp 1) ^ (N + (n + 1)))⁻¹ ∈
        Icc ((fun t : ℝ => B (t * x)) 0) ((fun t : ℝ => B (t * x)) s) := by
      rw [mem_Icc]
      simpa only [zero_mul, hB0, s.property.2] using
        show 0 ≤ ((Real.exp 1) ^ (N + (n + 1)))⁻¹ ∧
            ((Real.exp 1) ^ (N + (n + 1)))⁻¹ ≤
              ((Real.exp 1) ^ (N + n))⁻¹ from
          ⟨inv_nonneg.mpr (pow_nonneg (Real.exp_pos 1).le _), hlevel⟩
    rcases intermediate_value_Icc hs0 hcont.continuousOn htarget with ⟨u, hu, heq⟩
    refine ⟨⟨⟨u, ⟨⟨hu.1, hu.2.trans s.property.1.2⟩, ?_⟩⟩, hu.2⟩⟩
    simpa using heq
  let s0 : State 0 := Classical.choice hstart
  let next (n : ℕ) (s : State n) : {u : State (n + 1) // (u : ℝ) ≤ (s : ℝ)} :=
    Classical.choice (hnext n s)
  let s : ∀ n, State n := fun n => Nat.rec s0 (fun n sn => (next n sn).val) n
  let t : ℕ → ℝ := fun n => (s n).val
  refine ⟨t, ?_, ?_, ?_⟩
  · intro n
    exact (s n).property.1
  · intro n
    exact (s n).property.2
  intro n
  simpa only [t, s, Nat.rec_add_one] using (next n (s n)).property

/-- A Denjoy--Carleman uniqueness theorem for globally bounded iterated derivatives. -/
private theorem carleman_eq_zero_of_iteratedDeriv_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (M : ℕ → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hMpos : ∀ n, 0 < M n)
    (hlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2))
    (hbound : ∀ n x, ‖iteratedDeriv n f x‖ ≤ M n)
    (hdiv : ¬Summable (fun n => M n / M (n + 1)))
    (hflat : ∀ n, iteratedDeriv n f 0 = 0) : f = 0 := by
  have hBcont := carleman_continuous_bangFunction f M hf hMpos hbound
  have hB0 : carlemanBangFunction f M 0 = 0 := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n, rfl⟩
      unfold carlemanNormalizedDeriv
      simp only [hflat n, norm_zero, zero_div]
      norm_num
    · exact carleman_bang_nonneg f M hMpos hbound 0
  have hBzero (x : ℝ) : carlemanBangFunction f M x = 0 := by
    apply le_antisymm
    · by_contra hnot
      have hBxpos : 0 < carlemanBangFunction f M x := lt_of_not_ge hnot
      have hegt : (1 : ℝ) < Real.exp 1 := by
        simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr zero_lt_one
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hBxpos
        ((inv_lt_one₀ (lt_trans zero_lt_one hegt)).2 hegt)
      have hlevel : ((Real.exp 1) ^ N)⁻¹ ≤ carlemanBangFunction f M x := by
        simpa only [inv_pow] using hN.le
      obtain ⟨t, ht, hlevels, htmono⟩ :=
        carleman_level_sequence (carlemanBangFunction f M) hBcont hB0 x N hlevel
      have hratio_dist (n : ℕ) :
          M (N + n) / M (N + n + 1) ≤
            2 * Real.exp 1 * |t n * x - t (n + 1) * x| := by
        let q := N + n + 1
        have hqpred : q - 1 = N + n := by omega
        have hqnext : q = N + (n + 1) := by omega
        have hthreshold : ((Real.exp 1) ^ q)⁻¹ ≤
            carlemanBangFunction f M (t (n + 1) * x) := by
          rw [hlevels (n + 1), hqnext]
        have hgrowth := carleman_bang_growth f M hf hMpos hlog hbound hthreshold
          (y := t n * x)
        rw [hlevels n, hlevels (n + 1)] at hgrowth
        have hlevel_ratio : ((Real.exp 1) ^ (N + n))⁻¹ =
            Real.exp 1 * ((Real.exp 1) ^ (N + (n + 1)))⁻¹ := by
          rw [show N + (n + 1) = N + n + 1 by omega, pow_succ]
          field_simp [(Real.exp_pos 1).ne', (pow_pos (Real.exp_pos 1) (N + n)).ne']
        rw [hlevel_ratio] at hgrowth
        have hlevel_pos : 0 < ((Real.exp 1) ^ (N + (n + 1)))⁻¹ :=
          inv_pos.mpr (pow_pos (Real.exp_pos 1) _)
        have hexp : Real.exp 1 ≤ Real.exp
            (2 * Real.exp 1 * (M q / M (q - 1)) *
              |t n * x - t (n + 1) * x|) := by
          apply le_of_mul_le_mul_left _ hlevel_pos
          simpa only [mul_comm, mul_left_comm, mul_assoc] using hgrowth
        have harg : 1 ≤ 2 * Real.exp 1 * (M q / M (q - 1)) *
            |t n * x - t (n + 1) * x| := Real.exp_le_exp.mp hexp
        have harg' : 1 ≤
            (2 * Real.exp 1 * |t n * x - t (n + 1) * x| * M q) / M (q - 1) := by
          calc
            _ ≤ 2 * Real.exp 1 * (M q / M (q - 1)) *
                |t n * x - t (n + 1) * x| := harg
            _ = _ := by ring
        have hprev : M (q - 1) ≤
            2 * Real.exp 1 * |t n * x - t (n + 1) * x| * M q :=
          by simpa only [one_mul] using (le_div_iff₀ (hMpos (q - 1))).mp harg'
        have hratio : M (q - 1) / M q ≤
            2 * Real.exp 1 * |t n * x - t (n + 1) * x| := by
          apply (div_le_iff₀ (hMpos q)).2
          simpa only [mul_assoc] using hprev
        simpa only [hqpred, q] using hratio
      have hdist (n : ℕ) :
          |t n * x - t (n + 1) * x| = (t n - t (n + 1)) * |x| := by
        rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (htmono n))]
      have hsumdist (k : ℕ) :
          ∑ n ∈ Finset.range k, |t n * x - t (n + 1) * x| ≤ |x| := by
        calc
          _ = ∑ n ∈ Finset.range k, (t n - t (n + 1)) * |x| := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hdist n
          _ = (t 0 - t k) * |x| := by
            rw [← Finset.sum_mul, Finset.sum_range_sub']
          _ ≤ 1 * |x| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
            have ht0 := (ht 0).2
            have htk := (ht k).1
            linarith
          _ = |x| := one_mul _
      have htail : Summable (fun n => M (N + n) / M (N + n + 1)) := by
        apply summable_of_sum_range_le
        · intro n
          exact div_nonneg (hMpos _).le (hMpos _).le
        · intro k
          calc
            ∑ n ∈ Finset.range k, M (N + n) / M (N + n + 1) ≤
                ∑ n ∈ Finset.range k,
                  2 * Real.exp 1 * |t n * x - t (n + 1) * x| :=
              Finset.sum_le_sum fun n hn => hratio_dist n
            _ = 2 * Real.exp 1 *
                ∑ n ∈ Finset.range k, |t n * x - t (n + 1) * x| := by
              rw [Finset.mul_sum]
            _ ≤ 2 * Real.exp 1 * |x| :=
              mul_le_mul_of_nonneg_left (hsumdist k) (by positivity)
      have htail' : Summable (fun n => M (n + N) / M (n + N + 1)) := by
        simpa only [Nat.add_comm] using htail
      exact hdiv ((summable_nat_add_iff N).mp htail')
    · exact carleman_bang_nonneg f M hMpos hbound x
  funext x
  have hx := carleman_iteratedDeriv_le_bang f M hMpos hbound 0 x
  rw [hBzero x, zero_mul] at hx
  simpa only [iteratedDeriv_zero, Pi.zero_apply, norm_eq_zero] using
    le_antisymm hx (norm_nonneg (f x))

private lemma carleman_ae_nonneg {σ : Measure ℝ} (hs : σ (Iio 0) = 0) :
    ∀ᵐ x ∂σ, 0 ≤ x := by
  rw [ae_iff]
  rw [show {x : ℝ | ¬0 ≤ x} = Iio 0 by ext x; simp]
  exact hs

private lemma carleman_moment_eq_integral_abs_pow {σ : Measure ℝ}
    (hs : σ (Iio 0) = 0) (k : ℕ) :
    ProbabilityTheory.moment id k σ = ∫ x, |x| ^ k ∂σ := by
  unfold ProbabilityTheory.moment
  apply integral_congr_ae
  filter_upwards [carleman_ae_nonneg hs] with x hx
  simp only [Pi.pow_apply, id_eq, abs_of_nonneg hx]

private lemma carleman_eq_dirac_zero_of_moment_eq_zero
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (hs : σ (Iio 0) = 0)
    (k : ℕ) (hint : Integrable (fun x : ℝ => |x| ^ k) σ)
    (hm : ProbabilityTheory.moment id k σ = 0) : σ = Measure.dirac 0 := by
  have hint_zero : (fun x : ℝ => |x| ^ k) =ᵐ[σ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => pow_nonneg (abs_nonneg x) _) hint).mp (by
      rw [← carleman_moment_eq_integral_abs_pow hs k]
      exact hm)
  have hae : id =ᵐ[σ] fun _ : ℝ => 0 := by
    filter_upwards [hint_zero] with x hx
    simp only [Pi.zero_apply] at hx
    have habs : |x| = 0 := by
      by_contra hne
      have hpow : 0 < |x| ^ k := pow_pos (lt_of_le_of_ne (abs_nonneg x) (Ne.symm hne)) k
      rw [hx] at hpow
      exact lt_irrefl 0 hpow
    simpa only [id_eq, abs_eq_zero] using habs
  calc
    σ = σ.map id := Measure.map_id.symm
    _ = σ.map (fun _ : ℝ => 0) := Measure.map_congr hae
    _ = Measure.dirac 0 := by simp [Measure.map_const]

private lemma carleman_memLp_id_nat {σ : Measure ℝ} [IsFiniteMeasure σ] (n : ℕ)
    (h : Integrable (fun x : ℝ => |x| ^ n) σ) : MemLp id n σ := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using
      (memLp_zero_iff_aestronglyMeasurable.mpr (by fun_prop : AEStronglyMeasurable id σ))
  apply (integrable_norm_rpow_iff (f := id) (by fun_prop) (by exact_mod_cast hn) (by simp)).mp
  simpa only [id_eq, Real.norm_eq_abs, ENNReal.toReal_natCast, Real.rpow_natCast] using h

private lemma carleman_memLp_sqrt_map (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hs : σ (Iio 0) = 0)
    (hint : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ) (n : ℕ) :
    MemLp id n (σ.map Real.sqrt) := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using (memLp_zero_iff_aestronglyMeasurable.mpr
      (by fun_prop : AEStronglyMeasurable id (σ.map Real.sqrt)))
  rw [memLp_map_measure_iff (by fun_prop) Real.continuous_sqrt.measurable.aemeasurable]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hintn := hint n hnpos
  have hsqrt_int : Integrable (fun x : ℝ => ‖Real.sqrt x‖ ^ (2 * n)) σ := by
    apply hintn.congr
    filter_upwards [carleman_ae_nonneg hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x), pow_mul,
      Real.sq_sqrt hx, abs_of_nonneg hx]
  have hsqrt2 : MemLp Real.sqrt (2 * n : ℕ) σ := by
    apply (integrable_norm_rpow_iff (f := Real.sqrt) (by fun_prop)
      (by exact_mod_cast (by omega : 2 * n ≠ 0)) (by finiteness)).mp
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using hsqrt_int
  simpa only [Function.id_comp] using hsqrt2.mono_exponent
    (by exact_mod_cast (by omega : n ≤ 2 * n))

private lemma carleman_memLp_neg_sqrt_map (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hs : σ (Iio 0) = 0)
    (hint : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ) (n : ℕ) :
    MemLp id n (σ.map fun x => -Real.sqrt x) := by
  have hsmap := carleman_memLp_sqrt_map σ hs hint n
  have hsqrt : MemLp (id ∘ Real.sqrt) n σ :=
    (memLp_map_measure_iff (by fun_prop) Real.continuous_sqrt.measurable.aemeasurable).mp hsmap
  rw [memLp_map_measure_iff (f := fun x : ℝ => -Real.sqrt x) (g := id) (by fun_prop)
    (Real.continuous_sqrt.neg.measurable.aemeasurable)]
  apply hsqrt.neg.ae_eq
  filter_upwards with x
  rfl

private noncomputable def carlemanSymmetrization (σ : Measure ℝ) : Measure ℝ :=
  σ.map Real.sqrt + σ.map fun x => -Real.sqrt x

private lemma carleman_map_sq_symmetrization (σ : Measure ℝ) (hs : σ (Iio 0) = 0) :
    (carlemanSymmetrization σ).map (fun x : ℝ => x ^ 2) = σ + σ := by
  unfold carlemanSymmetrization
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hpos : (fun x : ℝ => x ^ 2) ∘ Real.sqrt =ᵐ[σ] id := by
    filter_upwards [carleman_ae_nonneg hs] with x hx
    simp only [Function.comp_apply, id_eq, Real.sq_sqrt hx]
  have hneg : (fun x : ℝ => x ^ 2) ∘ (fun x => -Real.sqrt x) =ᵐ[σ] id := by
    filter_upwards [carleman_ae_nonneg hs] with x hx
    simp only [Function.comp_apply, id_eq]
    rw [show (-Real.sqrt x) ^ 2 = (Real.sqrt x) ^ 2 by ring, Real.sq_sqrt hx]
  rw [Measure.map_congr hpos, Measure.map_congr hneg, Measure.map_id]

private lemma carleman_add_self_injective {σ τ : Measure ℝ} (h : σ + σ = τ + τ) : σ = τ := by
  ext s hs
  have heq : σ s + σ s = τ s + τ s := by
    simpa only [Measure.add_apply] using congrArg (fun ρ : Measure ℝ => ρ s) h
  apply le_antisymm
  · apply le_of_not_gt
    intro hlt
    have := ENNReal.add_lt_add hlt hlt
    rw [← heq] at this
    exact (lt_irrefl _ this)
  · apply le_of_not_gt
    intro hlt
    have := ENNReal.add_lt_add hlt hlt
    rw [heq] at this
    exact (lt_irrefl _ this)

private lemma carleman_memLp_symmetrization (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hs : σ (Iio 0) = 0)
    (hint : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ) (n : ℕ) :
    MemLp id n (carlemanSymmetrization σ) := by
  let _ : IsFiniteMeasure (carlemanSymmetrization σ) := by
    unfold carlemanSymmetrization
    infer_instance
  have hp := (carleman_memLp_sqrt_map σ hs hint n).integrable_norm_pow'
  have hn := (carleman_memLp_neg_sqrt_map σ hs hint n).integrable_norm_pow'
  apply carleman_memLp_id_nat n
  exact hp.add_measure hn

private lemma carleman_integrable_abs_pow_symmetrization
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (hs : σ (Iio 0) = 0)
    (hint : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (carlemanSymmetrization σ) := by
  let _ : IsFiniteMeasure (carlemanSymmetrization σ) := by
    unfold carlemanSymmetrization
    infer_instance
  simpa only [id_eq, Real.norm_eq_abs] using
    (carleman_memLp_symmetrization σ hs hint n).integrable_norm_pow'

private lemma carleman_integrable_pow_of_memLp {ρ : Measure ℝ} [IsFiniteMeasure ρ] (n : ℕ)
    (h : MemLp id n ρ) : Integrable (fun x : ℝ => x ^ n) ρ := by
  apply h.integrable_norm_pow'.congr' (by fun_prop)
  filter_upwards with x
  simp only [id_eq, Real.norm_eq_abs, norm_pow, abs_abs]

private lemma carleman_integral_pow_symmetrization_even
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (hs : σ (Iio 0) = 0)
    (hint : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ) (k : ℕ) :
    ∫ y, y ^ (2 * k) ∂carlemanSymmetrization σ =
      2 * ProbabilityTheory.moment id k σ := by
  unfold carlemanSymmetrization
  rw [integral_add_measure
    (carleman_integrable_pow_of_memLp _ (carleman_memLp_sqrt_map σ hs hint (2 * k)))
    (carleman_integrable_pow_of_memLp _ (carleman_memLp_neg_sqrt_map σ hs hint (2 * k)))]
  rw [integral_map Real.continuous_sqrt.measurable.aemeasurable (by fun_prop)]
  rw [integral_map (φ := fun x : ℝ => -Real.sqrt x)
    (Real.continuous_sqrt.neg.measurable.aemeasurable) (by fun_prop)]
  have hp : (fun x : ℝ => (Real.sqrt x) ^ (2 * k)) =ᵐ[σ] fun x => x ^ k := by
    filter_upwards [carleman_ae_nonneg hs] with x hx
    rw [pow_mul, Real.sq_sqrt hx]
  have hn : (fun x : ℝ => (-Real.sqrt x) ^ (2 * k)) =ᵐ[σ] fun x => x ^ k := by
    filter_upwards [carleman_ae_nonneg hs] with x hx
    rw [pow_mul, show (-Real.sqrt x) ^ 2 = (Real.sqrt x) ^ 2 by ring, Real.sq_sqrt hx]
  rw [integral_congr_ae hp, integral_congr_ae hn]
  unfold ProbabilityTheory.moment
  simp only [Pi.pow_apply, id_eq]
  ring

private lemma carleman_integral_pow_symmetrization_odd
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (hs : σ (Iio 0) = 0)
    (hint : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ) (k : ℕ) :
    ∫ y, y ^ (2 * k + 1) ∂carlemanSymmetrization σ = 0 := by
  unfold carlemanSymmetrization
  rw [integral_add_measure
    (carleman_integrable_pow_of_memLp _ (carleman_memLp_sqrt_map σ hs hint (2 * k + 1)))
    (carleman_integrable_pow_of_memLp _
      (carleman_memLp_neg_sqrt_map σ hs hint (2 * k + 1)))]
  rw [integral_map Real.continuous_sqrt.measurable.aemeasurable (by fun_prop)]
  rw [integral_map (φ := fun x : ℝ => -Real.sqrt x)
    (Real.continuous_sqrt.neg.measurable.aemeasurable) (by fun_prop)]
  have hneg : (fun x : ℝ => (-Real.sqrt x) ^ (2 * k + 1)) =
      -(fun x : ℝ => (Real.sqrt x) ^ (2 * k + 1)) := by
    funext x
    exact (show Odd (2 * k + 1) from ⟨k, by omega⟩).neg_pow _
  rw [hneg, integral_neg']
  ring

private lemma carleman_integral_abs_pow_symmetrization_even
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (hs : σ (Iio 0) = 0)
    (hint : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ) (k : ℕ) :
    ∫ y, |y| ^ (2 * k) ∂carlemanSymmetrization σ =
      2 * ProbabilityTheory.moment id k σ := by
  rw [show (∫ y, |y| ^ (2 * k) ∂carlemanSymmetrization σ) =
      ∫ y, y ^ (2 * k) ∂carlemanSymmetrization σ by
    apply integral_congr_ae
    filter_upwards with y
    rw [← abs_pow]
    exact abs_of_nonneg ((show Even (2 * k) from ⟨k, by omega⟩).pow_nonneg y)]
  exact carleman_integral_pow_symmetrization_even σ hs hint k

private lemma carleman_integral_abs_pow_add_symmetrizations
    (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hs : σ (Iio 0) = 0) (ht : τ (Iio 0) = 0)
    (his : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ)
    (hit : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) τ)
    (hm : ∀ k : ℕ, 0 < k → ProbabilityTheory.moment id k τ =
      ProbabilityTheory.moment id k σ) (k : ℕ) :
    ∫ x, |x| ^ (2 * k) ∂(carlemanSymmetrization σ + carlemanSymmetrization τ) =
      4 * ProbabilityTheory.moment id k σ := by
  rw [integral_add_measure (carleman_integrable_abs_pow_symmetrization σ hs his (2 * k))
    (carleman_integrable_abs_pow_symmetrization τ ht hit (2 * k)),
    carleman_integral_abs_pow_symmetrization_even σ hs his,
    carleman_integral_abs_pow_symmetrization_even τ ht hit]
  by_cases hk : k = 0
  · subst k
    simp [ProbabilityTheory.moment]
    norm_num
  · rw [hm k (Nat.pos_of_ne_zero hk)]
    ring

private lemma carleman_integral_pow_symmetrization_eq (σ τ : Measure ℝ)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hs : σ (Iio 0) = 0) (ht : τ (Iio 0) = 0)
    (his : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ)
    (hit : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) τ)
    (hm : ∀ k : ℕ, 0 < k → ProbabilityTheory.moment id k σ =
      ProbabilityTheory.moment id k τ) (n : ℕ) :
    ∫ x, x ^ n ∂carlemanSymmetrization σ =
      ∫ x, x ^ n ∂carlemanSymmetrization τ := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := hn
    rw [show k + k = 2 * k by omega, carleman_integral_pow_symmetrization_even σ hs his,
      carleman_integral_pow_symmetrization_even τ ht hit]
    by_cases hk : k = 0
    · subst k
      simp [ProbabilityTheory.moment]
    · rw [hm k (Nat.pos_of_ne_zero hk)]
  · obtain ⟨k, rfl⟩ := hn
    rw [carleman_integral_pow_symmetrization_odd σ hs his,
      carleman_integral_pow_symmetrization_odd τ ht hit]

private lemma carleman_norm_iteratedDeriv_charFun_le {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (n : ℕ) (h : MemLp id n ρ) (t : ℝ) :
    ‖iteratedDeriv n (charFun ρ) t‖ ≤ ∫ x, |x| ^ n ∂ρ := by
  rw [iteratedDeriv_charFun h, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with x
  simp [norm_pow, Complex.norm_exp, Real.norm_eq_abs, Complex.mul_re]

private lemma carleman_integral_abs_pow_cauchy {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) ρ) (a b : ℕ) :
    (∫ x, |x| ^ (a + b) ∂ρ) ^ 2 ≤
      (∫ x, |x| ^ (2 * a) ∂ρ) * ∫ x, |x| ^ (2 * b) ∂ρ := by
  let f : ℝ → ℝ := fun x => |x| ^ a
  let g : ℝ → ℝ := fun x => |x| ^ b
  have hf : MemLp f 2 ρ := (memLp_two_iff_integrable_sq (by fun_prop)).2 (by
    simpa only [f, ← pow_mul, show a * 2 = 2 * a by omega] using hint (2 * a))
  have hg : MemLp g 2 ρ := (memLp_two_iff_integrable_sq (by fun_prop)).2 (by
    simpa only [g, ← pow_mul, show b * 2 = 2 * b by omega] using hint (2 * b))
  have h := integral_mul_norm_le_Lp_mul_Lq
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
      (by simpa using hf) (by simpa using hg)
  have h' : (∫ x, |x| ^ (a + b) ∂ρ) ≤
      Real.sqrt (∫ x, |x| ^ (2 * a) ∂ρ) *
        Real.sqrt (∫ x, |x| ^ (2 * b) ∂ρ) := by
    simpa [f, g, Real.rpow_two, ← pow_mul, Real.sqrt_eq_rpow, ← pow_add,
      Nat.mul_comm] using h
  have hleft : 0 ≤ ∫ x, |x| ^ (a + b) ∂ρ :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have ha0 : 0 ≤ ∫ x, |x| ^ (2 * a) ∂ρ :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hb0 : 0 ≤ ∫ x, |x| ^ (2 * b) ∂ρ :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hsprod : 0 ≤ Real.sqrt (∫ x, |x| ^ (2 * a) ∂ρ) *
      Real.sqrt (∫ x, |x| ^ (2 * b) ∂ρ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ (Real.sqrt (∫ x, |x| ^ (2 * a) ∂ρ) *
        Real.sqrt (∫ x, |x| ^ (2 * b) ∂ρ)) ^ 2 :=
      (sq_le_sq₀ hleft hsprod).2 h'
    _ = _ := by rw [mul_pow, Real.sq_sqrt ha0, Real.sq_sqrt hb0]

private noncomputable def carlemanMomentMajorant (ρ : Measure ℝ) (n : ℕ) : ℝ :=
  if Even n then ∫ x, |x| ^ n ∂ρ else
    Real.sqrt ((∫ x, |x| ^ (n - 1) ∂ρ) * ∫ x, |x| ^ (n + 1) ∂ρ)

private lemma carleman_momentMajorant_even {ρ : Measure ℝ} {n : ℕ} (hn : Even n) :
    carlemanMomentMajorant ρ n = ∫ x, |x| ^ n ∂ρ := by
  simp [carlemanMomentMajorant, hn]

private lemma carleman_momentMajorant_odd {ρ : Measure ℝ} {n : ℕ} (hn : Odd n) :
    carlemanMomentMajorant ρ n = Real.sqrt
      ((∫ x, |x| ^ (n - 1) ∂ρ) * ∫ x, |x| ^ (n + 1) ∂ρ) := by
  simp [carlemanMomentMajorant, Nat.not_even_iff_odd.mpr hn]

private lemma carleman_momentMajorant_logconvex {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) ρ) :
    ∀ n, carlemanMomentMajorant ρ (n + 1) ^ 2 ≤
      carlemanMomentMajorant ρ n * carlemanMomentMajorant ρ (n + 2) := by
  intro n
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := hn
    have hodd : Odd (k + k + 1) := ⟨k, by omega⟩
    have heven0 : Even (k + k) := ⟨k, rfl⟩
    have heven2 : Even (k + k + 2) := heven0.add even_two
    rw [carleman_momentMajorant_odd hodd, carleman_momentMajorant_even heven0,
      carleman_momentMajorant_even heven2]
    have h0 : 0 ≤ ∫ x, |x| ^ (k + k) ∂ρ :=
      integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
    have h2 : 0 ≤ ∫ x, |x| ^ (k + k + 2) ∂ρ :=
      integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
    rw [show k + k + 1 - 1 = k + k by omega,
      show k + k + 1 + 1 = k + k + 2 by omega]
    rw [Real.sq_sqrt (mul_nonneg h0 h2)]
  · obtain ⟨k, rfl⟩ := hn
    have hodd0 : Odd (2 * k + 1) := ⟨k, rfl⟩
    have heven1 : Even (2 * k + 1 + 1) := hodd0.add_one
    have hodd2 : Odd (2 * k + 1 + 2) := hodd0.add_even even_two
    rw [carleman_momentMajorant_even heven1, carleman_momentMajorant_odd hodd0,
      carleman_momentMajorant_odd hodd2]
    have hA : 0 ≤ ∫ x, |x| ^ (2 * k) ∂ρ :=
      integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
    have hB : 0 ≤ ∫ x, |x| ^ (2 * k + 2) ∂ρ :=
      integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
    have hC : 0 ≤ ∫ x, |x| ^ (2 * k + 4) ∂ρ :=
      integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
    have hcs := carleman_integral_abs_pow_cauchy hint k (k + 2)
    have hcs' : (∫ x, |x| ^ (2 * k + 2) ∂ρ) ^ 2 ≤
        (∫ x, |x| ^ (2 * k) ∂ρ) * ∫ x, |x| ^ (2 * k + 4) ∂ρ := by
      simpa only [show k + (k + 2) = 2 * k + 2 by omega,
        show 2 * (k + 2) = 2 * k + 4 by omega] using hcs
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega,
      show 2 * k + 1 - 1 = 2 * k by omega,
      show 2 * k + 1 + 2 - 1 = 2 * k + 2 by omega,
      show 2 * k + 1 + 2 + 1 = 2 * k + 4 by omega]
    have hBsqrt : (∫ x, |x| ^ (2 * k + 2) ∂ρ) ≤
        Real.sqrt ((∫ x, |x| ^ (2 * k) ∂ρ) *
          ∫ x, |x| ^ (2 * k + 4) ∂ρ) :=
      (Real.le_sqrt hB (mul_nonneg hA hC)).2 hcs'
    calc
      _ = (∫ x, |x| ^ (2 * k + 2) ∂ρ) *
          ∫ x, |x| ^ (2 * k + 2) ∂ρ := pow_two _
      _ ≤ (∫ x, |x| ^ (2 * k + 2) ∂ρ) *
          Real.sqrt ((∫ x, |x| ^ (2 * k) ∂ρ) *
            ∫ x, |x| ^ (2 * k + 4) ∂ρ) :=
        mul_le_mul_of_nonneg_left hBsqrt hB
      _ = _ := by
        rw [Real.sqrt_mul hA, Real.sqrt_mul hA, Real.sqrt_mul hB]
        calc
          _ = Real.sqrt (∫ x, |x| ^ (2 * k) ∂ρ) *
              ((∫ x, |x| ^ (2 * k + 2) ∂ρ) *
                Real.sqrt (∫ x, |x| ^ (2 * k + 4) ∂ρ)) := by ring
          _ = Real.sqrt (∫ x, |x| ^ (2 * k) ∂ρ) *
              (Real.sqrt (∫ x, |x| ^ (2 * k + 2) ∂ρ) ^ 2 *
                Real.sqrt (∫ x, |x| ^ (2 * k + 4) ∂ρ)) := by
            rw [Real.sq_sqrt hB]
          _ = _ := by ring

private lemma carleman_integral_abs_pow_le_momentMajorant
    {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) ρ) (n : ℕ) :
    (∫ x, |x| ^ n ∂ρ) ≤ carlemanMomentMajorant ρ n := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [carleman_momentMajorant_even hn]
  · obtain ⟨k, rfl⟩ := hn
    rw [carleman_momentMajorant_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩),
      show 2 * k + 1 - 1 = 2 * k by omega,
      show 2 * k + 1 + 1 = 2 * k + 2 by omega]
    apply (Real.le_sqrt (integral_nonneg fun x => pow_nonneg (abs_nonneg x) _)
      (mul_nonneg (integral_nonneg fun x => pow_nonneg (abs_nonneg x) _)
        (integral_nonneg fun x => pow_nonneg (abs_nonneg x) _))).2
    simpa only [show k + (k + 1) = 2 * k + 1 by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega] using
        carleman_integral_abs_pow_cauchy hint k (k + 1)

private theorem carleman_measure_eq
    (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hs : σ (Iio 0) = 0) (ht : τ (Iio 0) = 0)
    (his : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) σ)
    (hit : ∀ k : ℕ, 0 < k → Integrable (fun x : ℝ => |x| ^ k) τ)
    (hm : ∀ k : ℕ, 0 < k → ProbabilityTheory.moment id k τ =
      ProbabilityTheory.moment id k σ)
    (hcarleman : ∑' n : ℕ, ENNReal.rpow
      (ENNReal.ofReal (ProbabilityTheory.moment id (n + 1) σ))
      (-1 / (2 * ((n + 1 : ℕ) : ℝ))) = ⊤) : τ = σ := by
  by_cases hzero : ∃ k : ℕ, 0 < k ∧ ProbabilityTheory.moment id k σ = 0
  · obtain ⟨k, hk, hmk⟩ := hzero
    have hs0 := carleman_eq_dirac_zero_of_moment_eq_zero σ hs k (his k hk) hmk
    have ht0 := carleman_eq_dirac_zero_of_moment_eq_zero τ ht k (hit k hk)
      ((hm k hk).trans hmk)
    exact ht0.trans hs0.symm
  have hmpos (k : ℕ) (hk : 0 < k) : 0 < ProbabilityTheory.moment id k σ := by
    apply lt_of_le_of_ne
    · rw [carleman_moment_eq_integral_abs_pow hs k]
      exact integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
    · exact Ne.symm fun heq => hzero ⟨k, hk, heq⟩
  let ρ : Measure ℝ := carlemanSymmetrization σ
  let υ : Measure ℝ := carlemanSymmetrization τ
  let ξ : Measure ℝ := ρ + υ
  let _ : IsFiniteMeasure ρ := by
    dsimp only [ρ, carlemanSymmetrization]
    infer_instance
  let _ : IsFiniteMeasure υ := by
    dsimp only [υ, carlemanSymmetrization]
    infer_instance
  let _ : IsFiniteMeasure ξ := by
    dsimp only [ξ]
    infer_instance
  have hρLp (n : ℕ) : MemLp id n ρ := by
    change MemLp id n (carlemanSymmetrization σ)
    exact carleman_memLp_symmetrization σ hs his n
  have hυLp (n : ℕ) : MemLp id n υ := by
    change MemLp id n (carlemanSymmetrization τ)
    exact carleman_memLp_symmetrization τ ht hit n
  have hρint (n : ℕ) : Integrable (fun x : ℝ => |x| ^ n) ρ := by
    change Integrable (fun x : ℝ => |x| ^ n) (carlemanSymmetrization σ)
    exact carleman_integrable_abs_pow_symmetrization σ hs his n
  have hυint (n : ℕ) : Integrable (fun x : ℝ => |x| ^ n) υ := by
    change Integrable (fun x : ℝ => |x| ^ n) (carlemanSymmetrization τ)
    exact carleman_integrable_abs_pow_symmetrization τ ht hit n
  have hξint (n : ℕ) : Integrable (fun x : ℝ => |x| ^ n) ξ := by
    change Integrable (fun x : ℝ => |x| ^ n) (ρ + υ)
    exact (hρint n).add_measure (hυint n)
  let M : ℕ → ℝ := carlemanMomentMajorant ξ
  have heven (k : ℕ) : ∫ x, |x| ^ (2 * k) ∂ξ =
      4 * ProbabilityTheory.moment id k σ := by
    change ∫ x, |x| ^ (2 * k) ∂(carlemanSymmetrization σ + carlemanSymmetrization τ) = _
    exact carleman_integral_abs_pow_add_symmetrizations σ τ hs ht his hit hm k
  have hevenpos (k : ℕ) : 0 < ∫ x, |x| ^ (2 * k) ∂ξ := by
    rw [heven k]
    by_cases hk : k = 0
    · subst k
      simp [ProbabilityTheory.moment]
    · exact mul_pos (by norm_num) (hmpos k (Nat.pos_of_ne_zero hk))
  have hMpos (n : ℕ) : 0 < M n := by
    rcases Nat.even_or_odd n with hn | hn
    · obtain ⟨k, rfl⟩ := hn
      rw [show k + k = 2 * k by omega]
      simp only [M]
      rw [carleman_momentMajorant_even
        (show Even (2 * k) from ⟨k, by omega⟩)]
      exact hevenpos k
    · obtain ⟨k, rfl⟩ := hn
      simp only [M]
      rw [carleman_momentMajorant_odd (show Odd (2 * k + 1) from ⟨k, rfl⟩),
        show 2 * k + 1 - 1 = 2 * k by omega,
        show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
      exact Real.sqrt_pos.2 (mul_pos (hevenpos k) (hevenpos (k + 1)))
  have hMlog : ∀ n, M (n + 1) ^ 2 ≤ M n * M (n + 2) := by
    simpa only [M] using carleman_momentMajorant_logconvex hξint
  have hMzero : M 0 = 4 := by
    simp only [M]
    rw [carleman_momentMajorant_even (show Even 0 from ⟨0, rfl⟩)]
    simpa [ProbabilityTheory.moment] using heven 0
  have hMeven (n : ℕ) : M (2 * (n + 1)) =
      4 * ProbabilityTheory.moment id (n + 1) σ := by
    simp only [M]
    rw [carleman_momentMajorant_even (show Even (2 * (n + 1)) from ⟨n + 1, by omega⟩)]
    exact heven (n + 1)
  have hMdiv : ¬Summable (fun n => M n / M (n + 1)) :=
    carleman_not_summable_ratios M (fun n => ProbabilityTheory.moment id (n + 1) σ)
      hMpos hMzero hMeven (fun n => hmpos (n + 1) (by omega)) hcarleman
  have hρsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (charFun ρ) := contDiff_charFun' hρLp
  have hυsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (charFun υ) := contDiff_charFun' hυLp
  have hbound (n : ℕ) (x : ℝ) :
      ‖iteratedDeriv n (charFun ρ - charFun υ) x‖ ≤ M n := by
    rw [iteratedDeriv_sub (hρsmooth.contDiffAt.of_le (by simp))
      (hυsmooth.contDiffAt.of_le (by simp))]
    calc
      _ ≤ ‖iteratedDeriv n (charFun ρ) x‖ + ‖iteratedDeriv n (charFun υ) x‖ :=
        norm_sub_le _ _
      _ ≤ (∫ y, |y| ^ n ∂ρ) + ∫ y, |y| ^ n ∂υ :=
        add_le_add (carleman_norm_iteratedDeriv_charFun_le n (hρLp n) x)
          (carleman_norm_iteratedDeriv_charFun_le n (hυLp n) x)
      _ = ∫ y, |y| ^ n ∂ξ := (integral_add_measure (hρint n) (hυint n)).symm
      _ ≤ M n := by
        simpa only [M] using carleman_integral_abs_pow_le_momentMajorant hξint n
  have hflat (n : ℕ) : iteratedDeriv n (charFun ρ - charFun υ) 0 = 0 := by
    rw [iteratedDeriv_sub (hρsmooth.contDiffAt.of_le (by simp))
      (hυsmooth.contDiffAt.of_le (by simp)), iteratedDeriv_charFun_zero (hρLp n),
      iteratedDeriv_charFun_zero (hυLp n)]
    change Complex.I ^ n * (∫ x, x ^ n ∂carlemanSymmetrization σ) -
      Complex.I ^ n * (∫ x, x ^ n ∂carlemanSymmetrization τ) = 0
    rw [carleman_integral_pow_symmetrization_eq σ τ hs ht his hit
      (fun k hk => (hm k hk).symm) n, sub_self]
  have hzero_fun : charFun ρ - charFun υ = 0 :=
    carleman_eq_zero_of_iteratedDeriv_bound _ M (hρsmooth.sub hυsmooth) hMpos hMlog
      hbound hMdiv hflat
  have hchar : charFun ρ = charFun υ := by
    funext x
    have hx := congrFun hzero_fun x
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hx
  have hsymm : ρ = υ := Measure.ext_of_charFun hchar
  have hmaps := congrArg (fun ω : Measure ℝ => ω.map (fun x : ℝ => x ^ 2)) hsymm
  change (carlemanSymmetrization σ).map (fun x : ℝ => x ^ 2) =
    (carlemanSymmetrization τ).map (fun x : ℝ => x ^ 2) at hmaps
  rw [carleman_map_sq_symmetrization σ hs, carleman_map_sq_symmetrization τ ht] at hmaps
  exact (carleman_add_self_injective hmaps).symm

/-- **Stieltjes moment determinacy.** A measure $\mu$ on $\mathbb{R}$ is Stieltjes moment
determinate when every probability measure $\nu$ on $\mathbb{R}$ such that $\nu((-\infty, 0)) = 0$,
$\int |x|^k \, d\nu(x) < \infty$ for every integer $k \ge 1$, and
$\int x^k \, d\nu(x) = \int x^k \, d\mu(x)$ for every integer $k \ge 1$ is equal to $\mu$.

The moments of $\mu$ are Bochner integrals, which are $0$ when $x^k$ is not $\mu$-integrable, and
the definition places no condition on $\mu$ itself.

Source: Gwo Dong Lin, "Recent Developments on the Moment Problem", Journal of
Statistical Distributions and Applications (2017), DOI 10.1186/s40488-017-0059-2,
arXiv:1703.01027v3. Corpus `jis_grounded_5e39d97b31ef58deb38a5a58`. Frozen TeX SHA-256
e2dcb54a4b25d57ae3ad6e52267862aeca0ae2f38ffb729df0d727013d3c3080, definition lines 57-75,
criterion lines 297-321. JIS application, frozen source SHA-256
66f0a4a264af03f82a43e3b37e62cc80cf0aed6f43e476e56456006203232bd0, lines 152-177. -/
public def StieltjesMomentDeterminate (μ : MeasureTheory.Measure ℝ) : Prop :=
  ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν],
    ν (Set.Iio (0 : ℝ)) = 0 →
    (∀ k : ℕ, 0 < k → MeasureTheory.Integrable (fun x : ℝ => |x| ^ k) ν) →
    (∀ k : ℕ, 0 < k →
      ProbabilityTheory.moment (id : ℝ → ℝ) k ν =
        ProbabilityTheory.moment (id : ℝ → ℝ) k μ) →
    ν = μ

/-- **Carleman's criterion for the Stieltjes moment problem.** Let $\mu$ be a probability measure
on $\mathbb{R}$ with $\mu((-\infty, 0)) = 0$ such that $\int |x|^k \, d\mu(x) < \infty$ for every
integer $k \ge 1$, and write $m_k = \int x^k \, d\mu(x)$. If
$\sum_{k \ge 1} m_k^{-1/(2k)} = \infty$, where the terms are taken in $[0, \infty]$ (so a term
with $m_k = 0$ equals $\infty$), then $\mu$ is Stieltjes moment determinate.

Proves `Wanted` entry `carleman_stieltjes_criterion`.

Proof: Symmetrize through the square-root map, apply Denjoy--Carleman quasi-analytic
uniqueness to the difference of characteristic functions, then push forward by squaring.

Source: Gwo Dong Lin, "Recent Developments on the Moment Problem" (2017), Theorem 2, (s6) implies
(s7). Corpus `jis_grounded_5e39d97b31ef58deb38a5a58`. Source spans: definition lines 57-75,
criterion lines 297-321, TeX SHA-256
e2dcb54a4b25d57ae3ad6e52267862aeca0ae2f38ffb729df0d727013d3c3080; JIS application lines
152-177, source SHA-256 66f0a4a264af03f82a43e3b37e62cc80cf0aed6f43e476e56456006203232bd0.
-/
public theorem carleman_stieltjes_criterion
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (hsupp : μ (Set.Iio (0 : ℝ)) = 0)
    (hint : ∀ k : ℕ, 0 < k →
      MeasureTheory.Integrable (fun x : ℝ => |x| ^ k) μ)
    (hcarleman : tsum (fun n : ℕ =>
      ENNReal.rpow
        (ENNReal.ofReal
          (ProbabilityTheory.moment (id : ℝ → ℝ) (n + 1) μ))
        (-1 / (2 * ((n + 1 : ℕ) : ℝ)))) = ⊤) :
    StieltjesMomentDeterminate μ := by
  intro ν _ hνsupp hνint hm
  exact carleman_measure_eq μ ν hsupp hνsupp hint hνint hm hcarleman

end MetaMathlibExt
