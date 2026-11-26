/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ComplexAnalysis/ComplementaryPolynomials.lean` (leanprover/lean-eval), at commit
38361be884302c7edce1908c4aef8296eb2cb27e, for the theorem statement.
Copyright 2026 Lean FRO, LLC.
Author (problem submitter): Kim Morrison.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream project ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS converted the benchmark theorem to a
wanted declaration and placed it in its current namespace. This module moves the statement from
`WantedExt/Analysis/ComplementaryPolynomialsWanted.lean` and supplies a proof.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Perfect

/-!
# Complementary polynomials on the unit circle

This is the basic existence statement appearing in quantum signal processing: if a complex
polynomial has sup norm at most `1` on the unit circle, then it admits a complementary polynomial
whose squared moduli add up to `1` on the circle.

The previous statement asked for `Q.natDegree = P.natDegree` (strict equality), which fails on
the boundary case `P = X`: there `|P(z)| = 1` on the entire unit circle, so any complementary `Q`
must vanish on the circle and hence be the zero polynomial; but `natDegree 0 = 0 ≠ 1 = natDegree X`.
We relax the constraint to `≤`, which is what Fejér-Riesz / spectral factorization actually
delivers (the degree of `Q` is at most that of `P`, with equality generically).
-/

namespace MathlibExt.Analysis.ComplementaryPolynomialsWanted.ComplexAnalysis

open Polynomial Complex
open scoped ComplexConjugate ComplexOrder

private noncomputable def circleQuot (F : ℂ[X]) (n : ℕ) (z : Circle) : ℂ :=
  F.eval (z : ℂ) / (z : ℂ) ^ n

private lemma continuous_circleQuot (F : ℂ[X]) (n : ℕ) :
    Continuous (circleQuot F n) := by
  exact (F.continuous.comp continuous_subtype_val).div
    (continuous_subtype_val.pow n) (fun z => pow_ne_zero _ (Circle.coe_ne_zero z))

-- Coefficient conjugation followed by reflection about the specified degree bound.
private noncomputable def reflectedConj (n : ℕ) (F : ℂ[X]) : ℂ[X] :=
  (F.map (starRingEnd ℂ)).reflect n

private lemma eval_reflectedConj {F : ℂ[X]} {n : ℕ} (hF : F.natDegree ≤ n) {z : ℂ}
    (hz : z ≠ 0) :
    (reflectedConj n F).eval z = z ^ n * conj (F.eval (conj z⁻¹)) := by
  let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹ n (F.map (starRingEnd ℂ))
    (natDegree_map_le.trans hF)
  have hc (w : ℂ) : (F.map (starRingEnd ℂ)).eval w = conj (F.eval (conj w)) := by
    simpa using (eval_map_apply (f := starRingEnd ℂ) (p := F) (conj w))
  rw [show ⅟(z⁻¹) = z by rw [invOf_eq_inv, inv_inv], eval₂_id, eval₂_id, inv_pow] at h
  rw [← div_eq_mul_inv] at h
  rw [reflectedConj, (div_eq_iff (pow_ne_zero n hz)).mp h, hc, mul_comm]

private lemma eval_reflectedConj_circle {F : ℂ[X]} {n : ℕ} (hF : F.natDegree ≤ n)
    (z : Circle) :
    (reflectedConj n F).eval (z : ℂ) = (z : ℂ) ^ n * conj (F.eval (z : ℂ)) := by
  rw [eval_reflectedConj hF z.coe_ne_zero, inv_eq_conj z.norm_coe, conj_conj]

private lemma reflectedConj_eq {F : ℂ[X]} {n : ℕ} (hF : F.natDegree ≤ 2 * n)
    (h : ∀ z, 0 ≤ circleQuot F n z) : reflectedConj (2 * n) F = F := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have : Infinite Circle := Infinite.of_injective _ AddCircle.homeomorphCircle'.injective
  apply eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective (α := Circle) Circle.coe_injective).mono ?_
  rintro _ ⟨z, rfl⟩
  change (reflectedConj (2 * n) F).eval (z : ℂ) = F.eval (z : ℂ)
  have hz : (z : ℂ) ^ n ≠ 0 := pow_ne_zero _ z.coe_ne_zero
  have hconj : conj (circleQuot F n z) = circleQuot F n z :=
    conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp (h z)).2
  have heval : F.eval (z : ℂ) = (z : ℂ) ^ n * circleQuot F n z := by
    rw [circleQuot, mul_comm, div_mul_cancel₀ _ hz]
  calc
    _ = (z : ℂ) ^ (2 * n) * conj (F.eval (z : ℂ)) := eval_reflectedConj_circle hF z
    _ = (z : ℂ) ^ n * circleQuot F n z := by
      rw [heval, map_mul, hconj, map_pow, ← inv_eq_conj z.norm_coe, inv_pow, mul_comm 2 n, pow_mul]
      field_simp
    _ = F.eval (z : ℂ) := heval.symm

-- A zero of the nonnegative normalized evaluation has zero derivative along the circle.
private lemma derivative_eval_eq_zero {F : ℂ[X]} {n : ℕ}
    (h : ∀ z, 0 ≤ circleQuot F n z) {a : Circle} (ha : F.IsRoot (a : ℂ)) :
    F.derivative.eval (a : ℂ) = 0 := by
  let path : ℝ → ℂ := fun t => (a : ℂ) * (Circle.exp t : ℂ)
  have hpath₀ : path 0 = a := by simp [path]
  have hpath : HasDerivAt path ((a : ℂ) * I) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I 0 :=
      (hasDerivAt_mul_const I).comp_ofReal
    simpa [path, Circle.coe_exp] using (hlin.cexp.const_mul (a : ℂ))
  have heval := (F.hasDerivAt (path 0)).comp 0 hpath
  let f : ℝ → ℂ := fun t => F.eval (path t) / path t ^ n
  have hf : HasDerivAt f (F.derivative.eval (a : ℂ) * ((a : ℂ) * I) / (a : ℂ) ^ n) 0 := by
    have hn : path 0 ^ n ≠ 0 := by simp [hpath₀]
    have he := heval.fun_div (hpath.pow n) hn
    simp only [Pi.pow_apply, Function.comp_apply, hpath₀, ha.eq_zero, zero_mul, sub_zero] at he
    convert he using 1
    field_simp [a.coe_ne_zero]
  have hnonneg (t : ℝ) : 0 ≤ f t := h (a * Circle.exp t)
  have hf₀ : f 0 = 0 := by simp [f, hpath₀, ha.eq_zero]
  have hmin : IsLocalMin (fun t => (f t).re) 0 :=
    Filter.Eventually.of_forall (fun t => by
      simpa [hf₀] using (RCLike.nonneg_iff.mp (hnonneg t)).1)
  have hre := hmin.hasDerivAt_eq_zero
    (reCLM.hasFDerivAt.comp_hasDerivAt 0 hf)
  have him : (fun t => (f t).im) = fun _ => 0 :=
    funext fun t => (RCLike.nonneg_iff.mp (hnonneg t)).2
  have him' := imCLM.hasFDerivAt.comp_hasDerivAt 0 hf
  change HasDerivAt (fun t => (f t).im) _ _ at him'
  rw [him] at him'
  have hd : F.derivative.eval (a : ℂ) * ((a : ℂ) * I) / (a : ℂ) ^ n = 0 := by
    apply Complex.ext
    · exact hre
    · exact him'.unique (hasDerivAt_const 0 0)
  exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hd).resolve_right
    (pow_ne_zero _ a.coe_ne_zero))).resolve_right (mul_ne_zero a.coe_ne_zero I_ne_zero)

private lemma pair_factor {F : ℂ[X]} {n : ℕ} (hF : F.natDegree ≤ 2 * n)
    (h : ∀ z, 0 ≤ circleQuot F n z) {a : ℂ} (ha : F.IsRoot a) (ha₀ : a ≠ 0) :
    ∃ G : ℂ[X], F = (X - C a) * (1 - C (conj a) * X) * G := by
  let b := (conj a)⁻¹
  have hca : conj a ≠ 0 := by simpa
  have hb₀ : b ≠ 0 := inv_ne_zero hca
  have hb : F.IsRoot b := by
    rw [IsRoot.def, ← reflectedConj_eq hF h, eval_reflectedConj hF hb₀]
    simp [b, ha.eq_zero]
  obtain ⟨G, hG⟩ := dvd_iff_isRoot.mpr ha
  have hGb : G.IsRoot b := by
    by_cases hab : b = a
    · have haa : ‖a‖ = 1 := by
        have hh : a * conj a = 1 := calc
          _ = b * conj a := by rw [hab]
          _ = 1 := inv_mul_cancel₀ hca
        rw [mul_conj'] at hh
        have hs : ‖a‖ ^ 2 = 1 := by exact_mod_cast hh
        nlinarith [norm_nonneg a]
      let z : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr haa⟩
      have hd := derivative_eval_eq_zero h (a := z) ha
      change F.derivative.eval a = 0 at hd
      rw [hG, derivative_mul] at hd
      simpa [IsRoot, hab] using hd
    · have hv := hb.eq_zero
      rw [hG, eval_mul, eval_sub, eval_X, eval_C] at hv
      exact (mul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr hab)
  obtain ⟨H, hH⟩ := dvd_iff_isRoot.mpr hGb
  have hlin : 1 - C (conj a) * X = C (-conj a) * (X - C b) := by
    rw [mul_sub, ← C_mul, C_neg, neg_mul]
    have hh : -conj a * b = -1 := by simp [b, hca]
    rw [hh, C_neg, C_1]
    ring
  have hs : C (-conj a) * C ((-conj a)⁻¹) = (1 : ℂ[X]) := by
    rw [← C_mul, mul_inv_cancel₀ (neg_ne_zero.mpr hca), C_1]
  refine ⟨C ((-conj a)⁻¹) * H, ?_⟩
  rw [hG, hH, hlin]
  calc
    _ = (X - C a) * (C (-conj a) * C ((-conj a)⁻¹) * (X - C b) * H) := by
      rw [hs, one_mul]
    _ = _ := by ring

private lemma eval_pair (a : ℂ) (z : Circle) :
    ((X - C a) * (1 - C (conj a) * X)).eval (z : ℂ) =
      (z : ℂ) * (‖(z : ℂ) - a‖ ^ 2 : ℝ) := by
  have h := mul_conj' ((z : ℂ) - a)
  rw [map_sub, ← inv_eq_conj z.norm_coe] at h
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_one]
  push_cast at *
  rw [← h]
  field_simp [z.coe_ne_zero]

private lemma circleQuot_factor (n : ℕ) (a : ℂ) (G : ℂ[X]) (z : Circle) :
    circleQuot ((X - C a) * (1 - C (conj a) * X) * G) (n + 1) z =
      (‖(z : ℂ) - a‖ ^ 2 : ℝ) * circleQuot G n z := by
  rw [circleQuot, eval_mul, eval_pair, pow_succ, circleQuot]
  field_simp [z.coe_ne_zero]
  ring

private lemma exists_circle_factor (n : ℕ) (F : ℂ[X]) (hF : F.natDegree ≤ 2 * n)
    (h : ∀ z, 0 ≤ circleQuot F n z) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧
      ∀ z : Circle, circleQuot F n z = (‖Q.eval (z : ℂ)‖ ^ 2 : ℝ) := by
  induction n generalizing F with
  | zero =>
    have hF₀ : F = C (F.coeff 0) := eq_C_of_natDegree_le_zero (by simpa using hF)
    obtain ⟨r, hr, hrF⟩ := RCLike.nonneg_iff_exists_ofReal.mp (h (1 : Circle))
    rw [hF₀, circleQuot, eval_C, pow_zero, div_one] at hrF
    refine ⟨C (Real.sqrt r : ℂ), by simp, fun z => ?_⟩
    rw [hF₀, circleQuot, eval_C, eval_C, pow_zero, div_one, ← hrF]
    simp [Real.norm_of_nonneg (Real.sqrt_nonneg r), Real.sq_sqrt hr]
  | succ n ih =>
    by_cases hzero : F = 0
    · exact ⟨0, by simp, by simp [hzero, circleQuot]⟩
    have hsym := congrArg (fun p : ℂ[X] => p.coeff 0) (reflectedConj_eq hF h)
    simp only [reflectedConj, coeff_reflect, revAt_zero, coeff_map] at hsym
    by_cases hc : F.coeff 0 = 0
    · have htop : F.coeff (2 * (n + 1)) = 0 := by
        simpa [hc] using congrArg conj hsym
      have hdeg : F.natDegree < 2 * (n + 1) := by
        refine lt_of_le_of_ne hF (fun he => ?_)
        rw [← he, ← leadingCoeff, leadingCoeff_eq_zero] at htop
        exact hzero htop
      obtain ⟨G, hG⟩ := X_dvd_iff.mpr hc
      have hG₀ : G ≠ 0 := by rintro rfl; simp_all
      rw [hG, natDegree_mul X_ne_zero hG₀, natDegree_X] at hdeg
      have heval (z : Circle) : circleQuot F (n + 1) z = circleQuot G n z := by
        rw [circleQuot, hG, eval_mul, eval_X, pow_succ, circleQuot]
        field_simp [z.coe_ne_zero]
      obtain ⟨Q, hQ, he⟩ := ih G (by omega) (fun z => heval z ▸ h z)
      exact ⟨Q, hQ.trans n.le_succ, fun z => (heval z).trans (he z)⟩
    · have hdeg : 2 * (n + 1) ≤ F.natDegree := by
        apply le_natDegree_of_ne_zero
        intro hn
        rw [hn, map_zero] at hsym
        exact hc hsym.symm
      obtain ⟨a, ha⟩ := Complex.exists_root (f := F)
        (natDegree_pos_iff_degree_pos.mp (by omega))
      have ha₀ : a ≠ 0 := by rintro rfl; exact hc ((coeff_zero_eq_eval_zero F).trans ha.eq_zero)
      obtain ⟨G, hG⟩ := pair_factor hF h ha ha₀
      have hca : conj a ≠ 0 := by simpa
      have hlin : (1 - C (conj a) * X : ℂ[X]).natDegree = 1 := by
        rw [natDegree_sub_eq_right_of_natDegree_lt, natDegree_C_mul_X _ hca]
        simp [natDegree_C_mul_X _ hca]
      have hG₀ : G ≠ 0 := by rintro rfl; simp_all
      have hlin₀ : (1 - C (conj a) * X : ℂ[X]) ≠ 0 := by
        intro hz
        simp [hz] at hlin
      rw [hG, natDegree_mul (mul_ne_zero (X_sub_C_ne_zero a) hlin₀) hG₀,
        natDegree_mul (X_sub_C_ne_zero a) hlin₀, natDegree_X_sub_C, hlin] at hF
      have heval (z : Circle) := (congrArg (fun F => circleQuot F (n + 1) z) hG).trans
        (circleQuot_factor n a G z)
      have hG_nonneg (z : Circle) : 0 ≤ circleQuot G n z := by
        have key (w : Circle) (hw : (w : ℂ) ≠ a) : 0 ≤ circleQuot G n w := by
          have hd : 0 < ‖(w : ℂ) - a‖ ^ 2 := sq_pos_of_ne_zero
            (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw))
          have hw' := h w
          rw [heval, RCLike.nonneg_iff] at hw'
          change 0 ≤ (↑(‖(w : ℂ) - a‖ ^ 2) * circleQuot G n w : ℂ).re ∧
            (↑(‖(w : ℂ) - a‖ ^ 2) * circleQuot G n w : ℂ).im = 0 at hw'
          simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero] at hw'
          exact RCLike.nonneg_iff.mpr ⟨(mul_nonneg_iff_of_pos_left hd).mp hw'.1,
            (mul_eq_zero.mp hw'.2).resolve_left hd.ne'⟩
        by_cases hz : (z : ℂ) = a
        · have : Nontrivial Circle := ⟨⟨-1, 1, Circle.neg_ne_self 1⟩⟩
          have : Filter.NeBot (nhdsWithin z ({z}ᶜ : Set Circle)) := by
            have hz' := PerfectSpace.univ_preperfect z (Set.mem_univ z)
            simpa [AccPt, nhdsWithin] using hz'
          have hs : ({z}ᶜ : Set Circle) ⊆ {w | 0 ≤ circleQuot G n w} := by
            intro w hw
            exact key w (fun hwa => hw (Circle.coe_injective (hwa.trans hz.symm)))
          have hc : IsClosed {w | 0 ≤ circleQuot G n w} :=
            isClosed_le continuous_const (continuous_circleQuot G n)
          exact hc.closure_subset_iff.mpr hs ((dense_compl_singleton z) z)
        · exact key z hz
      obtain ⟨Q, hQ, hQeval⟩ := ih G (by omega) hG_nonneg
      refine ⟨(X - C a) * Q, ?_, fun z => ?_⟩
      · exact natDegree_mul_le.trans (by rw [natDegree_X_sub_C]; omega)
      · rw [heval, hQeval, eval_mul, eval_sub, eval_X, eval_C, norm_mul, mul_pow, ofReal_mul]

/-- **Complementary polynomial on the unit circle.** Let $P$ be a complex polynomial with
$|P(z)| \le 1$ for every complex number $z$ with $|z| = 1$. Then there is a complex polynomial $Q$
with $\deg Q \le \deg P$ such that $|P(z)|^2 + |Q(z)|^2 = 1$ for every $z$ with $|z| = 1$. Here
the degree of the zero polynomial is taken to be $0$.

Source: https://link.springer.com/article/10.1007/s00220-025-05302-9 Via
leanprover/lean-eval@38361be, problem `exists_complementary_polynomial_on_unit_circle`. -/
public theorem exists_complementary_polynomial_on_unit_circle
    (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  let n := P.natDegree
  let F : ℂ[X] := X ^ n - P * reflectedConj n P
  have hR : (reflectedConj n P).natDegree ≤ n := by
    exact (natDegree_reflect_le (N := n)).trans (max_le le_rfl natDegree_map_le)
  have hF : F.natDegree ≤ 2 * n := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (by rw [natDegree_X_pow]; omega) (natDegree_mul_le.trans (by omega))
  have heval (z : Circle) :
      circleQuot F n z = (↑(1 - ‖P.eval (z : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    change circleQuot (X ^ n - P * reflectedConj n P) n z = _
    rw [circleQuot, eval_sub, eval_X_pow, eval_mul,
      eval_reflectedConj_circle (n := n) (F := P) le_rfl, ← mul_left_comm, mul_conj']
    push_cast
    field_simp [z.coe_ne_zero]
  have h (z : Circle) : 0 ≤ circleQuot F n z := by
    rw [heval]
    apply RCLike.ofReal_nonneg.mpr
    apply sub_nonneg.mpr
    simpa only [one_pow] using (pow_le_pow_left₀ (norm_nonneg _) (hP z) 2)
  obtain ⟨Q, hQ, hQeval⟩ := exists_circle_factor n F hF h
  refine ⟨Q, hQ, fun z => ?_⟩
  have he := ofReal_injective ((heval z).symm.trans (hQeval z))
  linarith only [he]

end MathlibExt.Analysis.ComplementaryPolynomialsWanted.ComplexAnalysis
