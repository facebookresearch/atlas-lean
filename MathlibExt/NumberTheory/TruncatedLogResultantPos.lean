/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TruncatedLogDiscriminant
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Positivity of the truncated logarithmic resultant

The resultant product for the truncated logarithmic polynomial is positive in every positive degree.
-/

namespace MetaMathlibExt

open Complex Polynomial
open scoped ComplexOrder

namespace truncatedLogResultantProduct_pos

private lemma eval_succ (z : ℂ) (n : ℕ) :
    aeval z (truncatedLogPolynomial (n + 1)) =
      aeval z (truncatedLogPolynomial n) + (↑(((n + 1 : ℕ) : ℝ)⁻¹) : ℂ) * z ^ (n + 1) := by
  have hpoly : truncatedLogPolynomial (n + 1) =
      truncatedLogPolynomial n + C (((n + 1 : ℕ) : ℚ)⁻¹) * X ^ (n + 1) := by
    simp only [truncatedLogPolynomial, Finset.sum_Icc_succ_top (Nat.succ_pos n), add_assoc]
  simp [hpoly]

-- Multiplying by 1 - z makes successive reciprocal coefficients appear as differences.
private lemma re_eval_mul_ge {z : ℂ} (hz : ‖z‖ = 1) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ)⁻¹) * (1 - z ^ (n + 1)).re ≤
      ((1 - z) * aeval z (truncatedLogPolynomial n)).re := by
  have hpow (k : ℕ) : 0 ≤ (1 - z ^ k).re := by
    have h := re_le_norm (z ^ k)
    rw [norm_pow, hz, one_pow] at h
    simpa only [sub_re, one_re, sub_nonneg] using h
  induction n, hn using Nat.le_induction with
  | base =>
    have heval : aeval z (truncatedLogPolynomial 1) = 1 + z := by
      simp [truncatedLogPolynomial]
    rw [heval, show (1 - z) * (1 + z) = 1 - z ^ 2 by ring, Nat.cast_one, inv_one, one_mul]
  | succ n hn ih =>
    have hstep : (1 - z) * aeval z (truncatedLogPolynomial (n + 1)) =
        (1 - z) * aeval z (truncatedLogPolynomial n) +
          (↑(((n + 1 : ℕ) : ℝ)⁻¹) : ℂ) * ((1 - z ^ (n + 2)) - (1 - z ^ (n + 1))) := by
      rw [eval_succ, pow_succ z (n + 1)]
      ring
    have hcoeff : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (n : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by exact_mod_cast hn)).mpr (by exact_mod_cast n.le_succ)
    have hmul := mul_le_mul_of_nonneg_right hcoeff (hpow (n + 1))
    simp only [hstep, add_re, re_ofReal_mul, sub_re, one_re] at ih hmul ⊢
    linarith

private lemma re_one_sub_pos {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    0 < (1 - z).re := by
  rw [sub_re, one_re, sub_pos]
  have hle : z.re ≤ 1 := hz ▸ re_le_norm z
  refine lt_of_le_of_ne hle fun hre => hz1 ?_
  have him : z.im = 0 := abs_re_eq_norm.mp (by simp [hz, hre])
  exact Complex.ext (by simpa using hre) (by simpa using him)

-- Conjugate pairs contribute squared norms. A conjugation-fixed factor is positive real.
private lemma prod_pos_of_conj_multiset (s : Multiset ℂ)
    (hs : s.map (starRingEnd ℂ) = s)
    (h0 : ∀ z ∈ s, z ≠ 0)
    (hr : ∀ z ∈ s, (starRingEnd ℂ) z = z → 0 < z) :
    0 < s.prod := by
  classical
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    by_cases hempty : s = 0
    · simp [hempty]
    obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hempty
    let c := starRingEnd ℂ
    have hlt : s.erase z < s := Multiset.erase_lt.mpr hz
    have hmap (t : Multiset ℂ) (w : ℂ) :
        (t.erase w).map c = (t.map c).erase (c w) :=
      Multiset.map_erase c c.injective w t
    by_cases hzreal : c z = z
    · have hfix : (s.erase z).map c = s.erase z := by rw [hmap, hs, hzreal]
      rw [← Multiset.prod_erase hz]
      exact mul_pos (hr z hz hzreal) (ih _ hlt hfix
        (fun w hw => h0 w (Multiset.mem_of_le hlt.le hw))
        (fun w hw => hr w (Multiset.mem_of_le hlt.le hw)))
    · have hcz : c z ∈ s.erase z := by
        apply (Multiset.mem_erase_of_ne hzreal).mpr
        rw [← hs]
        exact Multiset.mem_map_of_mem _ hz
      have hle := Multiset.erase_le (c z) (s.erase z)
      have hfix : ((s.erase z).erase (c z)).map c = (s.erase z).erase (c z) := by
        rw [hmap, hmap, hs, show c (c z) = z from Complex.conj_conj z, Multiset.erase_comm]
      have hpair : 0 < z * c z := by
        rw [Complex.mul_conj', ← ofReal_pow, zero_lt_real]
        exact pow_pos (norm_pos_iff.mpr (h0 z hz)) _
      rw [← Multiset.prod_erase hz, ← Multiset.prod_erase hcz, ← mul_assoc]
      exact mul_pos hpair (ih _ (hle.trans_lt hlt) hfix
        (fun w hw => h0 w (Multiset.mem_of_le (hle.trans hlt.le) hw))
        (fun w hw => hr w (Multiset.mem_of_le (hle.trans hlt.le) hw)))

end truncatedLogResultantProduct_pos

/-- **Positivity of the resultant product.** For every natural number $n \ge 1$, the resultant
product $\mathcal{P}_n$ is a positive integer.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Lemma 1
(`integers-2025-A39-lem-1`). -/
public theorem truncatedLogResultantProduct_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < truncatedLogResultantProduct n := by
  classical
  open truncatedLogResultantProduct_pos in
  let ι := Int.castRingHom ℂ
  let p : ℤ[X] := ∑ i ∈ Finset.range n, X ^ i
  let f := p.map ι
  let g := (scaledTruncatedLogPolynomial n).map ι
  let s := f.roots.map g.eval
  have hn0 : n ≠ 0 := by omega
  have hι : Function.Injective ι := Int.cast_injective
  have hf : f.Splits := IsAlgClosed.splits f
  have hmonic : f.Monic := (monic_geom_sum_X hn0 : p.Monic).map ι
  have hres : (↑(truncatedLogResultantProduct n) : ℂ) = s.prod := by
    change ι (resultant p (scaledTruncatedLogPolynomial n)) = s.prod
    rw [← resultant_map_map, ← natDegree_map_eq_of_injective hι p,
      ← natDegree_map_eq_of_injective hι (scaledTruncatedLogPolynomial n)]
    simpa only [hmonic.leadingCoeff, one_pow, one_mul] using
      resultant_eq_prod_eval f g g.natDegree le_rfl hf
  have hroot (z : ℂ) (hz : z ∈ f.roots) : z ^ n = 1 ∧ z ≠ 1 := by
    have hsum : ∑ i ∈ Finset.range n, z ^ i = 0 := by
      simpa [f, p, Polynomial.IsRoot, Polynomial.map_sum, Polynomial.eval_finsetSum] using
        (mem_roots hmonic.ne_zero).mp hz
    refine ⟨?_, ?_⟩
    · simpa [hsum, sub_eq_zero] using (geom_sum_mul z n).symm
    · rintro rfl
      have hcast : (n : ℂ) = 0 := by simpa using hsum
      exact hn0 (by exact_mod_cast hcast)
  have hscaled (z : ℂ) :
      g.eval z = (truncatedLogLcm n : ℂ) * aeval z (truncatedLogPolynomial n) := by
    have hmap := congrArg (Polynomial.map (algebraMap ℚ ℂ)) (map_scaledTruncatedLogPolynomial n)
    rw [Polynomial.map_map, RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) ι] at hmap
    change ((scaledTruncatedLogPolynomial n).map ι).eval z = _
    rw [hmap, Polynomial.map_mul, map_C, eval_mul, eval_C, aeval_def, eval_map]
    simp
  have hfactor (w : ℂ) (hw : w ∈ s) : w ≠ 0 ∧ (w.im = 0 → 0 < w.re) := by
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    obtain ⟨hpow, hz1⟩ := hroot z hz
    have hnorm := Complex.norm_eq_one_of_pow_eq_one hpow hn0
    have hdiff := re_one_sub_pos hnorm hz1
    have hbound := re_eval_mul_ge hnorm hn
    rw [pow_succ, hpow, one_mul] at hbound
    have hpos : 0 < ((1 - z) * g.eval z).re := by
      rw [hscaled, mul_left_comm, ← Complex.ofReal_natCast, re_ofReal_mul]
      have hlcm : 0 < (truncatedLogLcm n : ℝ) := by
        have hlcm : truncatedLogLcm n ≠ 0 := by
          rw [truncatedLogLcm, Finset.lcm_ne_zero_iff]
          exact fun j hj => Nat.ne_of_gt (Finset.mem_Icc.mp hj).1
        exact_mod_cast Nat.pos_of_ne_zero hlcm
      exact mul_pos hlcm ((mul_pos (by positivity) hdiff).trans_le hbound)
    refine ⟨?_, fun him => ?_⟩
    · intro heq
      simp [heq] at hpos
    · rw [Complex.mul_re, him, mul_zero, sub_zero] at hpos
      exact pos_of_mul_pos_right hpos hdiff.le
  have hstar (q : ℤ[X]) : (q.map ι).map (starRingEnd ℂ) = q.map ι := by
    rw [Polynomial.map_map, RingHom.ext_int ((starRingEnd ℂ).comp ι) ι]
  have hs : s.map (starRingEnd ℂ) = s := by
    have hroots : f.roots.map (starRingEnd ℂ) = f.roots := by
      rw [← hf.roots_map, show f.map (starRingEnd ℂ) = f from hstar p]
    calc
      s.map (starRingEnd ℂ) = (f.roots.map (starRingEnd ℂ)).map g.eval := by
        change (f.roots.map g.eval).map (starRingEnd ℂ) = _
        rw [Multiset.map_map, Multiset.map_map]
        apply Multiset.map_congr rfl
        intro z _
        change (starRingEnd ℂ) (g.eval z) = g.eval ((starRingEnd ℂ) z)
        rw [← eval_map_apply, show g.map (starRingEnd ℂ) = g from hstar _]
      _ = s := by rw [hroots]
  have hpos : 0 < (↑(truncatedLogResultantProduct n) : ℂ) := by
    rw [hres]
    exact prod_pos_of_conj_multiset s hs (fun w hw => (hfactor w hw).1) fun w hw hfix => by
      have him := Complex.conj_eq_iff_im.mp hfix
      exact Complex.pos_iff.mpr ⟨(hfactor w hw).2 him, him.symm⟩
  have hre := (Complex.pos_iff.mp hpos).1
  exact_mod_cast (show (0 : ℝ) < (truncatedLogResultantProduct n : ℝ) by simpa using hre)

end MetaMathlibExt
