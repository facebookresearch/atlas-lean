/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Analytic.Polynomial

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import MathlibExt.Analysis.Complex.Hurwitz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.MeanInequalities

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted

/-- H-stability: no zeros when every coordinate has positive real part. -/
private def vdw_HStable (k : ℕ) (q : MvPolynomial (Fin k) ℝ) : Prop :=
  ∀ z : Fin k → ℂ, (∀ i, 0 < (z i).re) → MvPolynomial.aeval z q ≠ 0

/-- Capacity bound: `c * ∏ x ≤ eval x q` on the positive orthant. -/
private def vdw_CapBound (k : ℕ) (q : MvPolynomial (Fin k) ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin k → ℝ, (∀ i, 0 < x i) → c * ∏ i, x i ≤ MvPolynomial.eval x q

/-- Full positivity of degree `d`: every degree-`d` coefficient is positive. -/
private def vdw_FullPos (k d : ℕ) (q : MvPolynomial (Fin k) ℝ) : Prop :=
  ∀ m : Fin k →₀ ℕ, Finsupp.degree m = d → 0 < q.coeff m

/-- The all-ones exponent. -/
private noncomputable def vdw_ones (k : ℕ) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm 1

/-- The `T` operator: `∂q/∂x₀` at `x₀ = 0`. -/
private noncomputable def vdw_T (k : ℕ) (q : MvPolynomial (Fin (k + 1)) ℝ) :
    MvPolynomial (Fin k) ℝ :=
  Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k q) 1

/-- The `D` operator: `∂q/∂x₀` in all variables, via `finSuccEquiv`. -/
private noncomputable def vdw_D (k : ℕ) (q : MvPolynomial (Fin (k + 1)) ℝ) :
    MvPolynomial (Fin (k + 1)) ℝ :=
  (MvPolynomial.finSuccEquiv ℝ k).symm
    (Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ k q))

/-- The product of column linear forms. -/
private noncomputable def vdw_p (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ j, ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i

/-- The Gurvits factor `g k = (k / (k + 1)) ^ k`. -/
private noncomputable def vdw_g (k : ℕ) : ℝ :=
  ((k : ℝ) / ((k : ℝ) + 1)) ^ k

private lemma vdw_pi_mul_sigma {m : ℕ} {s : Fin m → ℝ} (hs : ∀ i, 0 < s i) :
    (∏ i, s i) * (∑ i, (s i)⁻¹) = ∑ i, ∏ j ∈ Finset.univ.erase i, s j := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (∏ j ∈ Finset.univ.erase i, s j) = (∏ j, s j) * (s i)⁻¹ := by
    intro i _
    have hne : s i ≠ 0 := ne_of_gt (hs i)
    have hmul : s i * (∏ j ∈ Finset.univ.erase i, s j) = ∏ j, s j :=
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)
    have hinv : (∏ j ∈ Finset.univ.erase i, s j)
        = (s i)⁻¹ * (s i * (∏ j ∈ Finset.univ.erase i, s j)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [hinv, hmul]
    ring
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => (hterm i hi).symm

private lemma vdw_amgm_prod_bound {k m : ℕ} (hm : m ≤ k + 1) {a : ℝ} (ha : 0 < a)
    {b : ℝ} {s : Fin m → ℝ} (hs : ∀ i, 0 < s i)
    (h : ∀ t : ℝ, 0 < t → b * t ≤ a * ∏ i, (t + s i)) :
    ((k : ℝ) / ((k : ℝ) + 1)) ^ k * b
      ≤ a * ∑ i, ∏ j ∈ Finset.univ.erase i, s j := by
  have hg_nonneg : (0 : ℝ) ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ k := by
    apply pow_nonneg
    apply div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hsum_nonneg : (0 : ℝ) ≤ a * ∑ i, ∏ j ∈ Finset.univ.erase i, s j := by
    apply mul_nonneg (le_of_lt ha)
    apply Finset.sum_nonneg fun i _ => ?_
    apply Finset.prod_nonneg fun j _ => ?_
    exact le_of_lt (hs j)
  by_cases hb : b ≤ 0
  · calc ((k : ℝ) / ((k : ℝ) + 1)) ^ k * b
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg_nonneg hb
      _ ≤ a * ∑ i, ∏ j ∈ Finset.univ.erase i, s j := hsum_nonneg
  · push Not at hb
    by_cases hm0 : m = 0
    · subst hm0
      have hprod : ∀ t : ℝ, (∏ i : Fin 0, (t + s i)) = 1 := fun _ => by simp
      have htpos : (0 : ℝ) < a / b + 1 := by
        have hdiv : (0 : ℝ) ≤ a / b :=
          div_nonneg (le_of_lt ha) (le_of_lt hb)
        linarith
      have h1 := h (a / b + 1) htpos
      rw [hprod] at h1
      have hbt : b * (a / b + 1) = a + b := by
        have hne : b ≠ 0 := ne_of_gt hb
        rw [mul_add, mul_div_cancel₀ _ hne, mul_one]
      rw [hbt, mul_one] at h1
      have : b ≤ 0 := by linarith
      exact absurd this (not_le_of_gt hb)
    · by_cases hk0 : k = 0
      · have hm1 : m = 1 := by omega
        subst hm1
        subst hk0
        have hble : b ≤ a := by
          by_contra hcon
          push Not at hcon
          have hdiff : (0 : ℝ) < b - a := by linarith
          have hs0 : (0 : ℝ) < s 0 := hs 0
          have htpos : (0 : ℝ) < (a * s 0 + 1) / (b - a) := by positivity
          have h1 := h ((a * s 0 + 1) / (b - a)) htpos
          have hprod1 : (∏ i : Fin 1, ((a * s 0 + 1) / (b - a) + s i))
              = (a * s 0 + 1) / (b - a) + s 0 := by
            have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
            rw [Fintype.prod_unique, hdef]
          rw [hprod1] at h1
          have hne : b - a ≠ 0 := ne_of_gt hdiff
          have hcalc : b * ((a * s 0 + 1) / (b - a))
              = a * ((a * s 0 + 1) / (b - a) + s 0) + 1 := by
            field_simp
            ring
          linarith
        have hLHS : ((↑(0 : ℕ) : ℝ) / ((↑(0 : ℕ) : ℝ) + 1)) ^ (0 : ℕ) * b = b := by
          simp
        have hRHS : a * ∑ i : Fin 1, ∏ j ∈ Finset.univ.erase i, s j = a := by
          have hsum1 : (∑ i : Fin 1, ∏ j ∈ Finset.univ.erase i, s j) = 1 := by
            rw [Fintype.sum_unique]
            have herase : Finset.univ.erase (default : Fin 1) = ∅ := by
              rw [Finset.univ_unique]
              exact Finset.erase_singleton _
            rw [herase]
            exact Finset.prod_empty
          rw [hsum1, mul_one]
        rw [hLHS, hRHS]
        exact hble
      · have mpos : 0 < m := Nat.pos_of_ne_zero hm0
        have kpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hKpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr kpos
        have hK1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
        have hπpos : (0 : ℝ) < ∏ i, s i :=
          Finset.prod_pos fun i _ => hs i
        have hσpos : (0 : ℝ) < ∑ i, (s i)⁻¹ := by
          apply Finset.sum_pos (fun i _ => inv_pos.mpr (hs i))
          exact Finset.univ_nonempty_iff.mpr ⟨⟨0, mpos⟩⟩
        have hprod_eq : ∀ t : ℝ, ∏ i, (t + s i)
            = (∏ i, s i) * ∏ i, (1 + t * (s i)⁻¹) := by
          intro t
          have hterm : ∀ i : Fin m, t + s i = s i * (1 + t * (s i)⁻¹) := by
            intro i
            have hne : s i ≠ 0 := ne_of_gt (hs i)
            rw [mul_add, mul_one, ← mul_assoc, mul_comm (s i) t, mul_assoc,
              mul_inv_cancel₀ hne, mul_one]
            ring
          calc ∏ i, (t + s i) = ∏ i, (s i * (1 + t * (s i)⁻¹)) :=
                Finset.prod_congr rfl fun i _ => hterm i
            _ = (∏ i, s i) * ∏ i, (1 + t * (s i)⁻¹) :=
                Finset.prod_mul_distrib
        set tstar : ℝ := ((k : ℝ) + 1) / ((k : ℝ) * (∑ i, (s i)⁻¹)) with htstar
        have htstarpos : (0 : ℝ) < tstar := by
          apply div_pos hK1pos
          exact mul_pos hKpos hσpos
        set w : Option (Fin m) → ℝ := fun o => match o with
          | none => (k : ℝ) + 1 - (m : ℝ)
          | some _ => 1 with hwdef
        set z : Option (Fin m) → ℝ := fun o => match o with
          | none => 1
          | some i => 1 + tstar * (s i)⁻¹ with hzdef
        have hw_nonneg : ∀ o ∈ (Finset.univ : Finset (Option (Fin m))), 0 ≤ w o := by
          intro o _
          cases o with
          | none =>
            simp only [hwdef]
            have hcast : (m : ℝ) ≤ (k : ℝ) + 1 := by
              have : m ≤ k + 1 := hm
              have h1 : (m : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_le.mpr this
              rwa [Nat.cast_add, Nat.cast_one] at h1
            linarith
          | some i => simp [hwdef]
        have hsum_w : ∑ o ∈ (Finset.univ : Finset (Option (Fin m))), w o
            = (k : ℝ) + 1 := by
          rw [Fintype.sum_option]
          simp only [hwdef]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_one]
          ring
        have hsum_wpos : (0 : ℝ) < ∑ o ∈ (Finset.univ : Finset (Option (Fin m))), w o := by
          rw [hsum_w]
          exact hK1pos
        have hz_nonneg : ∀ o ∈ (Finset.univ : Finset (Option (Fin m))), 0 ≤ z o := by
          intro o _
          cases o with
          | none => simp [hzdef]
          | some i =>
            simp only [hzdef]
            have h1 : (0 : ℝ) ≤ tstar * (s i)⁻¹ := by
              apply mul_nonneg (le_of_lt htstarpos)
              exact le_of_lt (inv_pos.mpr (hs i))
            linarith
        have hprod_rw : (∏ o ∈ (Finset.univ : Finset (Option (Fin m))), z o ^ w o)
            = ∏ i, (1 + tstar * (s i)⁻¹) := by
          have hnone : z none ^ w none = 1 := by
            simp only [hzdef, hwdef]
            exact Real.one_rpow _
          have hsome : ∀ i : Fin m, z (some i) ^ w (some i)
              = 1 + tstar * (s i)⁻¹ := by
            intro i
            simp only [hzdef, hwdef]
            exact Real.rpow_one _
          rw [Fintype.prod_option, hnone, one_mul]
          exact Finset.prod_congr rfl fun i _ => hsome i
        have hsum_rw : (∑ o ∈ (Finset.univ : Finset (Option (Fin m))), w o * z o)
            = ((k : ℝ) + 1) + tstar * (∑ i, (s i)⁻¹) := by
          have hnone : w none * z none = ((k : ℝ) + 1 - (m : ℝ)) := by
            simp [hwdef, hzdef]
          have hsome : ∀ i : Fin m, w (some i) * z (some i)
              = 1 + tstar * (s i)⁻¹ := by
            intro i
            simp [hwdef, hzdef]
          have hsum_some : (∑ i : Fin m, (w (some i) * z (some i)))
              = (m : ℝ) + tstar * (∑ i, (s i)⁻¹) := by
            have hcongr : (∑ i : Fin m, (w (some i) * z (some i)))
                = ∑ i : Fin m, (1 + tstar * (s i)⁻¹) := by
              exact Finset.sum_congr rfl fun i _ => hsome i
            rw [hcongr, Finset.sum_add_distrib]
            have h1 : (∑ _i : Fin m, (1 : ℝ)) = (m : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul, mul_one]
            have h2 : (∑ i : Fin m, tstar * (s i)⁻¹)
                = tstar * (∑ i, (s i)⁻¹) := by
              rw [Finset.mul_sum]
            rw [h1, h2]
          rw [Fintype.sum_option, hnone, hsum_some]
          ring
        have hamgm := Real.geom_mean_le_arith_mean Finset.univ w z
          hw_nonneg hsum_wpos hz_nonneg
        rw [hprod_rw, hsum_rw, hsum_w] at hamgm
        have hPpos : (0 : ℝ) < ∏ i, (1 + tstar * (s i)⁻¹) := by
          apply Finset.prod_pos fun i _ => ?_
          have h1 : (0 : ℝ) < tstar * (s i)⁻¹ :=
            mul_pos htstarpos (inv_pos.mpr (hs i))
          linarith
        have hK1eq : ((k : ℝ) + 1) = (((k + 1 : ℕ)) : ℝ) := by
          rw [Nat.cast_add, Nat.cast_one]
        have hn_ne : k + 1 ≠ 0 := Nat.succ_ne_zero k
        have hQeq : ((k : ℝ) + 1 + tstar * (∑ i, (s i)⁻¹)) / ((k : ℝ) + 1)
            = ((k : ℝ) + 1) / (k : ℝ) := by
          have hσne : (∑ i, (s i)⁻¹) ≠ 0 := ne_of_gt hσpos
          have hKne : (k : ℝ) ≠ 0 := ne_of_gt hKpos
          have hK1ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hK1pos
          have htstar_mul : tstar * (∑ i, (s i)⁻¹) = ((k : ℝ) + 1) / (k : ℝ) := by
            rw [htstar, div_mul_eq_mul_div]
            exact mul_div_mul_right _ _ hσne
          rw [htstar_mul]
          field_simp
        have hPow : (∏ i, (1 + tstar * (s i)⁻¹))
            ≤ (((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1) := by
          have hle : ((∏ i, (1 + tstar * (s i)⁻¹)) ^ (((k : ℝ) + 1)⁻¹))
              ≤ ((k : ℝ) + 1) / (k : ℝ) := by
            rw [← hQeq]
            exact hamgm
          have hPeq : (∏ i, (1 + tstar * (s i)⁻¹))
              = (((∏ i, (1 + tstar * (s i)⁻¹)) ^ (((k : ℝ) + 1)⁻¹)) ^ (k + 1)) := by
            rw [hK1eq]
            exact (Real.rpow_inv_natCast_pow (le_of_lt hPpos) hn_ne).symm
          rw [hPeq]
          exact pow_le_pow_left₀ (Real.rpow_nonneg (le_of_lt hPpos) _) hle _
        have h_tstar := h tstar htstarpos
        rw [hprod_eq] at h_tstar
        have haP : (0 : ℝ) ≤ a * (∏ i, s i) :=
          mul_nonneg (le_of_lt ha) (le_of_lt hπpos)
        have h1 : b * tstar
            ≤ (a * (∏ i, s i)) * ((((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1)) := by
          have h1a : a * ((∏ i, s i) * ∏ i, (1 + tstar * (s i)⁻¹))
              = (a * (∏ i, s i)) * ∏ i, (1 + tstar * (s i)⁻¹) := by ring
          rw [h1a] at h_tstar
          exact le_trans h_tstar (mul_le_mul_of_nonneg_left hPow haP)
        have hσne : (∑ i, (s i)⁻¹) ≠ 0 := ne_of_gt hσpos
        have hKne : (k : ℝ) ≠ 0 := ne_of_gt hKpos
        have hK1ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hK1pos
        have hRinv_nonneg : (0 : ℝ) ≤ (((k : ℝ) / ((k : ℝ) + 1)) ^ (k + 1)) := by
          apply pow_nonneg
          exact div_nonneg (le_of_lt hKpos) (le_of_lt hK1pos)
        have hmult_nonneg : (0 : ℝ)
            ≤ (((k : ℝ) / ((k : ℝ) + 1)) ^ (k + 1)) * (∑ i, (s i)⁻¹) :=
          mul_nonneg hRinv_nonneg (le_of_lt hσpos)
        have h2 := mul_le_mul_of_nonneg_right h1 hmult_nonneg
        have hR_mul : ((((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1))
            * ((((k : ℝ) / ((k : ℝ) + 1))) ^ (k + 1)) = 1 := by
          rw [← mul_pow]
          have hdiv : ((k : ℝ) + 1) / (k : ℝ) * ((k : ℝ) / ((k : ℝ) + 1)) = 1 := by
            field_simp
          rw [hdiv, one_pow]
        have hRinv_succ : ((((k : ℝ) / ((k : ℝ) + 1))) ^ (k + 1))
            = ((((k : ℝ) / ((k : ℝ) + 1))) ^ k) * ((k : ℝ) / ((k : ℝ) + 1)) := by
          rw [pow_succ]
        have hT_eq : tstar * ((((k : ℝ) / ((k : ℝ) + 1))) ^ (k + 1))
            * (∑ i, (s i)⁻¹)
            = (((k : ℝ) / ((k : ℝ) + 1))) ^ k := by
          rw [hRinv_succ]
          have hT1 : tstar * ((k : ℝ) / ((k : ℝ) + 1))
              * (∑ i, (s i)⁻¹) = 1 := by
            rw [htstar]
            field_simp
            have hpos' : (0 : ℝ) < ∑ x, 1 / s x := by
              simpa [one_div] using hσpos
            exact div_self (ne_of_gt hpos')
          have : tstar * ((((k : ℝ) / ((k : ℝ) + 1)) ^ k)
              * ((k : ℝ) / ((k : ℝ) + 1))) * (∑ i, (s i)⁻¹)
              = ((((k : ℝ) / ((k : ℝ) + 1)) ^ k))
                * (tstar * ((k : ℝ) / ((k : ℝ) + 1)) * (∑ i, (s i)⁻¹)) := by
            ring
          rw [this, hT1, mul_one]
        have hLHS : (b * tstar)
            * ((((k : ℝ) / ((k : ℝ) + 1)) ^ (k + 1)) * (∑ i, (s i)⁻¹))
            = ((((k : ℝ) / ((k : ℝ) + 1))) ^ k) * b := by
          have : (b * tstar)
              * ((((k : ℝ) / ((k : ℝ) + 1)) ^ (k + 1)) * (∑ i, (s i)⁻¹))
              = b * (tstar * ((((k : ℝ) / ((k : ℝ) + 1))) ^ (k + 1))
                * (∑ i, (s i)⁻¹)) := by
            ring
          rw [this, hT_eq]
          ring
        have hRHS : ((a * (∏ i, s i))
            * ((((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1)))
            * ((((k : ℝ) / ((k : ℝ) + 1)) ^ (k + 1)) * (∑ i, (s i)⁻¹))
            = (a * (∏ i, s i)) * (∑ i, (s i)⁻¹) := by
          have : ((a * (∏ i, s i))
              * ((((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1)))
              * ((((k : ℝ) / ((k : ℝ) + 1)) ^ (k + 1)) * (∑ i, (s i)⁻¹))
              = (a * (∏ i, s i)) * (∑ i, (s i)⁻¹)
                * (((((k : ℝ) + 1) / (k : ℝ)) ^ (k + 1))
                  * ((((k : ℝ) / ((k : ℝ) + 1))) ^ (k + 1))) := by
            ring
          rw [this, hR_mul, mul_one]
        rw [hLHS, hRHS] at h2
        have hfinal : ((((k : ℝ) / ((k : ℝ) + 1))) ^ k) * b
            ≤ (a * (∏ i, s i)) * (∑ i, (s i)⁻¹) := h2
        have hmul_assoc : (a * (∏ i, s i)) * (∑ i, (s i)⁻¹)
            = a * (∑ i, ∏ j ∈ Finset.univ.erase i, s j) := by
          have hpi : (∏ i, s i) * (∑ i, (s i)⁻¹)
              = ∑ i, ∏ j ∈ Finset.univ.erase i, s j :=
            vdw_pi_mul_sigma hs
          calc (a * (∏ i, s i)) * (∑ i, (s i)⁻¹)
              = a * ((∏ i, s i) * (∑ i, (s i)⁻¹)) := by ring
            _ = a * (∑ i, ∏ j ∈ Finset.univ.erase i, s j) := by rw [hpi]
        rw [hmul_assoc] at hfinal
        exact hfinal

private lemma vdw_real_poly_eq_prod_of_roots_nonpos {f : Polynomial ℝ} (hf : f ≠ 0)
    (hr : ∀ z ∈ (Polynomial.map (algebraMap ℝ ℂ) f).roots, z.im = 0 ∧ z.re ≤ 0) :
    ∃ m : ℕ, ∃ s : Fin m → ℝ, m = f.natDegree ∧ (∀ i, 0 ≤ s i) ∧
      f = Polynomial.C f.leadingCoeff * ∏ i, (Polynomial.X + Polynomial.C (s i)) := by
  have hginj : Function.Injective (algebraMap ℝ ℂ) :=
    RingHom.injective (algebraMap ℝ ℂ)
  have heq := (IsAlgClosed.splits (Polynomial.map (algebraMap ℝ ℂ) f)).eq_prod_roots
  have hlc : (Polynomial.map (algebraMap ℝ ℂ) f).leadingCoeff
      = algebraMap ℝ ℂ f.leadingCoeff :=
    Polynomial.leadingCoeff_map _
  have hlc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  have hcard : (Polynomial.map (algebraMap ℝ ℂ) f).roots.card = f.natDegree :=
    IsAlgClosed.card_roots_map_eq_natDegree_of_injective f hginj
  have hcard' :
      Fintype.card (Polynomial.map (algebraMap ℝ ℂ) f).roots = f.natDegree := by
    rw [Multiset.card_coe]
    exact hcard
  set e : (Polynomial.map (algebraMap ℝ ℂ) f).roots ≃ Fin f.natDegree :=
    Fintype.equivFinOfCardEq hcard' with hedef
  have hmem : ∀ r : (Polynomial.map (algebraMap ℝ ℂ) f).roots,
      (((r : (Polynomial.map (algebraMap ℝ ℂ) f).roots) : ℂ)) ∈
        (Polynomial.map (algebraMap ℝ ℂ) f).roots := by
    intro r
    rw [← Multiset.count_pos]
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) r.2.isLt
  have hfactor : ∀ r : ℂ, r.im = 0 → r.re ≤ 0 →
      Polynomial.X - Polynomial.C r
        = Polynomial.map (algebraMap ℝ ℂ)
            (Polynomial.X + Polynomial.C (-r.re)) := by
    intro r him _
    have hcast : ((r.re : ℝ) : ℂ) = r := by
      apply Complex.ext_iff.mpr
      refine ⟨?_, ?_⟩ <;> simp [him]
    have hrR : algebraMap ℝ ℂ r.re = r := by
      rw [← hcast]
      simp
    have hneg : (algebraMap ℝ ℂ) (-r.re) = -r := by rw [map_neg, hrR]
    rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, hneg,
      sub_eq_add_neg, Polynomial.C_neg]
  have hprod : ((Polynomial.map (algebraMap ℝ ℂ) f).roots.map
        fun x => Polynomial.X - Polynomial.C x).prod
        = ∏ r : (Polynomial.map (algebraMap ℝ ℂ) f).roots,
            (Polynomial.X - Polynomial.C
              (((r : (Polynomial.map (algebraMap ℝ ℂ) f).roots) : ℂ))) := by
    rw [← Multiset.map_univ, Finset.prod_eq_multiset_prod]
  have hfin : ((Polynomial.map (algebraMap ℝ ℂ) f).roots.map
        fun x => Polynomial.X - Polynomial.C x).prod
        = ∏ i : Fin f.natDegree, Polynomial.map (algebraMap ℝ ℂ)
            (Polynomial.X + Polynomial.C
              (-(((((e.symm i : (Polynomial.map (algebraMap ℝ ℂ) f).roots)) : ℂ)).re))) := by
    rw [hprod]
    refine Fintype.prod_equiv e _ _ fun r => ?_
    show Polynomial.X - Polynomial.C (((r : _) : ℂ)) =
      Polynomial.map (algebraMap ℝ ℂ)
        (Polynomial.X + Polynomial.C (-((((e.symm (e r) : _) : ℂ)).re)))
    rw [Equiv.symm_apply_apply]
    exact hfactor _ (hr _ (hmem r)).1 (hr _ (hmem r)).2
  refine ⟨f.natDegree,
    fun i => -(((((e.symm i : (Polynomial.map (algebraMap ℝ ℂ) f).roots)) : ℂ)).re),
    rfl, fun i => ?_, ?_⟩
  · have h2 := (hr _ (hmem (e.symm i))).2
    simp only [neg_nonneg]
    exact h2
  · rw [hlc, hfin, ← Polynomial.map_prod, ← Polynomial.map_C,
      ← Polynomial.map_mul] at heq
    exact Polynomial.map_injective _ hginj heq

private lemma vdw_coeff_one_bound_of_roots_nonpos {k : ℕ} {f : Polynomial ℝ}
    (hdeg : f.natDegree ≤ k + 1) {b : ℝ} (hb : 0 ≤ b)
    (hr : ∀ z ∈ (Polynomial.map (algebraMap ℝ ℂ) f).roots, z.im = 0 ∧ z.re ≤ 0)
    (h : ∀ t : ℝ, 0 < t → b * t ≤ f.eval t) :
    ((k : ℝ) / ((k : ℝ) + 1)) ^ k * b ≤ f.coeff 1 := by
  by_cases hf0 : f = 0
  · subst hf0
    have hb0 : b = 0 := by
      have h1 := h 1 one_pos
      simp at h1
      linarith
    subst hb0
    simp
  · obtain ⟨m, s, hm_eq, hs, hf_eq⟩ :=
      vdw_real_poly_eq_prod_of_roots_nonpos hf0 hr
    have hm_le : m ≤ k + 1 := by omega
    have heval : ∀ u : ℝ, f.eval u = f.leadingCoeff * ∏ i, (u + s i) := by
      intro u
      conv_lhs => rw [hf_eq, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_prod]
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have hprod_pos : 0 < ∏ i, (1 + s i) :=
      Finset.prod_pos fun i _ => by linarith [hs i]
    have hlc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
    have hlc_pos : 0 < f.leadingCoeff := by
      have he1 := h 1 one_pos
      rw [mul_one, heval] at he1
      have hnn : (0 : ℝ) ≤ f.leadingCoeff * ∏ i, (1 + s i) := le_trans hb he1
      have hle : 0 ≤ f.leadingCoeff := nonneg_of_mul_nonneg_left hnn hprod_pos
      exact lt_of_le_of_ne hle (Ne.symm hlc_ne)
    have hN1 : ∀ δ : ℝ, 0 < δ →
        ((k : ℝ) / ((k : ℝ) + 1)) ^ k * b
          ≤ f.leadingCoeff * ∑ i, ∏ j ∈ Finset.univ.erase i, (s j + δ) := by
      intro δ hδ
      have hshift : ∀ t : ℝ, 0 < t →
          b * t ≤ f.leadingCoeff * ∏ i, (t + (s i + δ)) := by
        intro t ht
        have h1 : b * t ≤ b * (t + δ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ.le) hb
        have h2a := h (t + δ) (by linarith)
        rw [heval] at h2a
        have h3 : (∏ i, (t + δ + s i)) = ∏ i, (t + (s i + δ)) :=
          Finset.prod_congr rfl fun i _ => by ring
        rw [h3] at h2a
        exact le_trans h1 h2a
      exact vdw_amgm_prod_bound hm_le hlc_pos
        (fun i => add_pos_of_nonneg_of_pos (hs i) hδ) hshift
    have hcont : Continuous fun δ : ℝ =>
        f.leadingCoeff * ∑ i, ∏ j ∈ Finset.univ.erase i, (s j + δ) := by
      apply Continuous.mul continuous_const
      apply continuous_finsetSum _ fun i _ => ?_
      apply continuous_finsetProd _ fun j _ => ?_
      exact continuous_const.add continuous_id
    have hlim : Filter.Tendsto
        (fun δ : ℝ => f.leadingCoeff * ∑ i, ∏ j ∈ Finset.univ.erase i, (s j + δ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (f.leadingCoeff * ∑ i, ∏ j ∈ Finset.univ.erase i, (s j + 0))) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ((k : ℝ) / ((k : ℝ) + 1)) ^ k * b
          ≤ f.leadingCoeff * ∑ i, ∏ j ∈ Finset.univ.erase i, (s j + δ) := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact hN1 δ hδ
    have hle := ge_of_tendsto hlim hev
    simp only [add_zero] at hle
    have hcoeff : f.coeff 1
        = f.leadingCoeff * ∑ i, ∏ j ∈ Finset.univ.erase i, s j := by
      have hder : (∏ i, (Polynomial.X + Polynomial.C (s i))).derivative
          = ∑ i, ∏ j ∈ Finset.univ.erase i,
            (Polynomial.X + Polynomial.C (s j)) := by
        rw [Polynomial.derivative_prod_finset]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.derivative_X_add_C, mul_one]
      have h10 : (∏ i, (Polynomial.X + Polynomial.C (s i))).coeff 1
          = (∏ i, (Polynomial.X + Polynomial.C (s i))).derivative.coeff 0 := by
        have h10a := Polynomial.coeff_derivative
          (∏ i, (Polynomial.X + Polynomial.C (s i))) 0
        simpa using h10a.symm
      rw [hder, Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.eval_finsetSum] at h10
      have h0 : ∀ i : Fin m, (∏ j ∈ Finset.univ.erase i,
          (Polynomial.X + Polynomial.C (s j))).eval 0
          = ∏ j ∈ Finset.univ.erase i, s j := by
        intro i
        rw [Polynomial.eval_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]
      simp only [h0] at h10
      conv_lhs => rw [hf_eq, Polynomial.coeff_C_mul]
      rw [h10]
    rw [hcoeff]
    exact hle

private lemma vdw_isHomogeneous_aeval_smul {σ : Type*} {R S : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] {d : ℕ} {q : MvPolynomial σ R}
    (hq : q.IsHomogeneous d) (c : S) (z : σ → S) :
    MvPolynomial.aeval (fun i => c * z i) q = c ^ d * MvPolynomial.aeval z q := by
  rw [MvPolynomial.as_sum q, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hexp : ∑ i ∈ m.support, m i = d :=
    (hq.degree_eq_sum_deg_support hm).symm
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  change algebraMap R S (q.coeff m) * (∏ s ∈ m.support, (c * z s) ^ m s) =
    c ^ d * (algebraMap R S (q.coeff m) * (∏ s ∈ m.support, (z s) ^ m s))
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hexp]
  ring

private lemma vdw_finSuccEquiv_C {R : Type*} [CommSemiring R] {k : ℕ} (a : R) :
    MvPolynomial.finSuccEquiv R k (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
  simp [MvPolynomial.finSuccEquiv_apply]

private lemma vdw_aeval_cons_eq_eval_map_finSuccEquiv {R S : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] {k : ℕ} (q : MvPolynomial (Fin (k + 1)) R)
    (t : S) (z : Fin k → S) :
    MvPolynomial.aeval (Fin.cons t z) q =
      Polynomial.eval t
        (Polynomial.map (MvPolynomial.aeval z).toRingHom
          (MvPolynomial.finSuccEquiv R k q)) := by
  have hhom : (MvPolynomial.aeval (Fin.cons t z)).toRingHom =
      (Polynomial.evalRingHom t).comp
        ((Polynomial.mapRingHom (MvPolynomial.aeval z).toRingHom).comp
          (MvPolynomial.finSuccEquiv R k).toAlgHom.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [vdw_finSuccEquiv_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    · refine Fin.forall_iff_succ.mpr ⟨?_, ?_⟩
      · simp [MvPolynomial.aeval_X, Fin.cons_zero, MvPolynomial.finSuccEquiv_X_zero,
          Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom,
          Polynomial.eval_X]
      · intro i
        simp [MvPolynomial.aeval_X, Fin.cons_succ, MvPolynomial.finSuccEquiv_X_succ,
          Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom,
          Polynomial.eval_C]
  have hq := RingHom.congr_fun hhom q
  simpa [Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom] using hq

private lemma vdw_aeval_cons_zero_eq {R S : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] {k : ℕ} (q : MvPolynomial (Fin (k + 1)) R)
    (z : Fin k → S) :
    MvPolynomial.aeval (Fin.cons 0 z) q =
      MvPolynomial.aeval z (Polynomial.coeff (MvPolynomial.finSuccEquiv R k q) 0) := by
  rw [vdw_aeval_cons_eq_eval_map_finSuccEquiv, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_map]
  rfl

private lemma vdw_hstable_slice_roots_nonpos_real {k d : ℕ}
    {q : MvPolynomial (Fin (k + 1)) ℝ} (hq : q.IsHomogeneous d)
    (hH : vdw_HStable (k + 1) q) {x : Fin k → ℝ} (hx : ∀ i, 0 < x i) :
    ∀ t ∈ (Polynomial.map (algebraMap ℝ ℂ)
      (Polynomial.map (MvPolynomial.eval x) (MvPolynomial.finSuccEquiv ℝ k q))).roots,
      t.im = 0 ∧ t.re ≤ 0 := by
  intro t ht
  rw [Polynomial.mem_roots'] at ht
  obtain ⟨-, hroot⟩ := ht
  rw [Polynomial.IsRoot.def] at hroot
  have hmap : Polynomial.map (algebraMap ℝ ℂ)
        (Polynomial.map (MvPolynomial.eval x) (MvPolynomial.finSuccEquiv ℝ k q))
      = Polynomial.map (MvPolynomial.aeval (fun i => algebraMap ℝ ℂ (x i))).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q) := by
    rw [Polynomial.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp
  have key : MvPolynomial.aeval (Fin.cons t (fun i => algebraMap ℝ ℂ (x i))) q
      = 0 := by
    rw [vdw_aeval_cons_eq_eval_map_finSuccEquiv, ← hmap]
    exact hroot
  by_contra hcon
  have hcases : t.im ≠ 0 ∨ 0 < t.re := by
    by_contra hc
    push Not at hc
    exact hcon hc
  obtain ⟨ht0, hnorm⟩ : t ≠ 0 ∧ 0 < ‖t‖ + t.re := by
    rcases hcases with him | hre
    · refine ⟨fun h0 => him (by rw [h0]; exact Complex.zero_im), ?_⟩
      have habs : |t.re| < ‖t‖ := Complex.abs_re_lt_norm.mpr him
      rw [abs_lt] at habs
      linarith
    · refine ⟨?_, ?_⟩
      · intro h0
        rw [h0] at hre
        simp at hre
      · have hnn := norm_nonneg t
        linarith
  have hnpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have hlam_re : 0 < ((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)).re := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.conj_re]
    exact hnorm
  have hlamt_eq : ((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)) * t
      = ((‖t‖ : ℝ) : ℂ) * t + ((((‖t‖ ^ 2 : ℝ))) : ℂ) := by
    rw [add_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hlamt_re : 0 < (((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)) * t).re := by
    rw [hlamt_eq, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    have hfactor : ‖t‖ * t.re + ‖t‖ ^ 2 = ‖t‖ * (‖t‖ + t.re) := by ring
    rw [hfactor]
    exact mul_pos hnpos hnorm
  have hpt : ∀ i, (Fin.cons (α := fun _ => ℂ)
          ((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) * t)
        (fun i => (((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)
          * algebraMap ℝ ℂ (x i))) i
      = (((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) *
          Fin.cons (α := fun _ => ℂ) t (fun i => algebraMap ℝ ℂ (x i)) i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]
    · intro j
      simp only [Fin.cons_succ]
  have hscale : (Fin.cons ((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) * t)
        (fun i => (((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) * algebraMap ℝ ℂ (x i)))
      = (fun i => (((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) *
          Fin.cons (α := fun _ => ℂ) t (fun i => algebraMap ℝ ℂ (x i)) i) :=
    funext hpt
  have hpos : ∀ i, 0 < (Fin.cons (α := fun _ => ℂ)
          ((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) * t)
        (fun i => (((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)
          * algebraMap ℝ ℂ (x i)) i).re := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cons_zero]
      exact hlamt_re
    · intro j
      simp only [Fin.cons_succ]
      have hcoe : algebraMap ℝ ℂ (x j) = ((x j : ℝ) : ℂ) := by simp
      have hre2 : (((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)) * ((x j : ℝ) : ℂ)).re
          = ((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)).re * x j := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          sub_zero]
      rw [hcoe, hre2]
      exact mul_pos hlam_re (hx j)
  have hval : MvPolynomial.aeval
        (Fin.cons ((((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) * t)
          (fun i => (((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t)
            * algebraMap ℝ ℂ (x i))) q
      = (((‖t‖ : ℝ) : ℂ) + starRingEnd ℂ t) ^ d *
        MvPolynomial.aeval (Fin.cons t (fun i => algebraMap ℝ ℂ (x i))) q := by
    rw [hscale]
    exact vdw_isHomogeneous_aeval_smul hq _ _
  rw [key, mul_zero] at hval
  exact (hH _ hpos) hval

private lemma vdw_capacity_step {k : ℕ} {q : MvPolynomial (Fin (k + 1)) ℝ}
    (hq : q.IsHomogeneous (k + 1)) (hH : vdw_HStable (k + 1) q) {c : ℝ} (hc : 0 ≤ c)
    (hcap : vdw_CapBound (k + 1) q c) {y : Fin k → ℝ} (hy : ∀ i, 0 < y i) :
    ((k : ℝ) / ((k : ℝ) + 1)) ^ k * c * ∏ i, y i
      ≤ MvPolynomial.eval y (vdw_T k q) := by
  have hprod_pos : 0 < ∏ i, y i := Finset.prod_pos fun i _ => hy i
  have hb_nn : 0 ≤ c * ∏ i, y i := mul_nonneg hc (le_of_lt hprod_pos)
  have hdeg : (Polynomial.map (MvPolynomial.eval y)
      (MvPolynomial.finSuccEquiv ℝ k q)).natDegree ≤ k + 1 := by
    calc (Polynomial.map (MvPolynomial.eval y)
            (MvPolynomial.finSuccEquiv ℝ k q)).natDegree
        ≤ (MvPolynomial.finSuccEquiv ℝ k q).natDegree :=
          Polynomial.natDegree_map_le
      _ = MvPolynomial.degreeOf 0 q := MvPolynomial.natDegree_finSuccEquiv q
      _ ≤ q.totalDegree := MvPolynomial.degreeOf_le_totalDegree _ _
      _ ≤ k + 1 := hq.totalDegree_le
  have hr_slice : ∀ z ∈ (Polynomial.map (algebraMap ℝ ℂ)
        (Polynomial.map (MvPolynomial.eval y)
          (MvPolynomial.finSuccEquiv ℝ k q))).roots,
        z.im = 0 ∧ z.re ≤ 0 :=
    vdw_hstable_slice_roots_nonpos_real hq hH hy
  have hbound : ∀ t : ℝ, 0 < t → (c * ∏ i, y i) * t ≤
      (Polynomial.map (MvPolynomial.eval y)
        (MvPolynomial.finSuccEquiv ℝ k q)).eval t := by
    intro t ht
    have hpos_cons : ∀ i, 0 < Fin.cons (α := fun _ => ℝ) t y i := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        exact ht
      · intro j
        simp only [Fin.cons_succ]
        exact hy j
    have hcap_t := hcap (Fin.cons (α := fun _ => ℝ) t y) hpos_cons
    rw [MvPolynomial.eval_eq_eval_mv_eval'] at hcap_t
    have hpe : (∏ i, Fin.cons (α := fun _ => ℝ) t y i) = t * ∏ i, y i := by
      have h := Fin.prod_univ_succ (fun i => Fin.cons (α := fun _ => ℝ) t y i)
      simp only [Fin.cons_zero, Fin.cons_succ] at h
      exact h
    have hthis : c * ∏ i, Fin.cons (α := fun _ => ℝ) t y i
        = (c * ∏ i, y i) * t := by
      rw [hpe]
      ring
    rwa [hthis] at hcap_t
  have hN3 := vdw_coeff_one_bound_of_roots_nonpos hdeg hb_nn hr_slice hbound
  have hcoeff : (Polynomial.map (MvPolynomial.eval y)
      (MvPolynomial.finSuccEquiv ℝ k q)).coeff 1
      = MvPolynomial.eval y (vdw_T k q) := by
    unfold vdw_T
    rw [Polynomial.coeff_map]
  rw [hcoeff] at hN3
  calc ((k : ℝ) / ((k : ℝ) + 1)) ^ k * c * ∏ i, y i
      = ((k : ℝ) / ((k : ℝ) + 1)) ^ k * (c * ∏ i, y i) := by ring
    _ ≤ MvPolynomial.eval y (vdw_T k q) := hN3

private lemma vdw_T_isHomogeneous {k : ℕ} {q : MvPolynomial (Fin (k + 1)) ℝ}
    (hq : q.IsHomogeneous (k + 1)) : (vdw_T k q).IsHomogeneous k := by
  unfold vdw_T
  exact hq.finSuccEquiv_coeff_isHomogeneous 1 k (by omega)

private lemma vdw_ones_apply {k : ℕ} (i : Fin k) : vdw_ones k i = 1 := rfl

private lemma vdw_ones_degree {k : ℕ} : Finsupp.degree (vdw_ones k) = k := by
  simp [Finsupp.degree_eq_sum, vdw_ones_apply]

private lemma vdw_cons_ones {k : ℕ} :
    Finsupp.cons 1 (vdw_ones k) = vdw_ones (k + 1) := by
  ext i
  refine Fin.cases ?_ ?_ i <;>
    simp [Finsupp.cons_zero, Finsupp.cons_succ, vdw_ones_apply]

private lemma vdw_T_fullPos {k : ℕ} {q : MvPolynomial (Fin (k + 1)) ℝ}
    (hfp : vdw_FullPos (k + 1) (k + 1) q) :
    vdw_FullPos k k (vdw_T k q) := by
  intro m hm
  unfold vdw_T
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  apply hfp
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero]
  simp only [Finsupp.cons_succ]
  rw [← Finsupp.degree_eq_sum, hm, Nat.add_comm]

private lemma vdw_T_coeff_ones {k : ℕ} (q : MvPolynomial (Fin (k + 1)) ℝ) :
    (vdw_T k q).coeff (vdw_ones k) = q.coeff (vdw_ones (k + 1)) := by
  unfold vdw_T
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, vdw_cons_ones]

private lemma vdw_coeff_single_pos {k : ℕ} {q : MvPolynomial (Fin (k + 1)) ℝ}
    (hfp : vdw_FullPos (k + 1) (k + 1) q) :
    0 < q.coeff (Finsupp.single 0 (k + 1)) := by
  apply hfp
  rw [Finsupp.degree_single]

private lemma vdw_eval_ones_pos {k : ℕ} {p : MvPolynomial (Fin k) ℝ}
    (hp : p.IsHomogeneous k) (hfp : vdw_FullPos k k p) :
    0 < MvPolynomial.eval (fun _ => 1) p := by
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_pos (fun m hm => ?_) ?_
  · have hdeg : Finsupp.degree m = k := by
      rw [Finsupp.degree_apply]
      exact (hp.degree_eq_sum_deg_support hm).symm
    have hprod : (∏ i ∈ m.support, (1 : ℝ) ^ m i) = 1 := by simp
    rw [hprod, mul_one]
    exact hfp m hdeg
  · exact ⟨vdw_ones k, MvPolynomial.mem_support_iff.mpr
      (ne_of_gt (hfp _ vdw_ones_degree))⟩

private lemma vdw_hstable_D {k : ℕ} {q : MvPolynomial (Fin (k + 1)) ℝ}
    (hq : q.IsHomogeneous (k + 1))
    (hne : q.coeff (Finsupp.single 0 (k + 1)) ≠ 0)
    (hH : vdw_HStable (k + 1) q) :
    vdw_HStable (k + 1) (vdw_D k q) := by
  intro z hz
  have hu : 0 < (z 0).re := hz 0
  have hw : ∀ i, 0 < ((Fin.tail z) i).re := fun i => hz i.succ
  have hFeq : MvPolynomial.finSuccEquiv ℝ k (vdw_D k q)
      = Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ k q) := by
    unfold vdw_D
    exact AlgEquiv.apply_symm_apply _ _
  have hD_eval : ∀ t : ℂ, MvPolynomial.aeval (Fin.cons t (Fin.tail z)) (vdw_D k q)
      = (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
          (MvPolynomial.finSuccEquiv ℝ k q)).derivative.eval t := by
    intro t
    rw [vdw_aeval_cons_eq_eval_map_finSuccEquiv, hFeq, ← Polynomial.derivative_map]
  have hPcoeff : (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).coeff (k + 1)
      = (MvPolynomial.aeval (Fin.tail z)).toRingHom
          ((MvPolynomial.finSuccEquiv ℝ k q).coeff (k + 1)) :=
    Polynomial.coeff_map _ (k + 1)
  have hhom0 : ((MvPolynomial.finSuccEquiv ℝ k q).coeff (k + 1)).IsHomogeneous 0 :=
    hq.finSuccEquiv_coeff_isHomogeneous (k + 1) 0 (by omega)
  have htd0 : ((MvPolynomial.finSuccEquiv ℝ k q).coeff (k + 1)).totalDegree = 0 :=
    le_antisymm hhom0.totalDegree_le (Nat.zero_le _)
  have hCeq : (MvPolynomial.finSuccEquiv ℝ k q).coeff (k + 1)
      = MvPolynomial.C
          (((MvPolynomial.finSuccEquiv ℝ k q).coeff (k + 1)).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd0
  have hconst : ((MvPolynomial.finSuccEquiv ℝ k q).coeff (k + 1)).coeff 0
      = q.coeff (Finsupp.single 0 (k + 1)) := by
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_zero_eq_single_zero]
  have hPcoeff_ne : (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).coeff (k + 1) ≠ 0 := by
    rw [hPcoeff, hCeq, hconst]
    have hcast : (MvPolynomial.aeval (Fin.tail z)).toRingHom
          (MvPolynomial.C (q.coeff (Finsupp.single 0 (k + 1))))
        = algebraMap ℝ ℂ (q.coeff (Finsupp.single 0 (k + 1))) :=
      MvPolynomial.aeval_C _ _
    rw [hcast]
    have hcast2 : algebraMap ℝ ℂ (q.coeff (Finsupp.single 0 (k + 1)))
        = ((q.coeff (Finsupp.single 0 (k + 1)) : ℝ) : ℂ) := by simp
    rw [hcast2]
    simpa using hne
  have hPne : (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)) ≠ 0 :=
    fun h0 => hPcoeff_ne (by rw [h0]; exact Polynomial.coeff_zero _)
  have hle : k + 1 ≤ (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hPcoeff_ne
  have hdeg_pos : 0 < (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).degree := by
    have hpos : 0 < (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).natDegree := by omega
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hpos
  have hderiv_ne : (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by omega)
  have hroots : ∀ r ∈ (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).rootSet ℂ, r.re ≤ 0 := by
    intro r hr
    by_contra hcon
    push Not at hcon
    have hpos_r : ∀ i, 0 < (Fin.cons (α := fun _ => ℂ) r (Fin.tail z) i).re := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        exact hcon
      · intro j
        simp only [Fin.cons_succ]
        exact hw j
    have hr_eval : (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
          (MvPolynomial.finSuccEquiv ℝ k q)).eval r = 0 := by
      have h1 : Polynomial.aeval r _ = 0 :=
        (Polynomial.mem_rootSet_of_ne hPne).mp hr
      rwa [Polynomial.coe_aeval_eq_eval] at h1
    have heq_r := vdw_aeval_cons_eq_eval_map_finSuccEquiv q r (Fin.tail z)
    exact (hH _ hpos_r) (heq_r.trans hr_eval)
  have hGL : (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
        (MvPolynomial.finSuccEquiv ℝ k q)).derivative.rootSet ℂ
        ⊆ {w | w.re ≤ 0} := by
    have hsub := Polynomial.rootSet_derivative_subset_convexHull_rootSet hdeg_pos
    intro w hw_mem
    have hmem := hsub hw_mem
    have hsub2 : (Polynomial.map (MvPolynomial.aeval (Fin.tail z)).toRingHom
          (MvPolynomial.finSuccEquiv ℝ k q)).rootSet ℂ ⊆ {c : ℂ | c.re ≤ 0} :=
      fun r hr => hroots r hr
    exact convexHull_min hsub2 (convex_halfSpace_re_le (0 : ℝ)) hmem
  rw [← Fin.cons_self_tail z]
  intro hconD
  rw [hD_eval] at hconD
  have hconD' : Polynomial.aeval (z 0) (Polynomial.map
      (MvPolynomial.aeval (Fin.tail z)).toRingHom
      (MvPolynomial.finSuccEquiv ℝ k q)).derivative = 0 := by
    rw [Polynomial.coe_aeval_eq_eval]
    exact hconD
  have hmem := (Polynomial.mem_rootSet_of_ne hderiv_ne).mpr hconD'
  have hle0 := hGL hmem
  exact absurd hle0 (not_le_of_gt hu)

private lemma vdw_hstable_coeff_zero {k : ℕ} {D : MvPolynomial (Fin (k + 1)) ℝ}
    (hH : vdw_HStable (k + 1) D)
    (hne : MvPolynomial.eval (fun _ => 1)
      (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) ≠ 0) :
    vdw_HStable k (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) := by
  intro z' hz'
  set U : Set ℂ := {lam : ℂ | ∀ i, 0 < ((1 + lam * (z' i - 1) : ℂ)).re} with hUdef
  set F : ℝ → ℂ → ℂ := fun ep lam => MvPolynomial.aeval
    (Fin.cons (α := fun _ => ℂ) ((ep : ℝ) : ℂ)
      (fun i => 1 + lam * (z' i - 1))) D with hFdef
  set f : ℂ → ℂ := fun lam => MvPolynomial.aeval (fun i => 1 + lam * (z' i - 1))
    (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) with hfdef
  have hU_open : IsOpen U := by
    change IsOpen {lam : ℂ | ∀ i, 0 < ((1 + lam * (z' i - 1) : ℂ)).re}
    have heq : {lam : ℂ | ∀ i, 0 < ((1 + lam * (z' i - 1) : ℂ)).re}
        = ⋂ i, {lam : ℂ | (0 : ℝ) < ((1 + lam * (z' i - 1) : ℂ)).re} := by
      ext lam
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (Complex.continuous_re.comp
        (continuous_const.add (continuous_id.mul continuous_const)))
  have hw_convex : ∀ (a b : ℝ) (x y : ℂ), a + b = 1 →
      ∀ i, (1 + (a • x + b • y) * (z' i - 1) : ℂ)
        = a • (1 + x * (z' i - 1)) + b • (1 + y * (z' i - 1)) := by
    intro a b x y hab i
    have hb : b = 1 - a := by linarith
    subst hb
    simp only [Complex.real_smul]
    push_cast
    ring
  have hU_convex : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change ∀ i, 0 < ((1 + (a • x + b • y) * (z' i - 1) : ℂ)).re
    intro i
    have hx' : ∀ i, 0 < ((1 + x * (z' i - 1) : ℂ)).re := hx
    have hy' : ∀ i, 0 < ((1 + y * (z' i - 1) : ℂ)).re := hy
    rw [hw_convex a b x y hab i, Complex.add_re, Complex.smul_re,
      Complex.smul_re, smul_eq_mul, smul_eq_mul]
    have h1 := hx' i
    have h2 := hy' i
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      rw [hb1]
      simp only [zero_mul, zero_add, one_mul]
      exact h2
    · have hapos : 0 < a := by
        by_contra hc
        push Not at hc
        have hzero : a = 0 := le_antisymm hc ha
        exact ha0 hzero
      exact add_pos_of_pos_of_nonneg (mul_pos hapos h1) (mul_nonneg hb h2.le)
  have hU_preconn : IsPreconnected U := hU_convex.isPreconnected
  have f_eq : ∀ lam, F 0 lam = f lam := by
    intro lam
    change MvPolynomial.aeval
        (Fin.cons (α := fun _ => ℂ) (((0 : ℝ)) : ℂ)
          (fun i => 1 + lam * (z' i - 1))) D
        = MvPolynomial.aeval (fun i => 1 + lam * (z' i - 1))
          (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0)
    rw [show (((0 : ℝ)) : ℂ) = (0 : ℂ) from by simp, vdw_aeval_cons_zero_eq]
  have hΦcont : Continuous (Function.uncurry F) := by
    have hcoord : Continuous fun pl : ℝ × ℂ => Fin.cons (α := fun _ => ℂ)
        (((pl.1 : ℝ)) : ℂ) (fun i => 1 + pl.2 * (z' i - 1)) := by
      apply Continuous.finCons
      · exact Complex.continuous_ofReal.comp continuous_fst
      · exact continuous_pi fun i =>
          continuous_const.add (continuous_snd.mul continuous_const)
    have heq : Function.uncurry F
        = fun pl : ℝ × ℂ => MvPolynomial.eval
            (Fin.cons (α := fun _ => ℂ) (((pl.1 : ℝ)) : ℂ)
              (fun i => 1 + pl.2 * (z' i - 1)))
            ((MvPolynomial.map (algebraMap ℝ ℂ)) D) := by
      funext pl
      change MvPolynomial.aeval
          (Fin.cons (α := fun _ => ℂ) (((pl.1 : ℝ)) : ℂ)
            (fun i => 1 + pl.2 * (z' i - 1))) D = _
      rw [MvPolynomial.aeval_def, ← MvPolynomial.eval_map]
    rw [heq]
    exact (MvPolynomial.continuous_eval _).comp hcoord
  have hTLLU : TendstoLocallyUniformlyOn F f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU_open]
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hScompact : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
    have hUCont : UniformContinuousOn (Function.uncurry F)
        (Set.Icc (-1 : ℝ) 1 ×ˢ K) :=
      hScompact.uniformContinuousOn_of_continuous hΦcont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at hUCont
    obtain ⟨δ, hδ, hδU⟩ := hUCont ε hε
    have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
    have hminδ : min δ 1 ≤ δ := min_le_left _ _
    have hδ'pos : 0 < min δ 1 := lt_min hδ zero_lt_one
    have hball : Metric.ball (0 : ℝ) (min δ 1) ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds _ hδ'pos
    have hev_ball : ∀ᶠ ep in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ep ∈ Metric.ball (0 : ℝ) (min δ 1) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hball
    filter_upwards [hev_ball] with ep hep
    intro lam hlamK
    have hep_abs : |ep| < min δ 1 := by
      have h := Metric.mem_ball.mp hep
      rwa [Real.dist_eq, sub_zero] at h
    have hep1 : ep ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith [(abs_lt.mp hep_abs).1, hmin1],
        by linarith [(abs_lt.mp hep_abs).2, hmin1]⟩
    have hmem1 : (ep, lam) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ K := ⟨hep1, hlamK⟩
    have hmem2 : ((0 : ℝ), lam) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ K :=
      ⟨⟨by norm_num, by norm_num⟩, hlamK⟩
    have hdist : dist (ep, lam) ((0 : ℝ), lam) < δ := by
      rw [Prod.dist_eq, dist_self, max_lt_iff]
      refine ⟨?_, hδ⟩
      calc dist ep (0 : ℝ) = |ep| := by rw [Real.dist_eq, sub_zero]
        _ < δ := lt_of_lt_of_le hep_abs hminδ
    have h2 := hδU _ hmem1 _ hmem2 hdist
    rw [dist_comm (f lam) (F ep lam), ← f_eq lam]
    exact h2
  have han_ep : ∀ ep lam₀, AnalyticAt ℂ (F ep) lam₀ := by
    intro ep lam₀
    have hcoord : ∀ i, AnalyticAt ℂ
        (fun lam => (Fin.cons (α := fun _ => ℂ) (((ep : ℝ)) : ℂ)
          (fun j => 1 + lam * (z' j - 1))) i) lam₀ := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        exact analyticAt_const
      · intro j
        simp only [Fin.cons_succ]
        exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
    have h := AnalyticAt.aeval_mvPolynomial hcoord D
    exact h
  have hdiff : ∀ᶠ ep in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      DifferentiableOn ℂ (F ep) U := by
    filter_upwards with ep
    intro lam _
    exact ((han_ep ep lam).differentiableAt).differentiableWithinAt
  have hnevent : ∀ᶠ ep in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ lam ∈ U, F ep lam ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ep hep
    intro lam hlam
    have hlam' : ∀ i, 0 < ((1 + lam * (z' i - 1) : ℂ)).re := hlam
    have hpos : ∀ i, 0 < (Fin.cons (α := fun _ => ℂ) (((ep : ℝ)) : ℂ)
        (fun i => 1 + lam * (z' i - 1)) i).re := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        rw [Complex.ofReal_re]
        exact hep
      · intro j
        simp only [Fin.cons_succ]
        exact hlam' j
    exact hH _ hpos
  have h0U : (0 : ℂ) ∈ U := by
    change ∀ i, 0 < ((1 + (0 : ℂ) * (z' i - 1) : ℂ)).re
    intro i
    have h1 : (1 + (0 : ℂ) * (z' i - 1) : ℂ) = 1 := by ring
    rw [h1]
    simp
  have hw0eq : (fun i => 1 + (0 : ℂ) * (z' i - 1)) = (fun _ => 1) := by
    funext i
    ring
  have hwit0 : MvPolynomial.aeval (fun _ : Fin k => (1 : ℂ))
      (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) ≠ 0 := by
    have hw0 : (fun _ : Fin k => (1 : ℂ))
        = algebraMap ℝ ℂ ∘ (fun _ => (1 : ℝ)) := by
      funext i
      exact (map_one _).symm
    have hwit0 : MvPolynomial.aeval (fun _ : Fin k => (1 : ℂ))
        (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0)
        = algebraMap ℝ ℂ (MvPolynomial.eval (fun _ => (1 : ℝ))
          (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0)) := by
      rw [hw0, MvPolynomial.aeval_algebraMap_apply, MvPolynomial.aeval_eq_eval]
    rw [hwit0]
    have hcast2 : algebraMap ℝ ℂ (MvPolynomial.eval (fun _ => (1 : ℝ))
        (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0))
        = ((MvPolynomial.eval (fun _ => (1 : ℝ))
          (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) : ℝ) : ℂ) := by
      simp
    rw [hcast2]
    simpa using hne
  have hwit : ∃ lam ∈ U, f lam ≠ 0 := by
    refine ⟨0, h0U, ?_⟩
    have hfe : f 0 = MvPolynomial.aeval (fun _ : Fin k => (1 : ℂ))
        (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) := by
      change MvPolynomial.aeval (fun i => 1 + (0 : ℂ) * (z' i - 1))
          (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) = _
      rw [hw0eq]
    rw [hfe]
    exact hwit0
  have hconc := TendstoLocallyUniformlyOn.ne_zero_of_exists_ne_zero hTLLU hdiff
    hU_open hU_preconn hnevent hwit
  have h1U : (1 : ℂ) ∈ U := by
    change ∀ i, 0 < ((1 + (1 : ℂ) * (z' i - 1) : ℂ)).re
    intro i
    have h1 : (1 + (1 : ℂ) * (z' i - 1) : ℂ) = z' i := by ring
    rw [h1]
    exact hz' i
  have h1 := hconc 1 h1U
  have f1_eq : f 1 = MvPolynomial.aeval z'
      (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) := by
    change MvPolynomial.aeval (fun i => 1 + (1 : ℂ) * (z' i - 1))
        (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k D) 0) = _
    have hw1 : (fun i => 1 + (1 : ℂ) * (z' i - 1)) = z' := by
      funext i
      ring
    rw [hw1]
  rw [f1_eq] at h1
  exact h1

private lemma vdw_gurvits_induction (k : ℕ) : ∀ (q : MvPolynomial (Fin k) ℝ) (c : ℝ),
    q.IsHomogeneous k → vdw_HStable k q → vdw_FullPos k k q → 0 ≤ c →
    vdw_CapBound k q c →
    ((k.factorial : ℝ) / (k : ℝ) ^ k) * c ≤ q.coeff (vdw_ones k) := by
  induction k with
  | zero =>
    intro q c hhom hH hfp hc hcap
    have hC : q = MvPolynomial.C (q.coeff 0) :=
      MvPolynomial.eq_C_of_isEmpty q
    have hones : vdw_ones 0 = 0 := by
      ext i
      exact Fin.elim0 i
    have hcap0 := hcap (fun _ => (1 : ℝ)) (fun i => Fin.elim0 i)
    rw [hC, MvPolynomial.eval_C] at hcap0
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hcap0
    rw [hones]
    simpa using hcap0
  | succ k ih =>
    intro q c hhom hH hfp hc hcap
    have hThom : (vdw_T k q).IsHomogeneous k := vdw_T_isHomogeneous hhom
    have hTfp : vdw_FullPos k k (vdw_T k q) := vdw_T_fullPos hfp
    have hsingle : 0 < q.coeff (Finsupp.single 0 (k + 1)) :=
      vdw_coeff_single_pos hfp
    have hD : vdw_HStable (k + 1) (vdw_D k q) :=
      vdw_hstable_D hhom (ne_of_gt hsingle) hH
    have hTD : vdw_T k q =
        Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k (vdw_D k q)) 0 := by
      unfold vdw_D
      rw [AlgEquiv.apply_symm_apply]
      unfold vdw_T
      rw [Polynomial.coeff_derivative]
      simp
    have hne : MvPolynomial.eval (fun _ => 1)
        (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ k (vdw_D k q)) 0)
        ≠ 0 := by
      rw [← hTD]
      exact ne_of_gt (vdw_eval_ones_pos hThom hTfp)
    have hTH : vdw_HStable k (vdw_T k q) := by
      rw [hTD]
      exact vdw_hstable_coeff_zero hD hne
    have hg_nonneg : (0 : ℝ) ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ k := by
      apply pow_nonneg
      exact div_nonneg (Nat.cast_nonneg _) (by positivity)
    have hgc : (0 : ℝ) ≤ ((k : ℝ) / ((k : ℝ) + 1)) ^ k * c :=
      mul_nonneg hg_nonneg hc
    have hTcap : vdw_CapBound k (vdw_T k q) (((k : ℝ) / ((k : ℝ) + 1)) ^ k * c) := by
      intro y hy
      exact vdw_capacity_step hhom hH hc hcap hy
    have hIH := ih (vdw_T k q) (((k : ℝ) / ((k : ℝ) + 1)) ^ k * c)
      hThom hTH hTfp hgc hTcap
    rw [vdw_T_coeff_ones] at hIH
    have hscalar : ((k.factorial : ℝ) / (k : ℝ) ^ k)
          * (((k : ℝ) / ((k : ℝ) + 1)) ^ k)
        = (((k + 1).factorial : ℝ) / (((k + 1 : ℕ)) : ℝ) ^ (k + 1)) := by
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hK : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
        have hK1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hK1 : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hK1pos
        have hKk : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ hK
        have hK1k : ((k : ℝ) + 1) ^ k ≠ 0 := pow_ne_zero _ hK1
        have hK1s : ((k : ℝ) + 1) ^ (k + 1) ≠ 0 := pow_ne_zero _ hK1
        rw [Nat.factorial_succ, div_pow]
        push_cast
        field_simp
        ring
    have hfin : (((k + 1).factorial : ℝ) / (((k + 1 : ℕ)) : ℝ) ^ (k + 1)) * c
        = ((k.factorial : ℝ) / (k : ℝ) ^ k)
          * ((((k : ℝ) / ((k : ℝ) + 1)) ^ k) * c) := by
      rw [← hscalar]
      ring
    rw [hfin]
    exact hIH

private lemma vdw_prodColForms_isHomogeneous {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} :
    (vdw_p n A).IsHomogeneous n := by
  unfold vdw_p
  have h1 : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      (∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i).IsHomogeneous 1 := by
    intro j _
    apply MvPolynomial.IsHomogeneous.sum _ _ _
    intro i _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  have h2 := MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) h1
  simpa using h2

private lemma vdw_prodColForms_hstable {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 < A i j) :
    vdw_HStable n (vdw_p n A) := by
  intro z hz
  have hfactor : ∀ j : Fin n, MvPolynomial.aeval z
      (∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i) =
      ∑ i, algebraMap ℝ ℂ (A i j) * z i := by
    intro j
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  have hre_alg : ∀ r : ℝ, ∀ w : ℂ, (algebraMap ℝ ℂ r * w).re = r * w.re := by
    intro r w
    rw [RCLike.algebraMap_eq_ofReal]
    exact RCLike.re_ofReal_mul r w
  unfold vdw_p
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro j _
  rw [hfactor]
  have hre : 0 < (∑ i, algebraMap ℝ ℂ (A i j) * z i).re := by
    rw [Complex.re_sum]
    refine Finset.sum_pos (fun i _ => ?_) ?_
    · rw [hre_alg]
      exact mul_pos (hA i j) (hz i)
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  intro h0
  rw [h0, Complex.zero_re] at hre
  exact lt_irrefl _ hre

private lemma vdw_ell_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) (j : Fin n) (a : Fin n →₀ ℕ) :
    0 ≤ (∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i).coeff a := by
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  refine mul_nonneg (le_of_lt (hA i j)) ?_
  split_ifs <;> norm_num

private lemma vdw_ell_coeff_single {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (j i₀ : Fin n) :
    (∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i).coeff (Finsupp.single i₀ 1)
      = A i₀ j := by
  rw [MvPolynomial.coeff_sum]
  have hterm : ∀ i : Fin n, (MvPolynomial.C (A i j) * MvPolynomial.X i).coeff
      (Finsupp.single i₀ 1) = if i = i₀ then A i j else 0 := by
    intro i
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    by_cases hii : i = i₀
    · subst hii
      simp
    · have hne : Finsupp.single i 1 ≠ Finsupp.single i₀ 1 := by
        intro hcon
        exact hii ((Finsupp.single_left_inj one_ne_zero).mp hcon)
      simp [hne, hii]
  simp only [hterm]
  exact Fintype.sum_ite_eq' i₀ (fun x => A x j)

private lemma vdw_prod_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 < A i j) : ∀ S : Finset (Fin n), ∀ m : Fin n →₀ ℕ,
    0 ≤ (∏ j ∈ S, ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i).coeff m := by
  intro S
  induction S using Finset.induction with
  | empty =>
    intro m
    rw [Finset.prod_empty, MvPolynomial.coeff_one]
    split_ifs <;> norm_num
  | @insert j S hj ih =>
    intro m
    rw [Finset.prod_insert hj, MvPolynomial.coeff_mul]
    refine Finset.sum_nonneg fun x _ => ?_
    exact mul_nonneg (vdw_ell_nonneg hA j x.1) (ih x.2)

private lemma vdw_prodColForms_fullPos {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 < A i j) :
    vdw_FullPos n n (vdw_p n A) := by
  have key : ∀ S : Finset (Fin n), ∀ m : Fin n →₀ ℕ, Finsupp.degree m = S.card →
      0 < (∏ j ∈ S, ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X i).coeff m := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro m hm
      simp only [Finset.card_empty] at hm
      have hm0 : m = 0 := by
        rw [← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
        intro i hi
        exact (Finsupp.mem_support_iff.mp hi)
          (Nat.le_zero.mp (hm ▸ Finsupp.le_degree i m))
      subst hm0
      simp
    | @insert j S hj ih =>
      intro m hm
      have hcard : (insert j S).card = S.card + 1 :=
        Finset.card_insert_of_notMem hj
      rw [hcard] at hm
      rw [Finset.prod_insert hj, MvPolynomial.coeff_mul]
      have hmne : m ≠ 0 := by
        rintro rfl
        simp at hm
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∈ m.support := by
        by_contra hcon
        push Not at hcon
        have hempty : m.support = ∅ := Finset.eq_empty_of_forall_notMem hcon
        rw [Finsupp.support_eq_empty] at hempty
        exact hmne hempty
      have h1le : 1 ≤ m i₀ :=
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi₀)
      have hle : Finsupp.single i₀ 1 ≤ m := Finsupp.single_le_iff.mpr h1le
      have hadd : Finsupp.single i₀ 1 + (m - Finsupp.single i₀ 1) = m :=
        add_tsub_cancel_of_le hle
      have hdeg : Finsupp.degree (m - Finsupp.single i₀ 1) = S.card := by
        have h := congrArg Finsupp.degree hadd
        simp only [map_add, Finsupp.degree_single] at h
        omega
      have hmem : (Finsupp.single i₀ 1, m - Finsupp.single i₀ 1) ∈
          Finset.antidiagonal m := Finset.mem_antidiagonal.mpr hadd
      refine Finset.sum_pos' (fun x _ => mul_nonneg (vdw_ell_nonneg hA j x.1)
        (vdw_prod_nonneg hA S x.2)) ⟨_, hmem, ?_⟩
      show 0 < _ * _
      rw [vdw_ell_coeff_single]
      exact mul_pos (hA i₀ j) (ih _ hdeg)
  intro m hm
  have h := key Finset.univ m (by simpa using hm)
  simpa [vdw_p] using h

private lemma vdw_term_eq_monomial (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → Fin n) :
    (∏ j, MvPolynomial.C (A (x j) j) * MvPolynomial.X (x j)) =
      MvPolynomial.monomial (∑ j, Finsupp.single (x j) 1) (∏ j, A (x j) j) := by
  simp only [MvPolynomial.C_mul_X_eq_monomial]
  exact (MvPolynomial.monomial_sum_prod Finset.univ (fun j => Finsupp.single (x j) 1)
    (fun j => A (x j) j)).symm

private lemma vdw_expBij_iff (n : ℕ) (x : Fin n → Fin n) :
    ((∑ j, Finsupp.single (x j) 1) = vdw_ones n) ↔ Function.Bijective x := by
  constructor
  · intro hexp
    have hfib : ∀ i, (Finset.univ.filter (fun j => x j = i)).card = 1 := by
      intro i
      have h1 : ((∑ j, Finsupp.single (x j) 1) : Fin n →₀ ℕ) i = 1 := by
        rw [hexp]
        exact vdw_ones_apply i
      rw [Finsupp.finsetSum_apply] at h1
      simp only [Finsupp.single_apply] at h1
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact h1
    refine ⟨?_, ?_⟩
    · intro a b hab
      have ha : a ∈ Finset.univ.filter (fun j => x j = x a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hb : b ∈ Finset.univ.filter (fun j => x j = x a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩
      have h1 := hfib (x a)
      rw [Finset.card_eq_one] at h1
      obtain ⟨c, hc⟩ := h1
      rw [hc, Finset.mem_singleton] at ha hb
      exact ha.trans hb.symm
    · intro i
      have h1 := hfib i
      have hne : (Finset.univ.filter (fun j => x j = i)).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  · intro hbij
    obtain ⟨e, he⟩ : ∃ e : Equiv.Perm (Fin n), ⇑e = x :=
      ⟨Equiv.ofBijective x hbij, Equiv.coe_ofBijective x hbij⟩
    subst he
    ext i
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [vdw_ones_apply]
    refine Finset.sum_eq_single (e.symm i) (fun j _ hne => ?_)
      (fun h => absurd (Finset.mem_univ _) h) |>.trans ?_
    · have hne' : ⇑e j ≠ i :=
        fun hcon => hne (by rw [← hcon, Equiv.symm_apply_apply])
      simp [hne']
    · simp

private lemma vdw_coeff_ones_prodColForms_eq_permanent (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (vdw_p n A).coeff (vdw_ones n) = A.permanent := by
  have hcoeff : ∀ x : Fin n → Fin n,
      (∏ j, MvPolynomial.C (A (x j) j) * MvPolynomial.X (x j)).coeff (vdw_ones n) =
        if (∑ j, Finsupp.single (x j) 1) = vdw_ones n then ∏ j, A (x j) j
          else 0 := by
    intro x
    rw [vdw_term_eq_monomial, MvPolynomial.coeff_monomial]
  simp only [vdw_p, Matrix.permanent]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rw [MvPolynomial.coeff_sum]
  simp only [hcoeff, ← Finset.sum_filter]
  have him : Finset.univ.filter
        (fun x : Fin n → Fin n => (∑ j, Finsupp.single (x j) 1) = vdw_ones n) =
      Finset.univ.image (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_image.mpr ⟨Equiv.ofBijective x ((vdw_expBij_iff n x).mp hx.2),
        Finset.mem_univ _, Equiv.coe_ofBijective x _⟩
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨σ, _, hσ⟩ := hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hσ]
      exact (vdw_expBij_iff n _).mpr σ.bijective
  have hinj : Set.InjOn (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n))
      ↑(Finset.univ : Finset (Equiv.Perm (Fin n))) := by
    intro a _ b _ h
    apply Equiv.coe_fn_injective
    exact h
  rw [him, Finset.sum_image hinj]

private lemma vdw_capacity_prodColForms_ge_one {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n))
    {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    1 * ∏ i, x i ≤ MvPolynomial.eval x (vdw_p n A) := by
  have heval : MvPolynomial.eval x (vdw_p n A) = ∏ j, ∑ i, A i j * x i := by
    unfold vdw_p
    rw [MvPolynomial.eval_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [MvPolynomial.eval_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hcol : ∀ j : Fin n, ∏ i, x i ^ (A i j) ≤ ∑ i, A i j * x i := by
    intro j
    exact Real.geom_mean_le_arith_mean_weighted Finset.univ (fun i => A i j)
      (fun i => x i) (fun i _ => nonneg_of_mem_doublyStochastic hA)
      (sum_col_of_mem_doublyStochastic hA j) (fun i _ => le_of_lt (hx i))
  have hprod : ∏ j : Fin n, (∏ i, x i ^ (A i j)) ≤ ∏ j, (∑ i, A i j * x i) := by
    apply Finset.prod_le_prod₀
    · intro j _
      exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (le_of_lt (hx i)) _
    · intro j _
      exact hcol j
  have hswap : ∏ j : Fin n, (∏ i, x i ^ (A i j)) = ∏ i, x i := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_sum_of_pos (hx i)]
    rw [sum_row_of_mem_doublyStochastic hA i, Real.rpow_one]
  rw [one_mul, heval, ← hswap]
  exact hprod

private lemma vdw_permanent_ge_of_pos {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hpos : ∀ i j, 0 < A i j) :
    ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ A.permanent := by
  have hcap : vdw_CapBound n (vdw_p n A) 1 := fun x hx =>
    vdw_capacity_prodColForms_ge_one hA hx
  have h := vdw_gurvits_induction n (vdw_p n A) 1
    vdw_prodColForms_isHomogeneous (vdw_prodColForms_hstable hn hpos)
    (vdw_prodColForms_fullPos hpos) zero_le_one hcap
  rw [mul_one, vdw_coeff_ones_prodColForms_eq_permanent] at h
  exact h

end MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted

private noncomputable def vdw_J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => (n : ℝ)⁻¹

private lemma vdw_J_doublyStochastic {n : ℕ} (hn : 0 < n) :
    vdw_J n ∈ doublyStochastic ℝ (Fin n) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hpos : (0 : ℝ) ≤ (n : ℝ)⁻¹ := le_of_lt (inv_pos.mpr (Nat.cast_pos.mpr hn))
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun _ _ => hpos, ?_, ?_⟩ <;>
    intro i <;> simp only [vdw_J, Matrix.of_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hnR]

/--
The permanent of a doubly stochastic matrix is at least n! / n^n.
Source: G. P. Egorychev, Adv. Math. 42 (1981), 299-305, DOI 10.1016/0001-8708(81)90044-X; D. I.
Falikman, Math. Notes 29 (1981), 475-479, DOI 10.1007/BF01163285.

Proves `Wanted` entry `van_der_waerden_permanent`.
-/
public theorem van_der_waerden_permanent {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ A.permanent := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hnPos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
  have hJ := vdw_J_doublyStochastic hn
  have hcont : Continuous fun ε : ℝ => (((1 - ε) • A + ε • vdw_J n).permanent) := by
    unfold Matrix.permanent
    apply continuous_finsetSum _ fun σ _ => ?_
    apply continuous_finsetProd _ fun i _ => ?_
    have hentry : ∀ ε : ℝ, (((1 - ε) • A + ε • vdw_J n) (σ i) i)
        = (1 - ε) * A (σ i) i + ε * (n : ℝ)⁻¹ := by
      intro ε
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, vdw_J,
        Matrix.of_apply, smul_eq_mul, smul_eq_mul]
    simp_rw [hentry]
    apply Continuous.add
    · exact Continuous.mul (continuous_const.sub continuous_id) continuous_const
    · exact Continuous.mul continuous_id continuous_const
  have hlim : Filter.Tendsto (fun ε : ℝ => (((1 - ε) • A + ε • vdw_J n).permanent))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds A.permanent) := by
    have h0 : (((1 - (0 : ℝ)) • A + (0 : ℝ) • vdw_J n).permanent) = A.permanent := by
      simp
    rw [← h0]
    exact (hcont.tendsto _).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((n.factorial : ℝ) / (n : ℝ) ^ n)
        ≤ (((1 - ε) • A + ε • vdw_J n).permanent) := by
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hmem] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    have h1ε : (0 : ℝ) ≤ 1 - ε := by linarith
    have hεnn : (0 : ℝ) ≤ ε := le_of_lt hε0
    have hmem' : (1 - ε) • A + ε • vdw_J n ∈ doublyStochastic ℝ (Fin n) := by
      have hc : Convex ℝ ((doublyStochastic ℝ (Fin n)) :
          Set (Matrix (Fin n) (Fin n) ℝ)) := convex_doublyStochastic
      have ht : ε ∈ Set.Icc (0 : ℝ) 1 := ⟨hεnn, le_of_lt hε1⟩
      have hlm := hc.lineMap_mem hA hJ ht
      rw [AffineMap.lineMap_apply_module] at hlm
      simpa using hlm
    have hpos : ∀ i j, 0 < (((1 - ε) • A + ε • vdw_J n) i j) := by
      intro i j
      have hAij : (0 : ℝ) ≤ A i j := nonneg_of_mem_doublyStochastic hA
      have hentry : (((1 - ε) • A + ε • vdw_J n) i j)
          = (1 - ε) * A i j + ε * (n : ℝ)⁻¹ := by
        rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, vdw_J,
          Matrix.of_apply, smul_eq_mul, smul_eq_mul]
      rw [hentry]
      have h1 : (0 : ℝ) ≤ (1 - ε) * A i j := mul_nonneg h1ε hAij
      have h2 : (0 : ℝ) < ε * (n : ℝ)⁻¹ := mul_pos hε0 hnPos
      linarith
    exact vdw_permanent_ge_of_pos hn hmem' hpos
  exact ge_of_tendsto hlim hev

end MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted
