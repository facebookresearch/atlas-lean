/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry13Bernoulligen

namespace MetaMathlibExt

open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen

/-- Pair term from the Kachi–Tzermias product: for `K = k + 1`,
`1/2 - K * (2 * K - 1) * log (1 - 1 / (2 * K)) + K * (2 * K + 1) * log (1 - 1 / (2 * K + 1))`. -/
private noncomputable def z3pPairTerm (k : ℕ) : ℝ :=
  1 / 2 - ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) - 1) *
      Real.log (1 - 1 / (2 * ((k : ℝ) + 1))) +
    ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1) *
      Real.log (1 - 1 / (2 * ((k : ℝ) + 1) + 1))

/-- Weight function whose integral over `[0, 1]` is the sum of the pair terms. -/
private noncomputable def z3pWeight (t : ℝ) : ℝ :=
  (1 / 4) * (t * (1 - t) * Real.pi *
    (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)) - 2 * (1 - t))

private lemma z3p_integral_eq_pairTerm (k : ℕ) :
    ∫ t in (0 : ℝ)..1, (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2)) =
      z3pPairTerm k := by
  unfold z3pPairTerm
  set K : ℝ := (k : ℝ) + 1 with hKdef
  have hK1 : (1:ℝ) ≤ K := by
    have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith [hKdef]
  have hK0 : (0:ℝ) < K := by linarith
  have h2K : (0:ℝ) < 2 * K := by linarith
  set F : ℝ → ℝ := fun s : ℝ => s - s ^ 2 / 2
    + K * (1 - 2 * K) * (Real.log (2 * K - s) - Real.log (2 * K))
    - K * (1 + 2 * K) * (Real.log (2 * K + s) - Real.log (2 * K)) with hFdef
  have hmem : ∀ t ∈ Set.uIcc (0:ℝ) 1, (0:ℝ) ≤ t ∧ t ≤ 1 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact ⟨ht.1, ht.2⟩
  have hg1 : ∀ t ∈ Set.uIcc (0:ℝ) 1, (2:ℝ) * K - t ≠ 0 := by
    intro t ht
    obtain ⟨_, ht1⟩ := hmem t ht
    apply ne_of_gt
    have h2K2 : (2:ℝ) ≤ 2 * K := by linarith [hK1]
    linarith
  have hg2 : ∀ t ∈ Set.uIcc (0:ℝ) 1, (2:ℝ) * K + t ≠ 0 := by
    intro t ht
    obtain ⟨ht0, _⟩ := hmem t ht
    apply ne_of_gt
    have hKp : (0:ℝ) < 2 * K := h2K
    linarith
  have hin1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => 2 * K - s) (-1) t :=
    fun t => HasDerivAt.const_sub (2 * K) (hasDerivAt_id (x := t))
  have hin2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => 2 * K + s) 1 t := by
    intro t
    have h := HasDerivAt.const_add (2 * K) (hasDerivAt_id (x := t))
    simpa using h
  have hA : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - t) t := by
    intro t
    have h := HasDerivAt.sub (hasDerivAt_id (x := t))
      ((hasDerivAt_pow 2 t).div_const (2:ℝ))
    have heq : (1:ℝ) - (2:ℕ) * t ^ (2 - 1) / 2 = 1 - t := by
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
      ring
    rw [heq] at h
    exact h
  have hlogB : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => Real.log (2 * K - s) - Real.log (2 * K))
      ((-1) / (2 * K - t)) t := by
    intro t ht
    have h1 := HasDerivAt.log (hin1 t) (hg1 t ht)
    have h2 : HasDerivAt (fun _ : ℝ => Real.log (2 * K)) (0:ℝ) t :=
      hasDerivAt_const t _
    have h := h1.sub h2
    have heq : ((-1) / (2 * K - t) : ℝ) - 0 = (-1) / (2 * K - t) := sub_zero _
    rw [heq] at h
    exact h
  have hlogC : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => Real.log (2 * K + s) - Real.log (2 * K))
      ((1) / (2 * K + t)) t := by
    intro t ht
    have h1 := HasDerivAt.log (hin2 t) (hg2 t ht)
    have h2 : HasDerivAt (fun _ : ℝ => Real.log (2 * K)) (0:ℝ) t :=
      hasDerivAt_const t _
    have h := h1.sub h2
    have heq : ((1) / (2 * K + t) : ℝ) - 0 = (1) / (2 * K + t) := sub_zero _
    rw [heq] at h
    exact h
  have hB : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => K * (1 - 2 * K)
        * (Real.log (2 * K - s) - Real.log (2 * K)))
      (K * (1 - 2 * K) * ((-1) / (2 * K - t))) t := by
    intro t ht
    apply HasDerivAt.const_mul
    exact hlogB t ht
  have hC : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => K * (1 + 2 * K)
        * (Real.log (2 * K + s) - Real.log (2 * K)))
      (K * (1 + 2 * K) * ((1) / (2 * K + t))) t := by
    intro t ht
    apply HasDerivAt.const_mul
    exact hlogC t ht
  have hD : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt F
      ((1 - t) + K * (1 - 2 * K) * ((-1) / (2 * K - t))
        - K * (1 + 2 * K) * ((1) / (2 * K + t))) t := by
    intro t ht
    have h := HasDerivAt.sub (HasDerivAt.add (hA t) (hB t ht)) (hC t ht)
    rw [hFdef] at *
    exact h
  have dR : ∀ t ∈ Set.uIcc (0:ℝ) 1, t ^ 2 - 4 * K ^ 2 ≠ 0 := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := hmem t ht
    have htsq : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    have hKsq : (4:ℝ) ≤ 4 * K ^ 2 := by nlinarith [hK1]
    have hlt : t ^ 2 - 4 * K ^ 2 < 0 := by linarith
    exact ne_of_lt hlt
  have hDeq : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      (1 - t) + K * (1 - 2 * K) * ((-1) / (2 * K - t))
        - K * (1 + 2 * K) * ((1) / (2 * K + t))
        = (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * K ^ 2) := by
    intro t ht
    have g1 := hg1 t ht
    have g2 := hg2 t ht
    have hAB : (2 * K - t) * (2 * K + t) ≠ 0 := mul_ne_zero g1 g2
    have hneg : -((2 * K - t) * (2 * K + t)) ≠ 0 := neg_ne_zero.mpr hAB
    have hfac : t ^ 2 - 4 * K ^ 2 = -((2 * K - t) * (2 * K + t)) := by ring
    have cancel1 : ((-1 : ℝ) / (2 * K - t)) * (-((2 * K - t) * (2 * K + t)))
        = (2 * K + t) := by
      calc ((-1 : ℝ) / (2 * K - t)) * (-((2 * K - t) * (2 * K + t)))
          = (((-1) / (2 * K - t)) * (2 * K - t)) * (-(2 * K + t)) := by ring
        _ = (-1) * (-(2 * K + t)) := by rw [div_mul_cancel₀ _ g1]
        _ = 2 * K + t := by ring
    have cancel2 : ((1 : ℝ) / (2 * K + t)) * (-((2 * K - t) * (2 * K + t)))
        = -((2 * K - t)) := by
      calc ((1 : ℝ) / (2 * K + t)) * (-((2 * K - t) * (2 * K + t)))
          = (((1) / (2 * K + t)) * (2 * K + t)) * (-(2 * K - t)) := by ring
        _ = (1) * (-(2 * K - t)) := by rw [div_mul_cancel₀ _ g2]
        _ = -((2 * K - t)) := by ring
    have expand : ((1 - t) + K * (1 - 2 * K) * ((-1) / (2 * K - t))
        - K * (1 + 2 * K) * ((1) / (2 * K + t)))
        * (-((2 * K - t) * (2 * K + t)))
        = (1 - t) * (-((2 * K - t) * (2 * K + t)))
          + (K * (1 - 2 * K))
            * (((-1) / (2 * K - t)) * (-((2 * K - t) * (2 * K + t))))
          - (K * (1 + 2 * K))
            * (((1) / (2 * K + t)) * (-((2 * K - t) * (2 * K + t)))) := by
      ring
    have poly : (1 - t) * (-((2 * K - t) * (2 * K + t)))
        + (K * (1 - 2 * K)) * (2 * K + t)
        - (K * (1 + 2 * K)) * (-((2 * K - t))) = t ^ 2 - t ^ 3 := by
      ring
    have Lmul : ((1 - t) + K * (1 - 2 * K) * ((-1) / (2 * K - t))
        - K * (1 + 2 * K) * ((1) / (2 * K + t)))
        * (-((2 * K - t) * (2 * K + t))) = t ^ 2 - t ^ 3 := by
      rw [expand, cancel1, cancel2]
      exact poly
    rw [hfac, eq_div_iff hneg]
    exact Lmul
  have hderiv2 : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt F
      ((t ^ 2 - t ^ 3) / (t ^ 2 - 4 * K ^ 2)) t := by
    intro t ht
    rw [← hDeq t ht]
    exact hD t ht
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * K ^ 2))
      (Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.div
    · exact ((continuous_pow 2).sub (continuous_pow 3)).continuousOn
    · exact ((continuous_pow 2).sub continuous_const).continuousOn
    · intro t ht
      exact dR t ht
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * K ^ 2))
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable
  have hFTC : (∫ t in (0:ℝ)..1, (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * K ^ 2))
      = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 hint
  have e1 : Real.log (1 - 1 / (2 * K))
      = Real.log (2 * K - 1) - Real.log (2 * K) := by
    have h2Kne : (2:ℝ) * K ≠ 0 := ne_of_gt h2K
    have hA1 : (2:ℝ) * K - 1 ≠ 0 := ne_of_gt (by linarith [hK1])
    have harg : (1 - 1 / (2 * K) : ℝ) = (2 * K - 1) / (2 * K) := by
      field_simp
    rw [harg, Real.log_div hA1 h2Kne]
  have e2 : Real.log (1 - 1 / (2 * K + 1))
      = Real.log (2 * K) - Real.log (2 * K + 1) := by
    have hB0 : (2:ℝ) * K ≠ 0 := ne_of_gt h2K
    have hB1 : (2:ℝ) * K + 1 ≠ 0 := ne_of_gt (by linarith [hK0])
    have harg : (1 - 1 / (2 * K + 1) : ℝ) = (2 * K) / (2 * K + 1) := by
      field_simp
      ring
    rw [harg, Real.log_div hB0 hB1]
  have hF10 : F 1 - F 0
      = 1 / 2 - K * (2 * K - 1) * Real.log (1 - 1 / (2 * K))
        + K * (2 * K + 1) * Real.log (1 - 1 / (2 * K + 1)) := by
    have h0 : F 0 = 0 := by
      rw [hFdef]
      simp
    have h1 : F 1 = 1 - 1 ^ 2 / 2
        + K * (1 - 2 * K) * (Real.log (2 * K - 1) - Real.log (2 * K))
        - K * (1 + 2 * K) * (Real.log (2 * K + 1) - Real.log (2 * K)) := rfl
    rw [h0, h1, e1, e2]
    ring
  rw [hF10] at hFTC
  exact hFTC

private lemma z3p_hasSum_cot_partial_fraction {t : ℝ} (h0 : 0 < t) (h2 : t < 2) :
    HasSum (fun k : ℕ => 4 * t / (t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2)))
      (Real.pi * (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)) - 2 / t) := by
  have ht2 : (0:ℝ) < t / 2 ∧ t / 2 < 1 := by
    constructor <;> linarith
  have hz : (((t / 2 : ℝ)) : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    rw [Complex.intCast_re, Complex.ofReal_re] at hre
    have h1 : (0:ℤ) < n := by
      have h1r : (0:ℝ) < (n:ℝ) := by linarith
      exact_mod_cast h1r
    have h2n : n < (1:ℤ) := by
      have h2r : (n:ℝ) < 1 := by linarith
      exact_mod_cast h2r
    omega
  have hterm : ∀ k : ℕ, cotTerm ((((t / 2 : ℝ))) : ℂ) k
      = ((((4 * t / (t ^ 2 - 4 * ((k : ℝ) + 1) ^ 2) : ℝ))) : ℂ) := by
    intro k
    have hK : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have ha : ((k:ℂ)+1) = ((((k:ℝ)+1 : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_natCast, ← Complex.ofReal_add]
    have h2c : (2:ℂ) = ((((2:ℝ))) : ℂ) := (RCLike.ofReal_ofNat 2).symm
    rw [cotTerm_identity hz k]
    rw [ha, h2c, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub,
      ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_div,
      ← Complex.ofReal_mul, Complex.ofReal_inj]
    have hN1 : t / 2 + ((k:ℝ)+1) ≠ 0 := ne_of_gt (by linarith)
    have hN2 : t / 2 - ((k:ℝ)+1) ≠ 0 := ne_of_lt (by linarith)
    have hfac : t ^ 2 - 4 * ((k:ℝ)+1) ^ 2
        = (2 * (t / 2 - ((k:ℝ)+1))) * (2 * (t / 2 + ((k:ℝ)+1))) := by ring
    have d1 : (t / 2 + ((k:ℝ)+1)) * (t / 2 - ((k:ℝ)+1)) ≠ 0 :=
      mul_ne_zero hN1 hN2
    have d2 : t ^ 2 - 4 * ((k:ℝ)+1) ^ 2 ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hN2)
        (mul_ne_zero (by norm_num) hN1)
    rw [mul_one_div, div_eq_div_iff d1 d2]
    ring
  have earg : Real.pi * (t / 2) = Real.pi * t / 2 := by ring
  have e2 : (1:ℂ) / ((((t / 2 : ℝ))) : ℂ) = ((((2 / t : ℝ))) : ℂ) := by
    have ht0 : t ≠ 0 := ne_of_gt h0
    have e : (1 / (t / 2) : ℝ) = 2 / t := one_div_div t 2
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, e]
  have hval : (((Real.pi:ℝ)):ℂ) * Complex.cot ((((Real.pi:ℝ)):ℂ) * ((((t / 2 : ℝ))):ℂ))
      - 1 / ((((t / 2 : ℝ))):ℂ)
      = ((((Real.pi * (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2))
        - 2 / t : ℝ))) : ℂ) := by
    have e1 : (((Real.pi:ℝ)):ℂ) * ((((t / 2 : ℝ))):ℂ)
        = ((((Real.pi * (t / 2) : ℝ))) : ℂ) := (Complex.ofReal_mul _ _).symm
    rw [e1, ← Complex.ofReal_cot, ← Complex.ofReal_mul, Real.cot_eq_cos_div_sin,
      e2, ← Complex.ofReal_sub, Complex.ofReal_inj, earg]
  have hval_eq : (∑' n : ℕ, cotTerm ((((t / 2 : ℝ))) : ℂ) n)
      = (((Real.pi:ℝ)):ℂ) * Complex.cot ((((Real.pi:ℝ)):ℂ) * ((((t / 2 : ℝ))):ℂ))
        - 1 / ((((t / 2 : ℝ))):ℂ) := by
    unfold cotTerm
    exact (cot_series_rep' hz).symm
  have hsum := (summable_cotTerm hz).hasSum
  rw [hval_eq] at hsum
  have hsum3 := hsum.congr_fun (fun k => (hterm k).symm)
  rw [hval] at hsum3
  exact Complex.hasSum_ofReal.mp hsum3

private lemma z3p_hasSum_pairTerm_integral :
    HasSum z3pPairTerm (∫ t in (0 : ℝ)..1, z3pWeight t) := by
  have hmain : HasSum
      (fun k : ℕ => ∫ t in (0 : ℝ)..1, (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2)))
      (∫ t in (0 : ℝ)..1, z3pWeight t) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => 1 / (3 * (((k : ℝ) + 1) ^ 2))) ?_ ?_ ?_ ?_ ?_
    · intro k
      have hden : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
          t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2) ≠ 0 := by
        intro t ht
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Ioc] at ht
        obtain ⟨h0t, h1t⟩ := ht
        have hK1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
          have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have hprodK : (0 : ℝ) ≤ ((k : ℝ) + 1 - 1) * (((k : ℝ) + 1) + 1) :=
          mul_nonneg (by linarith) (by linarith)
        have hKsq : (1 : ℝ) ≤ (((k : ℝ) + 1) ^ 2) := by nlinarith [hprodK]
        have hprodt : (0 : ℝ) ≤ (1 - t) * (1 + t) :=
          mul_nonneg (by linarith) (by linarith)
        have htsq : t ^ 2 ≤ 1 := by nlinarith [hprodt]
        have hlt : t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2) < 0 := by linarith
        exact ne_of_lt hlt
      have hcont : ContinuousOn
          (fun t : ℝ => (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2)))
          (Set.uIoc (0 : ℝ) 1) := by
        apply ContinuousOn.div
        · exact ((continuous_pow 2).sub (continuous_pow 3)).continuousOn
        · exact ((continuous_pow 2).sub continuous_const).continuousOn
        · intro t ht
          exact hden t ht
      exact hcont.aestronglyMeasurable measurableSet_uIoc
    · intro k
      refine MeasureTheory.ae_of_all _ fun t htmem => ?_
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Ioc] at htmem
      obtain ⟨h0t, h1t⟩ := htmem
      have hK1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hnum : t ^ 2 - t ^ 3 = t ^ 2 * (1 - t) := by ring
      have hnum_nonneg : (0 : ℝ) ≤ t ^ 2 - t ^ 3 := by
        rw [hnum]
        exact mul_nonneg (sq_nonneg t) (by linarith)
      have hprodt : (0 : ℝ) ≤ (1 - t) * (1 + t) :=
        mul_nonneg (by linarith) (by linarith)
      have htsq : t ^ 2 ≤ 1 := by nlinarith [hprodt]
      have hnum_le : t ^ 2 - t ^ 3 ≤ 1 := by
        have ht3 : (0 : ℝ) ≤ t ^ 3 := pow_nonneg h0t.le 3
        linarith
      have hprodK : (0 : ℝ) ≤ ((k : ℝ) + 1 - 1) * (((k : ℝ) + 1) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      have hKsq : (1 : ℝ) ≤ (((k : ℝ) + 1) ^ 2) := by nlinarith [hprodK]
      have hden_pos : (0 : ℝ) < 4 * (((k : ℝ) + 1) ^ 2) - t ^ 2 := by linarith
      have hden_ge : 3 * (((k : ℝ) + 1) ^ 2)
          ≤ 4 * (((k : ℝ) + 1) ^ 2) - t ^ 2 := by linarith
      have hnorm : ‖(t ^ 2 - t ^ 3) / (t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2))‖
          = (t ^ 2 - t ^ 3) / (4 * (((k : ℝ) + 1) ^ 2) - t ^ 2) := by
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnum_nonneg,
          abs_of_neg (by linarith : t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2) < 0)]
        congr 1
        ring
      rw [hnorm,
        div_le_div_iff₀ hden_pos (by linarith : (0 : ℝ) < 3 * (((k : ℝ) + 1) ^ 2))]
      calc (t ^ 2 - t ^ 3) * (3 * (((k : ℝ) + 1) ^ 2))
          ≤ 1 * (3 * (((k : ℝ) + 1) ^ 2)) :=
            mul_le_mul_of_nonneg_right hnum_le (by linarith)
        _ ≤ 1 * (4 * (((k : ℝ) + 1) ^ 2) - t ^ 2) :=
            mul_le_mul_of_nonneg_left hden_ge (by norm_num)
    · have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
        (summable_nat_add_iff 1).mpr h2
      have hcast : (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2))
          = (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
        funext n
        rw [Nat.cast_add, Nat.cast_one]
      rw [hcast] at hshift
      have hscaled : Summable (fun k : ℕ => (1 / 3 : ℝ) * (1 / (((k : ℝ) + 1) ^ 2))) :=
        Summable.mul_left (1 / 3) hshift
      have heq : (fun k : ℕ => (1 : ℝ) / (3 * (((k : ℝ) + 1) ^ 2)))
          = (fun k : ℕ => (1 / 3 : ℝ) * (1 / (((k : ℝ) + 1) ^ 2))) := by
        funext k
        have hKpos : (0 : ℝ) < (k : ℝ) + 1 := by
          have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have hKne : ((k : ℝ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hKpos)
        field_simp
      refine MeasureTheory.ae_of_all _ fun t _ => ?_
      show Summable (fun k : ℕ => 1 / (3 * (((k : ℝ) + 1) ^ 2)))
      rw [heq]
      exact hscaled
    · exact intervalIntegrable_const
    · refine MeasureTheory.ae_of_all _ fun t htmem => ?_
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Ioc] at htmem
      obtain ⟨h0t, h1t⟩ := htmem
      have h2t : t < 2 := by linarith
      have hN2 := z3p_hasSum_cot_partial_fraction h0t h2t
      have hscaled := HasSum.mul_left (t * (1 - t) / 4) hN2
      have hD : ∀ k : ℕ, t ^ 2 - 4 * ((((k : ℝ) + 1) ^ 2)) ≠ 0 := by
        intro k
        have hK1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
          have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have hprodt : (0 : ℝ) ≤ (1 - t) * (1 + t) :=
          mul_nonneg (by linarith) (by linarith)
        have htsq : t ^ 2 ≤ 1 := by nlinarith [hprodt]
        have hprodK : (0 : ℝ) ≤ ((k : ℝ) + 1 - 1) * (((k : ℝ) + 1) + 1) :=
          mul_nonneg (by linarith) (by linarith)
        have hKsq : (1 : ℝ) ≤ (((k : ℝ) + 1) ^ 2) := by nlinarith [hprodK]
        have hlt : t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2) < 0 := by linarith
        exact ne_of_lt hlt
      have hterm : ∀ k : ℕ, (t * (1 - t) / 4)
          * (4 * t / (t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2)))
          = (t ^ 2 - t ^ 3) / (t ^ 2 - 4 * (((k : ℝ) + 1) ^ 2)) := by
        intro k
        have hDk := hD k
        field_simp
      have hval : (t * (1 - t) / 4) *
          (Real.pi * (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)) - 2 / t)
          = z3pWeight t := by
        have ht : t ≠ 0 := ne_of_gt h0t
        have e : (t * (1 - t) / 4) * (2 / t) = 2 * (1 - t) / 4 := by
          field_simp
        have e2 : (t * (1 - t) / 4) *
            (Real.pi * (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)) - 2 / t)
            = (t * (1 - t) / 4)
              * (Real.pi * (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)))
              - (t * (1 - t) / 4) * (2 / t) := by ring
        rw [e2, e]
        unfold z3pWeight
        ring
      have h2 := hscaled.congr_fun (fun k => (hterm k).symm)
      rwa [hval] at h2
  exact hmain.congr_fun (fun k => (z3p_integral_eq_pairTerm k).symm)

private lemma z3p_tsum_alternating_inv_cube :
    ∑' k : ℕ, (-1 : ℝ) ^ (k + 1) / ((((k + 1 : ℕ)) : ℝ)) ^ 3 =
      -(3 / 4) * (riemannZeta (3 : ℂ)).re := by
  have hsum_a : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hzeta : (riemannZeta (3 : ℂ)).re = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
    have h := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
    rw [Nat.cast_ofNat] at h
    have hsum_c : Summable (fun n : ℕ => ((((1 : ℝ) / (n : ℝ) ^ 3 : ℝ)) : ℂ)) :=
      Complex.summable_ofReal.mpr hsum_a
    have hre := Complex.hasSum_re hsum_c.hasSum
    have hterm : ∀ n : ℕ, ((((1 : ℝ) / (n : ℝ) ^ 3 : ℝ)) : ℂ).re
        = (1 : ℝ) / (n : ℝ) ^ 3 :=
      fun n => Complex.ofReal_re _
    have hbridge : (∑' n : ℕ, ((((1 : ℝ) / (n : ℝ) ^ 3 : ℝ)) : ℂ))
        = ∑' n : ℕ, (1 / (n : ℂ) ^ 3 : ℂ) := by
      apply tsum_congr
      intro n
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
        Complex.ofReal_natCast]
    have h2 := hre.tsum_eq
    rw [tsum_congr hterm, hbridge, ← h] at h2
    exact h2.symm
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    simp only at hab
    omega
  have hinj2o : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    simp only at hab
    omega
  have heven : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3) :=
    hsum_a.comp_injective hinj2
  have hodd : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3) :=
    hsum_a.comp_injective hinj2o
  have hscale : ∀ k : ℕ,
      (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3 = (1 / 8) * (1 / (k : ℝ) ^ 3) := by
    intro k
    have h2k : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [h2k]
    by_cases hk : (k : ℝ) = 0
    · simp [hk]
    · field_simp
      ring
  have heven_tsum : (∑' k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3)
      = (1 / 8) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
    rw [← tsum_mul_left]
    exact tsum_congr hscale
  have hodd_tsum : (∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3)
      = (7 / 8) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
    have h := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) heven hodd
    have h2 : (∑' k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3) +
        (∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3)
        = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := h
    rw [heven_tsum] at h2
    linarith [h2]
  have hb_even : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k) * (1 / ((2 * k : ℕ) : ℝ) ^ 3)
      = 1 / ((2 * k : ℕ) : ℝ) ^ 3 := by
    intro k
    rw [(even_two.mul_right k).neg_one_pow, one_mul]
  have hb_odd : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 1) * (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3)
      = -(1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3) := by
    intro k
    have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
    rw [hodd.neg_one_pow, neg_one_mul]
  have hb_sum : Summable (fun n : ℕ => (-1 : ℝ) ^ n * (1 / (n : ℝ) ^ 3)) :=
    hsum_a.alternating
  have hb_tsum : (∑' n : ℕ, (-1 : ℝ) ^ n * (1 / (n : ℝ) ^ 3))
      = -(3 / 4) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
    have h := tsum_even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n * (1 / (n : ℝ) ^ 3))
      (show Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k) *
        (1 / ((2 * k : ℕ) : ℝ) ^ 3)) from hb_sum.comp_injective hinj2)
      (show Summable (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) *
        (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3)) from hb_sum.comp_injective hinj2o)
    have h2 : (∑' k : ℕ, (-1 : ℝ) ^ (2 * k) * (1 / ((2 * k : ℕ) : ℝ) ^ 3)) +
        (∑' k : ℕ, (-1 : ℝ) ^ (2 * k + 1) * (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3))
        = ∑' n : ℕ, (-1 : ℝ) ^ n * (1 / (n : ℝ) ^ 3) := h
    have e1 : (∑' k : ℕ, (-1 : ℝ) ^ (2 * k) * (1 / ((2 * k : ℕ) : ℝ) ^ 3))
        = (1 / 8) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 := by
      have hsplit : (∑' k : ℕ, (-1 : ℝ) ^ (2 * k) * (1 / ((2 * k : ℕ) : ℝ) ^ 3))
          = ∑' k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3 := tsum_congr hb_even
      rw [hsplit]
      exact heven_tsum
    have e2 : (∑' k : ℕ, (-1 : ℝ) ^ (2 * k + 1) * (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3))
        = -((7 / 8) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3) := by
      have hsplit : (∑' k : ℕ, (-1 : ℝ) ^ (2 * k + 1) *
          (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3))
          = ∑' k : ℕ, -((1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3) := tsum_congr hb_odd
      rw [hsplit, tsum_neg, hodd_tsum]
    rw [e1, e2] at h2
    linarith [h2]
  have hshift : (∑' k : ℕ, (-1 : ℝ) ^ (k + 1) / ((((k + 1 : ℕ)) : ℝ)) ^ 3)
      = ∑' n : ℕ, (-1 : ℝ) ^ n * (1 / (n : ℝ) ^ 3) - (-1 : ℝ) ^ 0 * (1 / ((0 : ℕ) : ℝ) ^ 3) := by
    have hcongr : (∑' k : ℕ, (-1 : ℝ) ^ (k + 1) / ((((k + 1 : ℕ)) : ℝ)) ^ 3)
        = ∑' b : ℕ, (fun n : ℕ => (-1 : ℝ) ^ n * (1 / (n : ℝ) ^ 3)) (b + 1) := by
      apply tsum_congr
      intro k
      rw [div_eq_mul_one_div]
    rw [hcongr]
    have htail := hb_sum.tsum_eq_zero_add
    linarith [htail]
  have hzero : (-1 : ℝ) ^ 0 * (1 / ((0 : ℕ) : ℝ) ^ 3) = 0 := by norm_num
  rw [hshift, hb_tsum, hzeta, hzero, sub_zero]

private lemma z3p_pi_abs_lt :
    |Real.pi| < 2 * Real.pi := by
  rw [abs_of_pos Real.pi_pos]
  linarith [Real.pi_pos]

private lemma z3p_clausen_one_pi :
    MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen
      1 Real.pi = -Real.log 2 := by
  rw [MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen_one,
    Real.sin_pi_div_two]
  norm_num

private lemma z3p_clausen_two_pi :
    MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen
      2 Real.pi = 0 := by
  rw [MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen_of_two_le
      2 Real.pi (by norm_num)]
  have hz : ∀ k : ℕ,
      MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9ClausenTerm
        2 Real.pi k = 0 := by
    intro k
    unfold MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9ClausenTerm
    split_ifs with h
    · rw [Real.sin_nat_mul_pi, zero_div]
    · exact absurd ⟨1, rfl⟩ h
  simp [hz]

private lemma z3p_clausen_three_pi :
    MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen
      3 Real.pi = -(3 / 4) * (riemannZeta (3 : ℂ)).re := by
  rw [MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen_of_two_le
      3 Real.pi (by norm_num)]
  have hz : ∀ k : ℕ,
      MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9ClausenTerm
        3 Real.pi k
        = (-1 : ℝ) ^ (k + 1) / ((((k + 1 : ℕ)) : ℝ)) ^ 3 := by
    intro k
    unfold MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9ClausenTerm
    split_ifs with h
    · exfalso
      obtain ⟨r, hr⟩ := h
      omega
    · rw [Real.cos_nat_mul_pi]
  rw [tsum_congr hz]
  exact z3p_tsum_alternating_inv_cube

private lemma z3p_fact_two : Nat.factorial 2 = 2 := by decide

private lemma z3p_neg_one_pow_three : (-1 : ℝ) ^ (3 : ℕ) = -1 := by norm_num

private lemma z3p_entry13_one :
    IntervalIntegrable
      (MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Entry13Integrand
        1)
      MeasureTheory.volume 0 Real.pi ∧
      (∫ u in (0 : ℝ)..Real.pi,
        MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Entry13Integrand
          1 u) = Real.pi * Real.log 2 := by
  have h := ramanujan_part1_ch9_entry13_bernoulligen
    1 Real.pi (by norm_num) Real.pi_ne_zero z3p_pi_abs_lt
  refine ⟨h.1, ?_⟩
  have hcos : Real.cos (((1 : ℕ) : ℝ) * Real.pi / 2) = 0 := by
    rw [Nat.cast_one, one_mul, Real.cos_pi_div_two]
  have hr : Finset.range (1 + 1 : ℕ) = ({0, 1} : Finset ℕ) := by decide
  rw [h.2.2.2, hcos, hr, Finset.sum_insert (by decide),
    Finset.sum_singleton, show ((0 + 1 : ℕ)) = 1 from rfl,
    show ((1 + 1 : ℕ)) = 2 from rfl, show ((1 - 0 : ℕ)) = 1 from rfl,
    show ((1 - 1 : ℕ)) = 0 from rfl, show ((0 * 1 / 2 : ℕ)) = 0 from rfl,
    show ((1 * 2 / 2 : ℕ)) = 1 from rfl]
  simp only [pow_zero, pow_one, one_mul, mul_one, div_one, mul_zero, add_zero,
    zero_mul, Nat.cast_one, Nat.factorial_one,
    Nat.factorial_zero, z3p_clausen_one_pi, z3p_clausen_two_pi]
  ring

private lemma z3p_entry13_two :
    IntervalIntegrable
      (MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Entry13Integrand
        2)
      MeasureTheory.volume 0 Real.pi ∧
      (∫ u in (0 : ℝ)..Real.pi,
        MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Entry13Integrand
          2 u) = Real.pi ^ 2 * Real.log 2 - (7 / 2) * (riemannZeta (3 : ℂ)).re := by
  have h :=
    ramanujan_part1_ch9_entry13_bernoulligen
      2 Real.pi (by norm_num) Real.pi_ne_zero z3p_pi_abs_lt
  refine ⟨h.1, ?_⟩
  have hcos : Real.cos (((2 : ℕ) : ℝ) * Real.pi / 2) = -1 := by
    have e : ((2 : ℕ) : ℝ) * Real.pi / 2 = Real.pi := by push_cast; ring
    rw [e, Real.cos_pi]
  have e21 : ((2 + 1 : ℕ) : ℂ) = 3 := by norm_num
  have hr : Finset.range (2 + 1 : ℕ) = ({0, 1, 2} : Finset ℕ) := by decide
  rw [h.2.2.2, hcos, e21, hr, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show ((0 + 1 : ℕ)) = 1 from rfl, show ((1 + 1 : ℕ)) = 2 from rfl,
    show ((2 + 1 : ℕ)) = 3 from rfl, show ((0 * 1 / 2 : ℕ)) = 0 from rfl,
    show ((1 * 2 / 2 : ℕ)) = 1 from rfl, show ((2 * 3 / 2 : ℕ)) = 3 from rfl,
    show ((2 - 0 : ℕ)) = 2 from rfl, show ((2 - 1 : ℕ)) = 1 from rfl,
    show ((2 - 2 : ℕ)) = 0 from rfl]
  simp only [pow_zero, pow_one, one_mul, mul_one, div_one, mul_zero,
    Nat.cast_one, Nat.cast_ofNat, Nat.factorial_one, Nat.factorial_zero,
    z3p_fact_two, z3p_neg_one_pow_three, z3p_clausen_one_pi,
    z3p_clausen_two_pi, z3p_clausen_three_pi]
  ring

private lemma z3p_pointwise_cot (t : ℝ) :
    t * (1 - t) * Real.pi *
      (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2))
    = 2 * chapter9Entry13Integrand 1 (Real.pi * t)
      - (2 / Real.pi) * chapter9Entry13Integrand 2 (Real.pi * t) := by
  have e1 : 2 * ((Real.pi * t) ^ 1 / 2) = Real.pi * t := by ring
  have e2 : (2 / Real.pi) * ((Real.pi * t) ^ 2 / 2) = Real.pi * t ^ 2 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  unfold chapter9Entry13Integrand
  rw [show (2:ℝ) * ((Real.pi * t) ^ 1 / 2 *
      (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)))
      = (2 * ((Real.pi * t) ^ 1 / 2)) *
      (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)) from by ring,
    show (2 / Real.pi) * ((Real.pi * t) ^ 2 / 2 *
      (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)))
      = ((2 / Real.pi) * ((Real.pi * t) ^ 2 / 2)) *
      (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)) from by ring,
    e1, e2]
  ring

private lemma z3p_comp_one :
    IntervalIntegrable (fun t : ℝ => chapter9Entry13Integrand 1 (Real.pi * t))
      MeasureTheory.volume 0 1 := by
  have h := z3p_entry13_one.1.comp_mul_left (c := Real.pi)
  rwa [zero_div, div_self Real.pi_ne_zero] at h

private lemma z3p_comp_two :
    IntervalIntegrable (fun t : ℝ => chapter9Entry13Integrand 2 (Real.pi * t))
      MeasureTheory.volume 0 1 := by
  have h := z3p_entry13_two.1.comp_mul_left (c := Real.pi)
  rwa [zero_div, div_self Real.pi_ne_zero] at h

private lemma z3p_comp_val_one :
    (∫ t in (0 : ℝ)..1, chapter9Entry13Integrand 1 (Real.pi * t))
      = Real.pi⁻¹ * (Real.pi * Real.log 2) := by
  have h : (∫ t in (0 : ℝ)..1, chapter9Entry13Integrand 1 (Real.pi * t))
      = Real.pi⁻¹ • (∫ x in Real.pi * 0..Real.pi * 1,
        chapter9Entry13Integrand 1 x) :=
    intervalIntegral.integral_comp_mul_left _ Real.pi_ne_zero
  rw [mul_zero, mul_one, z3p_entry13_one.2, smul_eq_mul] at h
  exact h

private lemma z3p_comp_val_two :
    (∫ t in (0 : ℝ)..1, chapter9Entry13Integrand 2 (Real.pi * t))
      = Real.pi⁻¹ * (Real.pi ^ 2 * Real.log 2 - (7 / 2) * (riemannZeta (3 : ℂ)).re) := by
  have h : (∫ t in (0 : ℝ)..1, chapter9Entry13Integrand 2 (Real.pi * t))
      = Real.pi⁻¹ • (∫ x in Real.pi * 0..Real.pi * 1,
        chapter9Entry13Integrand 2 x) :=
    intervalIntegral.integral_comp_mul_left _ Real.pi_ne_zero
  rw [mul_zero, mul_one, z3p_entry13_two.2, smul_eq_mul] at h
  exact h

private lemma z3p_integral_t_one_sub_t_cot :
    IntervalIntegrable
      (fun t : ℝ => t * (1 - t) * Real.pi *
        (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)))
      MeasureTheory.volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, t * (1 - t) * Real.pi *
        (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2))) =
        7 * (riemannZeta (3 : ℂ)).re / Real.pi ^ 2 := by
  have hfun : (fun t : ℝ => t * (1 - t) * Real.pi *
        (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)))
      = (fun t : ℝ => 2 * chapter9Entry13Integrand 1 (Real.pi * t)
        - (2 / Real.pi) * chapter9Entry13Integrand 2 (Real.pi * t)) := by
    funext t
    exact z3p_pointwise_cot t
  have hcomb : IntervalIntegrable
      (fun t : ℝ => 2 * chapter9Entry13Integrand 1 (Real.pi * t)
        - (2 / Real.pi) * chapter9Entry13Integrand 2 (Real.pi * t))
      MeasureTheory.volume 0 1 :=
    (z3p_comp_one.const_mul 2).sub (z3p_comp_two.const_mul (2 / Real.pi))
  refine ⟨by rw [hfun]; exact hcomb, ?_⟩
  rw [hfun, intervalIntegral.integral_sub (z3p_comp_one.const_mul 2)
    (z3p_comp_two.const_mul (2 / Real.pi)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    z3p_comp_val_one, z3p_comp_val_two]
  have hpi : (Real.pi : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hpine : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

private lemma z3p_hasSum_pairTerm :
    HasSum z3pPairTerm (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4) := by
  have hval : (∫ t in (0 : ℝ)..1, z3pWeight t)
      = 7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4 := by
    have hfun : (fun t : ℝ => z3pWeight t)
        = (fun t : ℝ => (1 / 4 : ℝ) * ((t * (1 - t) * Real.pi *
          (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2))) - 2 * (1 - t))) := by
      funext t
      unfold z3pWeight
      ring
    have hcont2 : Continuous (fun t : ℝ => 2 * (1 - t)) :=
      continuous_const.mul (continuous_const.sub continuous_id)
    rw [hfun, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub z3p_integral_t_one_sub_t_cot.1
        (hcont2.intervalIntegrable 0 1),
      z3p_integral_t_one_sub_t_cot.2]
    have h2 : (∫ t in (0 : ℝ)..1, 2 * (1 - t)) = 1 := by
      have hfun2 : (fun t : ℝ => (2 : ℝ) * (1 - t)) = (fun t : ℝ => 2 - 2 * t) := by
        funext t
        ring
      have hcont3 : Continuous (fun t : ℝ => 2 * t) :=
        continuous_const.mul continuous_id
      rw [hfun2,
        intervalIntegral.integral_sub intervalIntegrable_const
          (hcont3.intervalIntegrable 0 1),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_id]
      norm_num
    rw [h2]
    ring
  rw [← hval]
  exact z3p_hasSum_pairTerm_integral

private lemma z3p_abs_log_one_add_inv_sub_le {u : ℝ} (hu : 2 ≤ u) :
    |Real.log (1 + 1 / u) - 1 / u + 1 / (2 * u ^ 2)| ≤ 2 / u ^ 3 := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hu0' : u ≠ 0 := ne_of_gt hu0
  have habs : |-1 / u| = 1 / u := by
    rw [show (-1 : ℝ) / u = -(1 / u) by ring, abs_neg,
      abs_of_pos (div_pos one_pos hu0)]
  have hxu : |-1 / u| < 1 := by
    rw [habs, div_lt_one hu0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -1 / u) hxu 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
  have e1 : (1 : ℝ) - -1 / u = 1 + 1 / u := by ring
  have e2 : (-1 / u) ^ (0 + 1) / ((((0 : ℕ)) : ℝ) + 1) = -1 / u := by norm_num
  have e3 : (-1 / u) ^ (1 + 1) / ((((1 : ℕ)) : ℝ) + 1) = 1 / (2 * u ^ 2) := by
    have hsq : (-1 / u) ^ (1 + 1) = 1 / u ^ 2 := by
      rw [show (1 + 1 : ℕ) = 2 from rfl]
      field_simp
    rw [hsq, show ((((1 : ℕ)) : ℝ) + 1) = 2 by norm_num, div_div]
    congr 1
    ring
  rw [e1, e2, e3] at h
  have hinv : (1 : ℝ) / u ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hu
  have hpos : (0 : ℝ) < 1 - 1 / u := by linarith
  have hRHS : |-1 / u| ^ (2 + 1) / (1 - |-1 / u|) ≤ 2 / u ^ 3 := by
    rw [habs]
    have hu3 : (0 : ℝ) < u ^ 3 := by positivity
    rw [div_le_div_iff₀ hpos hu3]
    have hcube : (1 / u : ℝ) ^ (2 + 1) * u ^ 3 = 1 := by
      rw [show (2 + 1 : ℕ) = 3 from rfl, div_pow, one_pow,
        div_mul_cancel₀ _ (ne_of_gt hu3)]
    rw [hcube]
    nlinarith [hinv, div_pos one_pos hu0, hpos]
  have hLHS : |(0 : ℝ) + -1 / u + 1 / (2 * u ^ 2) + Real.log (1 + 1 / u)|
      = |Real.log (1 + 1 / u) - 1 / u + 1 / (2 * u ^ 2)| := by
    congr 1
    ring
  rw [hLHS] at h
  exact h.trans hRHS

private lemma z3p_atTop_two_mul_add_one :
    Filter.Tendsto (fun m : ℕ => 2 * m + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  exact ⟨b, fun m hm => by omega⟩

private lemma z3p_bound_tendsto_zero (C : ℝ) :
    Filter.Tendsto (fun m : ℕ => C / ((2 * m + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) :=
  Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ).comp z3p_atTop_two_mul_add_one) C

private lemma z3p_aux_zero_a : Filter.Tendsto
    (fun m : ℕ => (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) *
      Real.log (1 + 1 / (2 * (m : ℝ) + 1)) - (m : ℝ) - 3 / 4)
    Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm'
    (a := fun m : ℕ => (9 / 4 : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ?_ ?_
  · rw [Filter.eventually_atTop]
    refine ⟨1, fun m hm => ?_⟩
    have hupos : (0:ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
      have h : 0 < 2 * m + 1 := by omega
      exact_mod_cast h
    have hu2 : (2:ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      have h : 2 ≤ 2 * m + 1 := by omega
      exact_mod_cast h
    have hu : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hmu : (m : ℝ) = (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 := by rw [hu]; ring
    have hD := z3p_abs_log_one_add_inv_sub_le (u := ((2 * m + 1 : ℕ) : ℝ)) hu2
    have hne : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hupos
    have hA_nonneg : (0:ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) *
        (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 := by positivity
    have hexpr : ((2 * m + 1 : ℕ) : ℝ) * ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2 + 1)
          * Real.log (1 + 1 / ((2 * m + 1 : ℕ) : ℝ))
          - (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 - 3 / 4
        = ((((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) / 2)
            * (Real.log (1 + 1 / ((2 * m + 1 : ℕ) : ℝ))
              - 1 / ((2 * m + 1 : ℕ) : ℝ)
              + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ) ^ 2)))
          - 1 / (4 * ((2 * m + 1 : ℕ) : ℝ)) := by
      have hnu2 : (2:ℝ) * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)
      have hnu4 : (4:ℝ) * ((2 * m + 1 : ℕ) : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num) hne
      field_simp
      ring
    have h4upos : (0:ℝ) < 4 * ((2 * m + 1 : ℕ) : ℝ) := by linarith
    have e : ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 *
          (2 / ((2 * m + 1 : ℕ) : ℝ) ^ 3)
        = (((2 * m + 1 : ℕ) : ℝ) + 1) / ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
      have hnu3 : ((2 * m + 1 : ℕ) : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hne
      field_simp
    have huu : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
      have hu1 : (1:ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by linarith
      calc ((2 * m + 1 : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) * 1 := (mul_one _).symm
        _ ≤ ((2 * m + 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hu1 (le_of_lt hupos)
        _ = ((2 * m + 1 : ℕ) : ℝ) ^ 2 := (pow_two _).symm
    have g1 : (((2 * m + 1 : ℕ) : ℝ) + 1) / ((2 * m + 1 : ℕ) : ℝ) ^ 2
        ≤ 2 / ((2 * m + 1 : ℕ) : ℝ) := by
      have h3 : (0:ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ h3 hupos]
      linarith [huu]
    have g2 : (1:ℝ) / (4 * ((2 * m + 1 : ℕ) : ℝ))
        ≤ (1 / 4) / ((2 * m + 1 : ℕ) : ℝ) := by
      rw [div_div]
    have g3 : (2:ℝ) / ((2 * m + 1 : ℕ) : ℝ)
        + (1 / 4) / ((2 * m + 1 : ℕ) : ℝ)
        = 9 / 4 / ((2 * m + 1 : ℕ) : ℝ) := by
      rw [← add_div]
      norm_num
    rw [← hu, hmu, hexpr]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg hA_nonneg,
      abs_of_pos (div_pos one_pos h4upos)]
    refine (add_le_add
      (mul_le_mul_of_nonneg_left hD hA_nonneg) le_rfl).trans ?_
    calc ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 *
            (2 / ((2 * m + 1 : ℕ) : ℝ) ^ 3) + 1 / (4 * ((2 * m + 1 : ℕ) : ℝ))
          = (((2 * m + 1 : ℕ) : ℝ) + 1) / ((2 * m + 1 : ℕ) : ℝ) ^ 2
            + 1 / (4 * ((2 * m + 1 : ℕ) : ℝ)) := by rw [e]
      _ ≤ 2 / ((2 * m + 1 : ℕ) : ℝ) + (1 / 4) / ((2 * m + 1 : ℕ) : ℝ) :=
          add_le_add g1 g2
      _ = 9 / 4 / ((2 * m + 1 : ℕ) : ℝ) := g3
  · exact z3p_bound_tendsto_zero (9 / 4)

private lemma z3p_aux_zero_b : Filter.Tendsto
    (fun m : ℕ => (m : ℝ) * (4 * (m : ℝ) + 5) *
      Real.log (1 + 1 / (2 * (m : ℝ) + 1)) - 2 * (m : ℝ) - 1)
    Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm'
    (a := fun m : ℕ => (13 / 2 : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ?_ ?_
  · rw [Filter.eventually_atTop]
    refine ⟨1, fun m hm => ?_⟩
    have hupos : (0:ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
      have h : 0 < 2 * m + 1 := by omega
      exact_mod_cast h
    have hu2 : (2:ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      have h : 2 ≤ 2 * m + 1 := by omega
      exact_mod_cast h
    have hu1 : (1:ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      have h : 1 ≤ 2 * m + 1 := by omega
      exact_mod_cast h
    have hu0 : (0:ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      have h : 0 ≤ 2 * m + 1 := by omega
      exact_mod_cast h
    have hu : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hmu : (m : ℝ) = (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 := by rw [hu]; ring
    have hD := z3p_abs_log_one_add_inv_sub_le (u := ((2 * m + 1 : ℕ) : ℝ)) hu2
    have hne : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hupos
    have hB_nonneg : (0:ℝ) ≤ (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 *
        (2 * ((2 * m + 1 : ℕ) : ℝ) + 3) := by
      apply mul_nonneg <;> linarith
    have hexpr_b : (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 *
          (4 * ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) + 5)
          * Real.log (1 + 1 / ((2 * m + 1 : ℕ) : ℝ))
          - 2 * ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) - 1
        = ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2 * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)
            * (Real.log (1 + 1 / ((2 * m + 1 : ℕ) : ℝ))
              - 1 / ((2 * m + 1 : ℕ) : ℝ)
              + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ) ^ 2)))
          - 7 / (4 * ((2 * m + 1 : ℕ) : ℝ))
          + 3 / (4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2) := by
      have hnu2 : (2:ℝ) * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)
      have hnu4 : (4:ℝ) * ((2 * m + 1 : ℕ) : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num) hne
      have hnu4sq : (4:ℝ) * ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)
      field_simp
      ring
    have h4upos : (0:ℝ) < 4 * ((2 * m + 1 : ℕ) : ℝ) := by linarith
    have h4sqpos : (0:ℝ) < 4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hB4 : (((2 * m + 1 : ℕ) : ℝ) - 1) * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)
        ≤ 4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (((2 * m + 1 : ℕ) : ℝ) - 1),
        sq_nonneg ((2 * m + 1 : ℕ) : ℝ), hu0, hu1]
    have eB : (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)
          * (2 / ((2 * m + 1 : ℕ) : ℝ) ^ 3)
        = ((((2 * m + 1 : ℕ) : ℝ) - 1) * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3))
          / ((2 * m + 1 : ℕ) : ℝ) ^ 3 := by
      have hnu3 : ((2 * m + 1 : ℕ) : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hne
      field_simp
    have gB : (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)
          * (2 / ((2 * m + 1 : ℕ) : ℝ) ^ 3)
        ≤ 4 / ((2 * m + 1 : ℕ) : ℝ) := by
      have h3 : (0:ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 3 := by positivity
      rw [eB, div_le_div_iff₀ h3 hupos]
      have hmul := mul_le_mul_of_nonneg_right hB4 hu0
      linarith [hmul]
    have huu : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
      calc ((2 * m + 1 : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) * 1 := (mul_one _).symm
        _ ≤ ((2 * m + 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hu1 (le_of_lt hupos)
        _ = ((2 * m + 1 : ℕ) : ℝ) ^ 2 := (pow_two _).symm
    have h323 : (3:ℝ) / (4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2)
        ≤ (3 / 4) / ((2 * m + 1 : ℕ) : ℝ) := by
      have h4sq : (0:ℝ) < 4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ h4sq hupos]
      linarith [huu]
    have eC : (7:ℝ) / (4 * ((2 * m + 1 : ℕ) : ℝ)) + (3 / 4) / ((2 * m + 1 : ℕ) : ℝ)
        = (5 / 2) / ((2 * m + 1 : ℕ) : ℝ) := by
      have hnu4 : (4:ℝ) * ((2 * m + 1 : ℕ) : ℝ) ≠ 0 :=
        mul_ne_zero (by norm_num) hne
      field_simp
      ring
    have gC : (7:ℝ) / (4 * ((2 * m + 1 : ℕ) : ℝ))
          + 3 / (4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2)
        ≤ (5 / 2) / ((2 * m + 1 : ℕ) : ℝ) := by
      rw [← eC]
      exact add_le_add le_rfl h323
    have gD : (4:ℝ) / ((2 * m + 1 : ℕ) : ℝ)
          + (5 / 2) / ((2 * m + 1 : ℕ) : ℝ)
        = 13 / 2 / ((2 * m + 1 : ℕ) : ℝ) := by
      rw [← add_div]
      norm_num
    rw [← hu, hmu, hexpr_b]
    refine ((norm_add_le _ _).trans ?_)
    refine ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
    have hsplit : ‖(((2 * m + 1 : ℕ) : ℝ) - 1) / 2 * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)
          * (Real.log (1 + 1 / ((2 * m + 1 : ℕ) : ℝ))
            - 1 / ((2 * m + 1 : ℕ) : ℝ)
            + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ) ^ 2))‖
        = ‖(((2 * m + 1 : ℕ) : ℝ) - 1) / 2 * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)‖
          * ‖Real.log (1 + 1 / ((2 * m + 1 : ℕ) : ℝ))
            - 1 / ((2 * m + 1 : ℕ) : ℝ)
            + 1 / (2 * ((2 * m + 1 : ℕ) : ℝ) ^ 2)‖ := norm_mul _ _
    rw [hsplit]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hB_nonneg,
      abs_of_pos (div_pos (by norm_num) h4upos),
      abs_of_pos (div_pos (by norm_num) h4sqpos)]
    refine (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hD hB_nonneg) le_rfl)
      le_rfl).trans ?_
    calc ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2 * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)
              * (2 / ((2 * m + 1 : ℕ) : ℝ) ^ 3)
              + 7 / (4 * ((2 * m + 1 : ℕ) : ℝ)))
            + 3 / (4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2)
          = ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2 * (2 * ((2 * m + 1 : ℕ) : ℝ) + 3)
              * (2 / ((2 * m + 1 : ℕ) : ℝ) ^ 3))
            + (7 / (4 * ((2 * m + 1 : ℕ) : ℝ))
              + 3 / (4 * ((2 * m + 1 : ℕ) : ℝ) ^ 2)) := add_assoc _ _ _
      _ ≤ 4 / ((2 * m + 1 : ℕ) : ℝ) + (5 / 2) / ((2 * m + 1 : ℕ) : ℝ) :=
          add_le_add gB gC
      _ = 13 / 2 / ((2 * m + 1 : ℕ) : ℝ) := gD
  · exact z3p_bound_tendsto_zero (13 / 2)

private lemma z3p_boundary_limits :
    Filter.Tendsto
      (fun m : ℕ => (2 * (m : ℝ) + 1) * ((m : ℝ) + 1) *
        Real.log (1 + 1 / (2 * (m : ℝ) + 1)) - (m : ℝ))
      Filter.atTop (nhds (3 / 4)) ∧
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) * (4 * (m : ℝ) + 5) *
        Real.log (1 + 1 / (2 * (m : ℝ) + 1)) - 2 * (m : ℝ))
      Filter.atTop (nhds 1) := by
  constructor
  · have h2 := (tendsto_const_nhds (x := (3 / 4 : ℝ))).add z3p_aux_zero_a
    rw [add_zero] at h2
    exact h2.congr (fun m => by ring)
  · have h2 := (tendsto_const_nhds (x := (1 : ℝ))).add z3p_aux_zero_b
    rw [add_zero] at h2
    exact h2.congr (fun m => by ring)

private lemma z3p_base_pos (n : ℕ) (hn : 1 ≤ n) :
    (0:ℝ) < 1 - 1 / ((n + 1 : ℕ) : ℝ) := by
  have h2 : (2:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have h : 2 ≤ n + 1 := by omega
    exact_mod_cast h
  have hlt : 1 / ((n + 1 : ℕ) : ℝ) < 1 := by
    calc 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) h2
      _ < 1 := by norm_num
  linarith

private lemma z3p_factor_eq_exp (n : ℕ) (hn : 1 ≤ n) :
    (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n)
      = Real.exp (((((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n : ℤ) : ℝ)
        * Real.log (1 - 1 / ((n + 1 : ℕ) : ℝ))) := by
  have h := z3p_base_pos n hn
  have hlog : Real.log ((1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
        (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
      = (((((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n : ℤ) : ℝ)
        * Real.log (1 - 1 / ((n + 1 : ℕ) : ℝ))) :=
    Real.log_zpow _ _
  have h2 := congrArg Real.exp hlog
  rw [Real.exp_log (zpow_pos h _)] at h2
  exact h2

private lemma z3p_pairTerm_succ (m : ℕ) :
    z3pPairTerm m = 1 / 2 - ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) *
      Real.log (1 - 1 / (2 * (m : ℝ) + 2)) +
      ((m : ℝ) + 1) * (2 * (m : ℝ) + 3) *
      Real.log (1 - 1 / (2 * (m : ℝ) + 3)) := by
  unfold z3pPairTerm
  have hK : (2:ℝ) * ((m : ℝ) + 1) = 2 * (m : ℝ) + 2 := by ring
  have hK2 : (2:ℝ) * (m : ℝ) + 2 + 1 = 2 * (m : ℝ) + 3 := by ring
  rw [hK, hK2]
  ring

private lemma z3p_T_one (m : ℕ) : ((2 * m + 1) * ((2 * m + 1) + 1) / 2 : ℕ)
    = (2 * m + 1) * (m + 1) := by
  have h : (2 * m + 1) * ((2 * m + 1) + 1) = 2 * ((2 * m + 1) * (m + 1)) := by
    ring
  rw [h]
  exact Nat.mul_div_cancel_left _ (by norm_num)

private lemma z3p_T_two (m : ℕ) : ((2 * m + 2) * ((2 * m + 2) + 1) / 2 : ℕ)
    = (m + 1) * (2 * m + 3) := by
  have h : (2 * m + 2) * ((2 * m + 2) + 1) = 2 * ((m + 1) * (2 * m + 3)) := by
    ring
  rw [h]
  exact Nat.mul_div_cancel_left _ (by norm_num)

private lemma z3p_sign_one (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 :=
  Odd.neg_one_pow ⟨m, rfl⟩

private lemma z3p_sign_two (m : ℕ) : (-1 : ℤ) ^ (2 * m + 2) = 1 :=
  Even.neg_one_pow ⟨m + 1, by ring⟩

private lemma z3p_base_one (m : ℕ) :
    ((2 * m + 1 + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 2 := by push_cast; ring

private lemma z3p_base_two (m : ℕ) :
    ((2 * m + 2 + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 3 := by push_cast; ring

private lemma z3p_prod_even_eq_exp (m : ℕ) :
    ∏ n ∈ Finset.Icc 1 (2 * m),
        (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
          (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n) =
      Real.exp ((∑ k ∈ Finset.range m, z3pPairTerm k) - (m : ℝ) / 2) := by
  induction m with
  | zero =>
    have hz : (2:ℕ) * 0 = 0 := by ring
    rw [hz, Finset.Icc_eq_empty_of_lt (by norm_num), Finset.prod_empty,
      Finset.sum_range_zero]
    simp
  | succ m ih =>
    have h2m : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h2m, Finset.prod_Icc_succ_top (show 1 ≤ 2 * m + 1 + 1 by omega),
      Finset.prod_Icc_succ_top (show 1 ≤ 2 * m + 1 by omega), ih,
      z3p_factor_eq_exp (2 * m + 1) (by omega),
      z3p_factor_eq_exp (2 * m + 2) (by omega),
      z3p_T_one m, z3p_T_two m, z3p_sign_one m, z3p_sign_two m,
      z3p_base_one m, z3p_base_two m,
      ← Real.exp_add, ← Real.exp_add, Finset.sum_range_succ, z3p_pairTerm_succ]
    congr 1
    push_cast
    ring

private lemma z3p_ratio_factor (m : ℕ) :
    ((((2 * m + 2 : ℕ) : ℝ) ^ ((2 * m + 2 : ℕ) ^ 2)) /
      ((((2 * m + 1 : ℕ) : ℝ)) ^ ((2 * m + 1 : ℕ) ^ 2)))
      = Real.exp (((((2 * m + 2 : ℕ) : ℝ)) ^ 2) *
        Real.log (((2 * m + 2 : ℕ) : ℝ))
        - ((((2 * m + 1 : ℕ) : ℝ)) ^ 2) *
        Real.log (((2 * m + 1 : ℕ) : ℝ))) := by
  have hpos1 : (0:ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by
    have h : 0 < 2 * m + 2 := by omega
    exact_mod_cast h
  have hpos2 : (0:ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
    have h : 0 < 2 * m + 1 := by omega
    exact_mod_cast h
  have hdiv : (0:ℝ) < ((((2 * m + 2 : ℕ) : ℝ) ^ ((2 * m + 2 : ℕ) ^ 2)) /
      ((((2 * m + 1 : ℕ) : ℝ)) ^ ((2 * m + 1 : ℕ) ^ 2))) :=
    div_pos (pow_pos hpos1 _) (pow_pos hpos2 _)
  conv_lhs => rw [← Real.exp_log hdiv]
  congr 1
  rw [Real.log_div (pow_ne_zero _ (ne_of_gt hpos1))
    (pow_ne_zero _ (ne_of_gt hpos2)), Real.log_pow, Real.log_pow,
    Nat.cast_pow, Nat.cast_pow]

private lemma z3p_log_sub_one (m : ℕ) :
    Real.log (1 - 1 / (2 * (m : ℝ) + 2))
      = Real.log (2 * (m : ℝ) + 1) - Real.log (2 * (m : ℝ) + 2) := by
  have hne : (2:ℝ) * (m : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  have hne1 : (2:ℝ) * (m : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have harg : (1:ℝ) - 1 / (2 * (m : ℝ) + 2)
      = (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) := by
    field_simp
    ring
  rw [harg, Real.log_div hne1 hne]

private lemma z3p_log_sub_two (m : ℕ) :
    Real.log (1 - 1 / (2 * (m : ℝ) + 3))
      = Real.log (2 * (m : ℝ) + 2) - Real.log (2 * (m : ℝ) + 3) := by
  have hne : (2:ℝ) * (m : ℝ) + 3 ≠ 0 := ne_of_gt (by positivity)
  have hne1 : (2:ℝ) * (m : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  have harg : (1:ℝ) - 1 / (2 * (m : ℝ) + 3)
      = (2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 3) := by
    field_simp
    ring
  rw [harg, Real.log_div hne1 hne]

private lemma z3p_ratio_prod_eq_exp (m : ℕ) :
    ((∏ n ∈ Finset.Icc 1 m, (((2 * n : ℕ) : ℝ) ^ ((2 * n : ℕ) ^ 2))) /
      (∏ n ∈ Finset.Icc 1 m, (((2 * n - 1 : ℕ) : ℝ) ^ ((2 * n - 1 : ℕ) ^ 2)))) =
      Real.exp ((∑ k ∈ Finset.range m, z3pPairTerm k) - (m : ℝ) / 2 +
        (m : ℝ) * (2 * (m : ℝ) + 1) * Real.log (((2 * m + 1 : ℕ) : ℝ))) := by
  induction m with
  | zero =>
    have hempty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty_of_lt (by norm_num)
    have e0 : ((2 * 0 + 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hempty, Finset.prod_empty, Finset.prod_empty, Finset.sum_range_zero, e0,
      Real.log_one]
    simp
  | succ m ih =>
    have e2 : 2 * (m + 1) = 2 * m + 2 := by ring
    have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have eb : ((2 * (m + 1) + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 3 := by
      push_cast; ring
    rw [Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega) _,
      Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega) _,
      e1, eb, e2, ← div_mul_div_comm, ih, z3p_ratio_factor m,
      ← Real.exp_add, Finset.sum_range_succ]
    congr 1
    push_cast
    rw [z3p_pairTerm_succ m, z3p_log_sub_one m, z3p_log_sub_two m]
    ring

private lemma z3p_third_factor (m : ℕ) :
    (((((2 * m + 2 : ℕ) : ℝ) ^ (4 * m + 5)) /
      ((((2 * m + 1 : ℕ) : ℝ) ^ (12 * m + 9)))) ^ m)
      = Real.exp ((m : ℝ) * (((4 * (m : ℝ) + 5) *
        Real.log (((2 * m + 2 : ℕ) : ℝ)))
        - ((12 * (m : ℝ) + 9) * Real.log (((2 * m + 1 : ℕ) : ℝ))))) := by
  have hpos1 : (0:ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by
    have h : 0 < 2 * m + 2 := by omega
    exact_mod_cast h
  have hpos2 : (0:ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
    have h : 0 < 2 * m + 1 := by omega
    exact_mod_cast h
  have hdiv : (0:ℝ) < (((((2 * m + 2 : ℕ) : ℝ) ^ (4 * m + 5)) /
      ((((2 * m + 1 : ℕ) : ℝ)) ^ (12 * m + 9)))) :=
    div_pos (pow_pos hpos1 _) (pow_pos hpos2 _)
  have hm : (0:ℝ) < (((((2 * m + 2 : ℕ) : ℝ) ^ (4 * m + 5)) /
      ((((2 * m + 1 : ℕ) : ℝ)) ^ (12 * m + 9)))) ^ m := pow_pos hdiv m
  conv_lhs => rw [← Real.exp_log hm]
  congr 1
  rw [Real.log_pow, Real.log_div (pow_ne_zero _ (ne_of_gt hpos1))
    (pow_ne_zero _ (ne_of_gt hpos2)), Real.log_pow, Real.log_pow]
  push_cast
  ring

private lemma z3p_log_split (m : ℕ) :
    Real.log (((2 * m + 2 : ℕ) : ℝ))
      = Real.log (((2 * m + 1 : ℕ) : ℝ))
        + Real.log (1 + 1 / (2 * (m : ℝ) + 1)) := by
  have hpos1 : (0:ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
    have h : 0 < 2 * m + 1 := by omega
    exact_mod_cast h
  have e1 : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m:ℝ) + 1 := by push_cast; ring
  have e2 : ((2 * m + 2 : ℕ) : ℝ) = 2 * (m:ℝ) + 2 := by push_cast; ring
  have harg : (((2 * m + 2 : ℕ) : ℝ))
      = (((2 * m + 1 : ℕ) : ℝ)) * (1 + 1 / (2 * (m : ℝ) + 1)) := by
    rw [e1, e2]
    have hne : (2:ℝ) * (m:ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  have hnn : (1:ℝ) + 1 / (2 * (m : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  rw [harg, Real.log_mul (ne_of_gt hpos1) hnn, add_comm]

private lemma z3p_third_seq_eq_exp (m : ℕ) :
    ((∏ n ∈ Finset.Icc 1 m, (((2 * n : ℕ) : ℝ) ^ ((2 * n : ℕ) ^ 2))) /
      (∏ n ∈ Finset.Icc 1 m, (((2 * n - 1 : ℕ) : ℝ) ^ ((2 * n - 1 : ℕ) ^ 2)))) ^ 4 *
        (((((2 * m + 2 : ℕ) : ℝ) ^ (4 * m + 5)) /
          ((((2 * m + 1 : ℕ) : ℝ) ^ (12 * m + 9)))) ^ m) =
      Real.exp (4 * (∑ k ∈ Finset.range m, z3pPairTerm k) +
        ((m : ℝ) * (4 * (m : ℝ) + 5) * Real.log (1 + 1 / (2 * (m : ℝ) + 1)) -
          2 * (m : ℝ))) := by
  rw [z3p_ratio_prod_eq_exp m, ← Real.exp_nat_mul, z3p_third_factor m,
    ← Real.exp_add]
  congr 1
  rw [z3p_log_split m]
  push_cast
  ring

private lemma z3p_rpow_quarter : Real.rpow (Real.exp 1) (1 / 4 : ℝ)
    = Real.exp (1 / 4 : ℝ) := by
  exact Real.exp_one_rpow _

private lemma z3p_inv_rpow_quarter : 1 / Real.rpow (Real.exp 1) (1 / 4 : ℝ)
    = Real.exp (-(1 / 4) : ℝ) := by
  rw [z3p_rpow_quarter, one_div, ← Real.exp_neg]

private lemma z3p_sum_tendsto : Filter.Tendsto
    (fun m : ℕ => ∑ k ∈ Finset.range m, z3pPairTerm k)
    Filter.atTop
    (nhds (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4)) :=
  HasSum.tendsto_sum_nat z3p_hasSum_pairTerm

private lemma z3p_tendsto_even :
    Filter.Tendsto
      (fun m : ℕ =>
        ∏ n ∈ Finset.Icc 1 (2 * m),
          Real.rpow (Real.exp 1) (1 / 4) *
            (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
              (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop
      (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4))) := by
  have hpoint : ∀ m : ℕ, (∏ n ∈ Finset.Icc 1 (2 * m),
        Real.rpow (Real.exp 1) (1 / 4) *
          (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
            (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
      = Real.exp (∑ k ∈ Finset.range m, z3pPairTerm k) := by
    intro m
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc,
      Nat.add_sub_cancel, z3p_rpow_quarter, ← Real.exp_nat_mul,
      z3p_prod_even_eq_exp m, ← Real.exp_add]
    congr 1
    push_cast
    ring
  exact z3p_sum_tendsto.rexp.congr (fun m => (hpoint m).symm)

private lemma z3p_log_split_real (m : ℕ) :
    Real.log (2 * (m : ℝ) + 2)
      = Real.log (2 * (m : ℝ) + 1) + Real.log (1 + 1 / (2 * (m : ℝ) + 1)) := by
  have e1 : ((2 * m + 2 : ℕ) : ℝ) = 2 * (m:ℝ) + 2 := by push_cast; ring
  have e2 : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m:ℝ) + 1 := by push_cast; ring
  rw [← e1]
  nth_rewrite 1 [← e2]
  exact z3p_log_split m

private lemma z3p_tendsto_odd :
    Filter.Tendsto
      (fun m : ℕ =>
        ∏ n ∈ Finset.Icc 1 (2 * m + 1),
          (1 / Real.rpow (Real.exp 1) (1 / 4)) *
            (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
              (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop
      (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) + 1 / 4))) := by
  have hpoint : ∀ m : ℕ, (∏ n ∈ Finset.Icc 1 (2 * m + 1),
        (1 / Real.rpow (Real.exp 1) (1 / 4)) *
          (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
            (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
      = Real.exp ((∑ k ∈ Finset.range m, z3pPairTerm k)
        + ((2 * (m : ℝ) + 1) * ((m : ℝ) + 1) *
          Real.log (1 + 1 / (2 * (m : ℝ) + 1)) - (m : ℝ)) - 1 / 4) := by
    intro m
    rw [Finset.prod_Icc_succ_top (show 1 ≤ 2 * m + 1 by omega),
      Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc,
      Nat.add_sub_cancel, z3p_inv_rpow_quarter, ← Real.exp_nat_mul,
      z3p_prod_even_eq_exp m,
      z3p_factor_eq_exp (2 * m + 1) (by omega),
      z3p_T_one m, z3p_sign_one m, z3p_base_one m,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    rw [z3p_log_sub_one m, z3p_log_split_real m]
    ring
  have hexp_arg : Filter.Tendsto
      (fun m : ℕ => (∑ k ∈ Finset.range m, z3pPairTerm k)
        + ((2 * (m : ℝ) + 1) * ((m : ℝ) + 1) *
          Real.log (1 + 1 / (2 * (m : ℝ) + 1)) - (m : ℝ)) - 1 / 4)
      Filter.atTop
      (nhds ((7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4
        + 3 / 4) - 1 / 4)) :=
    (z3p_sum_tendsto.add z3p_boundary_limits.1).sub
      (tendsto_const_nhds (x := (1 / 4 : ℝ)))
  have heq : ((7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4
      + 3 / 4) - 1 / 4)
      = 7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) + 1 / 4 := by
    ring
  rw [heq] at hexp_arg
  exact hexp_arg.rexp.congr (fun m => (hpoint m).symm)

private lemma z3p_tendsto_third :
    Filter.Tendsto
      (fun m : ℕ =>
        ((∏ n ∈ Finset.Icc 1 m,
            (((2 * n : ℕ) : ℝ) ^ ((2 * n : ℕ) ^ 2))) /
          (∏ n ∈ Finset.Icc 1 m,
            (((2 * n - 1 : ℕ) : ℝ) ^ ((2 * n - 1 : ℕ) ^ 2)))) ^ 4 *
        ((((2 * m + 2 : ℕ) : ℝ) ^ (4 * m + 5)) /
          (((2 * m + 1 : ℕ) : ℝ) ^ (12 * m + 9))) ^ m)
      Filter.atTop
      (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / Real.pi ^ 2))) := by
  have hexp_arg : Filter.Tendsto
      (fun m : ℕ => 4 * (∑ k ∈ Finset.range m, z3pPairTerm k) +
        ((m : ℝ) * (4 * (m : ℝ) + 5) *
          Real.log (1 + 1 / (2 * (m : ℝ) + 1)) - 2 * (m : ℝ)))
      Filter.atTop
      (nhds (4 * (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4)
        + 1)) :=
    ((tendsto_const_nhds (x := (4 : ℝ))).mul z3p_sum_tendsto).add
      z3p_boundary_limits.2
  have hpi : (Real.pi : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have heq : 4 * (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4) + 1
      = 7 * (riemannZeta (3 : ℂ)).re / Real.pi ^ 2 := by
    have h4pi : (4:ℝ) * Real.pi ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) hpi
    field_simp
    ring
  rw [heq] at hexp_arg
  exact hexp_arg.rexp.congr (fun m => (z3p_third_seq_eq_exp m).symm)

@[expose] public section

/-! # Infinite product formulas for zeta(3)
-/

/--
**Kachi–Tzermias infinite products for $\zeta(3)$.** Let $\zeta$ be the Riemann zeta function
and, for $n \ge 1$, put $a_n = \left(1 - \frac{1}{n+1}\right)^{(-1)^n n(n+1)/2}$. Then, as
$m \to \infty$,
$$\prod_{n=1}^{2m+1} e^{-1/4} a_n \to \exp\left(\frac{7\zeta(3)}{4\pi^2} + \frac{1}{4}\right),
\qquad \prod_{n=1}^{2m} e^{1/4} a_n \to \exp\left(\frac{7\zeta(3)}{4\pi^2} - \frac{1}{4}\right),$$
and
$$\left(\prod_{n=1}^{m} \frac{(2n)^{(2n)^2}}{(2n-1)^{(2n-1)^2}}\right)^4
\left(\frac{(2m+2)^{4m+5}}{(2m+1)^{12m+9}}\right)^m \to \exp\left(\frac{7\zeta(3)}{\pi^2}\right).$$

Source: Yasuyuki Kachi and Pavlos Tzermias, "Infinite Products Involving zeta(3) and
Catalan's Constant," Journal of Integer Sequences 15 (2012), Article 12.9.4,
Proposition `zeta3`, equations `zeta3i`–`zeta3iii`, lines 124–144,
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Tzermias/tzermias2.tex>.

Proves `Wanted` entry `zeta_three_infinite_product_formulas`.
-/
public theorem zeta_three_infinite_product_formulas :
    Filter.Tendsto
      (fun m : ℕ =>
        ∏ n ∈ Finset.Icc 1 (2 * m + 1),
          (1 / Real.rpow (Real.exp 1) (1 / 4)) *
            (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
              (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop
      (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) + 1 / 4))) ∧
    Filter.Tendsto
      (fun m : ℕ =>
        ∏ n ∈ Finset.Icc 1 (2 * m),
          Real.rpow (Real.exp 1) (1 / 4) *
            (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^
              (((n * (n + 1) / 2 : ℕ) : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop
      (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / (4 * Real.pi ^ 2) - 1 / 4))) ∧
    Filter.Tendsto
      (fun m : ℕ =>
        ((∏ n ∈ Finset.Icc 1 m,
            (((2 * n : ℕ) : ℝ) ^ ((2 * n : ℕ) ^ 2))) /
          (∏ n ∈ Finset.Icc 1 m,
            (((2 * n - 1 : ℕ) : ℝ) ^ ((2 * n - 1 : ℕ) ^ 2)))) ^ 4 *
        ((((2 * m + 2 : ℕ) : ℝ) ^ (4 * m + 5)) /
          (((2 * m + 1 : ℕ) : ℝ) ^ (12 * m + 9))) ^ m)
      Filter.atTop
      (nhds (Real.exp (7 * (riemannZeta (3 : ℂ)).re / Real.pi ^ 2))) := by
  exact ⟨z3p_tendsto_odd, z3p_tendsto_even, z3p_tendsto_third⟩

end

end MetaMathlibExt
