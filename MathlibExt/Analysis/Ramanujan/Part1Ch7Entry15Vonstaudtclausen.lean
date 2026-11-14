/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Phi
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Basic.Complex.BigOperators
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.Order.Compact

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry15Vonstaudtclausen

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry15Left (r : ℂ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : ℂ :=
  (chapter7Phi r ⟨x - 1, by constructor <;> linarith⟩ -
      chapter7Phi r ⟨-x, by constructor <;> linarith⟩) /
    (4 * Complex.Gamma (r + 1))

def chapter7Entry15Term (r : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (Real.sin (2 * Real.pi * k * x) : ℂ) /
    Complex.cpow (((2 * Real.pi * k : ℝ) : ℂ)) (r + 1)

def chapter7Entry15PartialSum (r : ℂ) (x : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 N, chapter7Entry15Term r x k

/-- The exponential `exp (2 * π * x * I)` whose powers bound sine partial sums. -/
private noncomputable def sinExp (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- Uniform bound for sine partial sums at `x`: `2 / ‖sinExp x - 1‖`. -/
private noncomputable def sinBound (x : ℝ) : ℝ :=
  2 / ‖sinExp x - 1‖

private theorem sinExp_ne_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    sinExp x ≠ 1 := by
  intro h
  rw [sinExp, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hcast : (((2 * Real.pi * x : ℝ)) : ℂ) = (x : ℂ) * (2 * (Real.pi : ℂ)) := by
    push_cast
    ring
  rw [hcast] at hn
  have hfactor : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero _ _
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  have hx_eq : (x : ℂ) = (n : ℂ) := by
    have hn2 : (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
        = (n : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      linear_combination hn
    exact mul_right_cancel₀ hfactor hn2
  have hxr : x = (n : ℝ) := by exact_mod_cast hx_eq
  have hnpos : (0 : ℤ) < n := by
    have h0 : (0 : ℝ) < (n : ℝ) := by rw [← hxr]; exact hx0
    exact_mod_cast h0
  have hnlt : n < (1 : ℤ) := by
    have h1 : (n : ℝ) < (1 : ℝ) := by rw [← hxr]; exact hx1
    exact_mod_cast h1
  omega

private theorem sinExp_pow_im (x : ℝ) (j : ℕ) :
    ((sinExp x) ^ j).im = Real.sin (2 * Real.pi * x * j) := by
  have hpow : (sinExp x) ^ j
      = Complex.exp (((2 * Real.pi * x * j : ℝ) : ℂ) * Complex.I) := by
    rw [sinExp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, Complex.exp_ofReal_mul_I_im]

private theorem sinExp_norm (x : ℝ) : ‖sinExp x‖ = 1 := by
  simp only [sinExp, Complex.norm_exp_ofReal_mul_I]

private theorem sinPartial_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ) :
    ‖∑ j ∈ Finset.range k, ((((Real.sin (2 * Real.pi * x * j) : ℝ))) : ℂ)‖
      ≤ 2 / ‖sinExp x - 1‖ := by
  have h1 : sinExp x - 1 ≠ 0 := sub_ne_zero.mpr (sinExp_ne_one hx0 hx1)
  have h1pos : (0 : ℝ) < ‖sinExp x - 1‖ := norm_pos_iff.mpr h1
  have hgeom : (∑ j ∈ Finset.range k, (sinExp x) ^ j) * (sinExp x - 1)
      = (sinExp x) ^ k - 1 := geom_sum_mul _ _
  have hsum : (∑ j ∈ Finset.range k, (sinExp x) ^ j)
      = ((sinExp x) ^ k - 1) / (sinExp x - 1) := by
    rw [eq_div_iff h1]
    exact hgeom
  have him : (∑ j ∈ Finset.range k, ((((Real.sin (2 * Real.pi * x * j) : ℝ))) : ℂ))
      = (((∑ j ∈ Finset.range k, (sinExp x) ^ j).im : ℝ) : ℂ) := by
    rw [Complex.im_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [sinExp_pow_im]
  rw [him, Complex.norm_real, Real.norm_eq_abs]
  calc |(∑ j ∈ Finset.range k, (sinExp x) ^ j).im|
        ≤ ‖∑ j ∈ Finset.range k, (sinExp x) ^ j‖ :=
          Complex.abs_im_le_norm _
      _ = ‖((sinExp x) ^ k - 1) / (sinExp x - 1)‖ := by rw [hsum]
      _ ≤ 2 / ‖sinExp x - 1‖ := by
          rw [norm_div]
          have hnum : ‖(sinExp x) ^ k - 1‖ ≤ 2 := by
            have h1 : ‖(sinExp x) ^ k‖ = 1 := by
              rw [norm_pow, sinExp_norm, one_pow]
            calc ‖(sinExp x) ^ k - 1‖ ≤ ‖(sinExp x) ^ k‖ + ‖(1 : ℂ)‖ :=
                    norm_sub_le _ _
                _ = 2 := by rw [h1, norm_one]; norm_num
          exact (div_le_div_iff_of_pos_right h1pos).mpr hnum

private theorem sinBound_nonneg (x : ℝ) : 0 ≤ sinBound x := by
  simp only [sinBound]
  positivity

/-- Sine partial sums: `∑ j ∈ range k, sin (2 * π * x * j)`. -/
private noncomputable def bpA (x : ℝ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, ((((Real.sin (2 * Real.pi * x * j) : ℝ))) : ℂ)

/-- Inverse-power factor `k ^ (-s)` for the summation by parts. -/
private noncomputable def bpG (s : ℂ) (k : ℕ) : ℂ :=
  ((((k : ℝ))) : ℂ) ^ (-s)

/-- Summation-by-parts summand `A_{i+1} * (g_{i+1} - g_i)`. -/
private noncomputable def bpH (x : ℝ) (s : ℂ) (i : ℕ) : ℂ :=
  bpA x (i + 1) * (bpG s (i + 1) - bpG s i)

/-- The absolutely convergent by-parts series, whose negation is the sine sum. -/
private noncomputable def bpT (x : ℝ) (s : ℂ) : ℂ :=
  ∑' i, bpH x s i

private theorem bpA_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ) :
    ‖bpA x k‖ ≤ sinBound x :=
  sinPartial_bound hx0 hx1 k

/-- Mean-value bound for consecutive inverse powers. -/
private theorem cpow_diff_bound_aux {s : ℂ} (hs : 0 < s.re) {t0 : ℝ}
    (ht0 : 1 ≤ t0) :
    ‖(((t0 + 1 : ℝ)) : ℂ) ^ (-s) - ((t0 : ℝ) : ℂ) ^ (-s)‖
      ≤ ‖s‖ / t0 ^ (s.re + 1) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.zero_re, neg_eq_zero] at h2
    linarith
  have hderiv : ∀ t ∈ Set.Icc t0 (t0 + 1),
      HasDerivWithinAt (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s))
        ((-s) * ((t : ℝ) : ℂ) ^ (-s - 1)) (Set.Icc t0 (t0 + 1)) t := by
    intro t ht
    have htne : t ≠ 0 := by
      have hle : t0 ≤ t := ht.1
      linarith
    exact (hasDerivAt_ofReal_cpow_const htne hs0).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico t0 (t0 + 1),
      ‖(-s) * ((((t : ℝ))) : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ / t0 ^ (s.re + 1) := by
    intro t ht
    have htge : t0 ≤ t := ht.1
    have htpos : (0 : ℝ) < t := by linarith
    have ht0pos : (0 : ℝ) < t0 := by linarith
    have hnorm : ‖((((t : ℝ))) : ℂ) ^ (-s - 1)‖ = t ^ (-(s.re + 1)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      congr 1
      have hre : (-s - 1).re = -(s.re + 1) := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
        ring
      exact hre
    rw [norm_mul, hnorm, norm_neg]
    have hle_pow : t0 ^ (s.re + 1) ≤ t ^ (s.re + 1) :=
      Real.rpow_le_rpow ht0pos.le htge (by linarith)
    have hpost0 : (0 : ℝ) < t0 ^ (s.re + 1) := Real.rpow_pos_of_pos ht0pos _
    have hpost : (0 : ℝ) < t ^ (s.re + 1) := Real.rpow_pos_of_pos htpos _
    have hinv : t ^ (-(s.re + 1)) ≤ t0 ^ (-(s.re + 1)) := by
      rw [Real.rpow_neg htpos.le, Real.rpow_neg ht0pos.le]
      exact (inv_le_inv₀ hpost hpost0).mpr hle_pow
    calc ‖s‖ * t ^ (-(s.re + 1)) ≤ ‖s‖ * t0 ^ (-(s.re + 1)) :=
            mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ = ‖s‖ / t0 ^ (s.re + 1) := by
            rw [Real.rpow_neg ht0pos.le, div_eq_mul_inv]
  have hmem : t0 + 1 ∈ Set.Icc t0 (t0 + 1) :=
    Set.right_mem_Icc.mpr (le_add_of_nonneg_right zero_le_one)
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    (t0 + 1) hmem
  rw [show (t0 + 1) - t0 = (1 : ℝ) by ring, mul_one] at hmvt
  exact hmvt

private theorem bpH_zero (x : ℝ) (s : ℂ) : bpH x s 0 = 0 := by
  simp only [bpH]
  have hA : bpA x (0 + 1) = 0 := by
    simp only [zero_add, bpA, Finset.sum_range_one]
    simp
  rw [hA, zero_mul]

private theorem bpH_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℂ} (hs : 0 < s.re) (i : ℕ) :
    ‖bpH x s i‖ ≤ sinBound x * ‖s‖ / (i : ℝ) ^ (s.re + 1) := by
  by_cases hi : i = 0
  · subst hi
    rw [bpH_zero, norm_zero]
    have hz : (0 : ℝ) ^ (s.re + 1) = 0 :=
      Real.zero_rpow (by linarith : (0 : ℝ) < s.re + 1).ne'
    simp only [Nat.cast_zero, hz, div_zero, le_refl]
  · have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
    have hA : ‖bpA x (i + 1)‖ ≤ sinBound x := bpA_bound hx0 hx1 _
    have hD : ‖bpG s (i + 1) - bpG s i‖ ≤ ‖s‖ / (i : ℝ) ^ (s.re + 1) := by
      have h := cpow_diff_bound_aux hs hi1
      have hcast : ((((i + 1 : ℕ))) : ℝ) = (i : ℝ) + 1 := by simp
      simp only [bpG]
      rw [hcast]
      exact h
    calc ‖bpH x s i‖
          = ‖bpA x (i + 1)‖ * ‖bpG s (i + 1) - bpG s i‖ := by
            simp only [bpH, norm_mul]
        _ ≤ sinBound x * (‖s‖ / (i : ℝ) ^ (s.re + 1)) :=
            mul_le_mul hA hD (norm_nonneg _) (sinBound_nonneg x)
        _ = sinBound x * ‖s‖ / (i : ℝ) ^ (s.re + 1) := by rw [mul_div_assoc]

private theorem bpT_summable (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℂ} (hs : 0 < s.re) : Summable (bpH x s) := by
  refine Summable.of_norm_bounded ?_ (bpH_bound x hx0 hx1 hs)
  have hS := (Real.summable_one_div_nat_rpow.mpr
    (show (1 : ℝ) < s.re + 1 by linarith)).mul_left (sinBound x * ‖s‖)
  have hfun : (fun i : ℕ => sinBound x * ‖s‖ / (i : ℝ) ^ (s.re + 1))
      = fun n : ℕ => (sinBound x * ‖s‖) * (1 / (n : ℝ) ^ (s.re + 1)) := by
    funext i
    rw [mul_one_div]
  rw [hfun]
  exact hS

/-- Each sine-series term factors through the by-parts data. -/
private theorem sinTerm_eq_mul (x : ℝ) (s : ℂ) (k : ℕ) :
    ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s
      = ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) * bpG s k := by
  by_cases hk : k = 0
  · subst hk
    simp
  · have hbase : (k : ℂ) = ((((k : ℝ))) : ℂ) := (Complex.ofReal_natCast k).symm
    change ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s
      = ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) * ((((k : ℝ))) : ℂ) ^ (-s)
    rw [hbase, div_eq_mul_inv, ← Complex.cpow_neg]

/-- The `Icc` sine partial sums agree with shifted `range` sums. -/
private theorem sinIcc_eq_range (x : ℝ) (s : ℂ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s)
      = ∑ k ∈ Finset.range (N + 1),
        ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s := by
  have h0 : ((((Real.sin (2 * Real.pi * x * ((0 : ℕ) : ℝ)) : ℝ))) : ℂ)
      / ((0 : ℕ) : ℂ) ^ s = 0 := by simp
  induction N with
  | zero =>
    rw [Finset.Icc_eq_empty (by decide), Finset.sum_empty, Finset.sum_range_succ,
      Finset.range_zero, Finset.sum_empty, zero_add]
    exact h0.symm
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), Finset.sum_range_succ, ih]

/-- The sine-series `range` partial sums converge to `-bpT`. -/
private theorem sinRange_tendsto {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N => ∑ k ∈ Finset.range N,
      ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s)
      atTop (𝓝 (-bpT x s)) := by
  have hterm : ∀ k : ℕ,
      ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s
      = ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) * bpG s k :=
    fun k => sinTerm_eq_mul x s k
  have hbp : ∀ N, (∑ k ∈ Finset.range (N + 1),
        ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) * bpG s k)
      = (bpA x (N + 1) * bpG s N) - ∑ i ∈ Finset.range N, bpH x s i := by
    intro N
    have h := Finset.sum_range_by_parts'
      (fun k => ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ)) (bpG s) (N + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at h
    exact h
  have hbound0 : Tendsto (fun N => bpA x (N + 1) * bpG s N) atTop (𝓝 0) := by
    have hle : ∀ N, ‖bpA x (N + 1) * bpG s N‖ ≤ sinBound x / (N : ℝ) ^ s.re := by
      intro N
      by_cases hN : N = 0
      · subst hN
        have hA : bpA x (0 + 1) = 0 := by
          simp only [zero_add, bpA, Finset.sum_range_one]
          simp
        rw [hA, zero_mul, norm_zero]
        have hz : (0 : ℝ) ^ s.re = 0 := Real.zero_rpow hs.ne'
        simp only [Nat.cast_zero, hz, div_zero, le_refl]
      · have hNpos : (0 : ℝ) < (N : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hN
        rw [norm_mul]
        have hB : ‖bpA x (N + 1)‖ ≤ sinBound x := bpA_bound hx0 hx1 _
        have hG : ‖bpG s N‖ = 1 / (N : ℝ) ^ s.re := by
          simp only [bpG, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
          rw [Complex.neg_re, Real.rpow_neg hNpos.le, one_div]
        rw [hG]
        calc ‖bpA x (N + 1)‖ * (1 / (N : ℝ) ^ s.re)
              ≤ sinBound x * (1 / (N : ℝ) ^ s.re) :=
                mul_le_mul_of_nonneg_right hB
                  (one_div_pos.mpr (Real.rpow_pos_of_pos hNpos _)).le
            _ = sinBound x / (N : ℝ) ^ s.re := by rw [mul_one_div]
    have hlim : Tendsto (fun N : ℕ => sinBound x / (N : ℝ) ^ s.re) atTop
        (𝓝 0) := by
      have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ s.re) atTop atTop :=
        (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
      have hinv : Tendsto (fun N : ℕ => ((N : ℝ) ^ s.re)⁻¹) atTop (𝓝 0) :=
        hpow.inv_tendsto_atTop
      have hmul := (tendsto_const_nhds (x := sinBound x)).mul hinv
      rw [mul_zero] at hmul
      have hcongr : (fun N : ℕ => sinBound x / (N : ℝ) ^ s.re)
          = fun N : ℕ => sinBound x * ((N : ℝ) ^ s.re)⁻¹ := by
        funext N
        rw [div_eq_mul_inv]
      rw [hcongr]
      exact hmul
    exact squeeze_zero_norm hle hlim
  have hsumT : Tendsto (fun N => ∑ i ∈ Finset.range N, bpH x s i) atTop
      (𝓝 (bpT x s)) :=
    (bpT_summable x hx0 hx1 hs).hasSum.tendsto_sum_nat
  have hShift : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s) atTop
      (𝓝 (-bpT x s)) := by
    have heq : ∀ N, (∑ k ∈ Finset.range (N + 1),
          ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s)
        = (bpA x (N + 1) * bpG s N) - ∑ i ∈ Finset.range N, bpH x s i := by
      intro N
      rw [← hbp N]
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k
    have hfun : (fun N => ∑ k ∈ Finset.range (N + 1),
          ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s)
        = fun N => (bpA x (N + 1) * bpG s N)
          - ∑ i ∈ Finset.range N, bpH x s i :=
      funext heq
    rw [hfun]
    have h := hbound0.sub hsumT
    rw [show (0 : ℂ) - bpT x s = -bpT x s from zero_sub _] at h
    exact h
  exact (tendsto_add_atTop_iff_nat 1).mp hShift

/-- The sine-series `Icc` partial sums converge to `-bpT`. -/
private theorem sinIcc_tendsto_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s)
      atTop (𝓝 (-bpT x s)) := by
  have hR := sinRange_tendsto hx0 hx1 hs
  have hS := (tendsto_add_atTop_iff_nat 1).mpr hR
  exact hS.congr (fun N : ℕ => (sinIcc_eq_range x s N).symm)

/-- On `1 < s.re`, the by-parts limit agrees with `sinZeta`. -/
private theorem neg_bpT_eq_sinZeta {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℂ} (hs1 : 1 < s.re) :
    -bpT x s = HurwitzZeta.sinZeta (x : UnitAddCircle) s := by
  have hs0 : (0 : ℝ) < s.re := zero_lt_one.trans hs1
  have hT := sinIcc_tendsto_neg hx0 hx1 hs0
  have hS : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s) atTop
      (𝓝 (HurwitzZeta.sinZeta (x : UnitAddCircle) s)) := by
    have hHas : HasSum (fun n : ℕ =>
          ((((Real.sin (2 * Real.pi * x * n) : ℝ))) : ℂ) / (n : ℂ) ^ s)
        (HurwitzZeta.sinZeta (x : UnitAddCircle) s) :=
      HurwitzZeta.hasSum_nat_sinZeta x hs1
    have hR := hHas.tendsto_sum_nat
    have hS' := (tendsto_add_atTop_iff_nat 1).mpr hR
    exact hS'.congr (fun N : ℕ => (sinIcc_eq_range x s N).symm)
  exact tendsto_nhds_unique hT hS

private theorem isOpen_re_pos : IsOpen {z : ℂ | 0 < z.re} :=
  Complex.isOpen_re_gt 0

private theorem isOpen_re_gt_one : IsOpen {z : ℂ | 1 < z.re} :=
  Complex.isOpen_re_gt 1

private theorem convex_re_pos : Convex ℝ {z : ℂ | 0 < z.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hre]
  rcases eq_or_ne a 0 with rfl | ha0
  · have hb1 : b = 1 := by linarith
    rw [hb1]
    simp only [zero_mul, zero_add, one_mul]
    exact hy
  · have ha' : 0 < a := lt_of_le_of_ne' ha ha0
    exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)

private theorem preconnected_re_pos : IsPreconnected {z : ℂ | 0 < z.re} :=
  Convex.isPreconnected convex_re_pos

/-- Each by-parts summand is holomorphic in `s` on `0 < s.re`. -/
private theorem bpH_differentiableAt (x : ℝ) (i : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (fun s => bpH x s i) s := by
  by_cases hi : i = 0
  · subst hi
    have hfun : (fun s => bpH x s 0) = fun _ => (0 : ℂ) :=
      funext (fun s => bpH_zero x s)
    rw [hfun]
    exact differentiableAt_const 0
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    have h1 : ∀ k : ℕ, 1 ≤ k → DifferentiableAt ℂ (fun s : ℂ => bpG s k) s := by
      intro k hk
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (by omega : k ≠ 0)
      have hk0 : ((((k : ℝ))) : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
      have hneg : DifferentiableAt ℂ (fun s : ℂ => -s) s := by fun_prop
      exact hneg.const_cpow (Or.inl hk0)
    have hsub := (h1 (i + 1) (by omega)).sub (h1 i hi1)
    exact hsub.const_mul (bpA x (i + 1))

/-- The by-parts series is locally uniformly summable on `0 < s.re`. -/
private theorem bpT_summableLocallyUniformlyOn (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    SummableLocallyUniformlyOn (fun i s => bpH x s i)
      {z : ℂ | 0 < z.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_re_pos
  intro K hKsub hKcomp
  obtain ⟨σ0, hσ0pos, hσ0le⟩ := hKcomp.exists_forall_le'
    Complex.continuous_re.continuousOn (fun b hb => hKsub hb)
  by_cases hKne : K.Nonempty
  · obtain ⟨s0, hs0K, hs0max⟩ :=
      hKcomp.exists_isMaxOn hKne continuous_norm.continuousOn
    refine ⟨fun i => sinBound x * ‖s0‖ / (i : ℝ) ^ (σ0 + 1), ?_, ?_⟩
    · have hS := (Real.summable_one_div_nat_rpow.mpr
        (show (1 : ℝ) < σ0 + 1 by linarith)).mul_left (sinBound x * ‖s0‖)
      have hfun : (fun i : ℕ => sinBound x * ‖s0‖ / (i : ℝ) ^ (σ0 + 1))
          = fun n : ℕ => (sinBound x * ‖s0‖) * (1 / (n : ℝ) ^ (σ0 + 1)) := by
        funext i
        rw [mul_one_div]
      rw [hfun]
      exact hS
    · intro i s hsK
      have hspos : 0 < s.re := hKsub hsK
      have hσle : σ0 ≤ s.re := hσ0le s hsK
      have hR : ‖s‖ ≤ ‖s0‖ := isMaxOn_iff.mp hs0max s hsK
      have hB0 : 0 ≤ sinBound x := sinBound_nonneg x
      have hR0 : 0 ≤ ‖s0‖ := norm_nonneg _
      have hbase := bpH_bound x hx0 hx1 hspos i
      by_cases hi : i = 0
      · subst hi
        rw [bpH_zero]
        simp only [norm_zero]
        have hz : (0 : ℝ) ^ (σ0 + 1) = 0 :=
          Real.zero_rpow (by linarith : (0 : ℝ) < σ0 + 1).ne'
        simp only [Nat.cast_zero, hz, div_zero, le_refl]
      · have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
        have hipos : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le (by norm_num) hi1
        have hpow_le : (i : ℝ) ^ (σ0 + 1) ≤ (i : ℝ) ^ (s.re + 1) :=
          Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)
        have hpost0 : (0 : ℝ) < (i : ℝ) ^ (σ0 + 1) :=
          Real.rpow_pos_of_pos hipos _
        have hpost : (0 : ℝ) < (i : ℝ) ^ (s.re + 1) :=
          Real.rpow_pos_of_pos hipos _
        calc ‖bpH x s i‖ ≤ sinBound x * ‖s‖ / (i : ℝ) ^ (s.re + 1) := hbase
            _ = (sinBound x * ‖s‖) * (1 / (i : ℝ) ^ (s.re + 1)) := by
                rw [mul_one_div]
            _ ≤ (sinBound x * ‖s0‖) * (1 / (i : ℝ) ^ (σ0 + 1)) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left hR hB0
                · exact one_div_le_one_div_of_le hpost0 hpow_le
                · exact (one_div_pos.mpr hpost).le
                · exact mul_nonneg hB0 hR0
            _ = sinBound x * ‖s0‖ / (i : ℝ) ^ (σ0 + 1) := by rw [mul_one_div]
  · refine ⟨fun _ => (0 : ℝ), summable_zero, ?_⟩
    intro i s hsK
    exact (hKne ⟨s, hsK⟩).elim

private theorem bpT_analytic (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    AnalyticOnNhd ℂ (bpT x) {z | 0 < z.re} := by
  have hsum := bpT_summableLocallyUniformlyOn x hx0 hx1
  have hdiff : ∀ i s, s ∈ {z : ℂ | 0 < z.re} →
      DifferentiableAt ℂ (fun s => bpH x s i) s :=
    fun i s _ => bpH_differentiableAt x i s
  have hD := hsum.differentiableOn isOpen_re_pos hdiff
  have hD' : DifferentiableOn ℂ (bpT x) {z : ℂ | 0 < z.re} := hD
  exact hD'.analyticOnNhd isOpen_re_pos

/-- The by-parts limit equals `sinZeta` on all of `0 < s.re`. -/
private theorem bpT_eq_sinZeta {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℂ} (hs : 0 < s.re) :
    -bpT x s = HurwitzZeta.sinZeta (x : UnitAddCircle) s := by
  have hT : AnalyticOnNhd ℂ (fun z => -bpT x z) {z | 0 < z.re} :=
    (bpT_analytic x hx0 hx1).neg
  have hS : AnalyticOnNhd ℂ (HurwitzZeta.sinZeta (x : UnitAddCircle))
      {z | 0 < z.re} :=
    (HurwitzZeta.differentiableAt_sinZeta _).differentiableOn.analyticOnNhd
      isOpen_re_pos
  have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
    have h2 : (2 : ℂ) = 1 + 1 := by norm_num
    change (1 : ℝ) < (2 : ℂ).re
    rw [h2, Complex.add_re, Complex.one_re]
    norm_num
  have hev : (fun z => -bpT x z) =ᶠ[𝓝 (2 : ℂ)]
      HurwitzZeta.sinZeta (x : UnitAddCircle) := by
    have hnb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      isOpen_re_gt_one.mem_nhds hmem
    filter_upwards [hnb] with z hz using neg_bpT_eq_sinZeta hx0 hx1 hz
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    have h2 : (2 : ℂ) = 1 + 1 := by norm_num
    change (0 : ℝ) < (2 : ℂ).re
    rw [h2, Complex.add_re, Complex.one_re]
    norm_num
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hT hS
    preconnected_re_pos h2mem hev hs

/-- The sine-series `Icc` partial sums converge to `sinZeta` for `0 < s.re`. -/
private theorem sinIcc_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ s)
      atTop (𝓝 (HurwitzZeta.sinZeta (x : UnitAddCircle) s)) := by
  have hT := sinIcc_tendsto_neg hx0 hx1 hs
  rw [bpT_eq_sinZeta hx0 hx1 hs] at hT
  exact hT

private theorem entry15_of_re_gt_neg_one {r : ℂ} {x : ℝ} (hr : -1 < r.re)
    (hx0 : 0 < x) (hx1 : x < 1) :
    ∃! L : ℂ,
      Tendsto (chapter7Entry15PartialSum r x) atTop (𝓝 L) ∧
        chapter7Entry15Left r x hx0 hx1 =
          -Complex.cos ((Real.pi : ℂ) * r / 2) * L := by
  have hs1 : (0 : ℝ) < (r + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hne : ∀ n : ℕ, r + 1 ≠ -((n : ℕ) : ℂ) := by
    intro n h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at h2
    have hn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hG : Complex.Gamma (r + 1) ≠ 0 := Complex.Gamma_ne_zero hne
  have hG4 : (4 : ℂ) * Complex.Gamma (r + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) hG
  have hFE := HurwitzZeta.hurwitzZetaOdd_one_sub
    ((((x : ℝ))) : UnitAddCircle) (s := r + 1) hne
  rw [show (1 : ℂ) - (r + 1) = -r by ring] at hFE
  have hsin : Complex.sin (((Real.pi : ℂ)) * (r + 1) / 2)
      = Complex.cos (((Real.pi : ℂ)) * r / 2) := by
    have heq : ((Real.pi : ℂ)) * (r + 1) / 2
        = ((Real.pi : ℂ)) * r / 2 + ((Real.pi : ℂ)) / 2 := by ring
    rw [heq, Complex.sin_add, Complex.cos_pi_div_two,
      Complex.sin_pi_div_two]
    ring
  rw [hsin] at hFE
  have hneg : -(((((x : ℝ))) : UnitAddCircle))
      = ((((1 - x : ℝ))) : UnitAddCircle) := by
    have h1 : ((((1 : ℝ))) : UnitAddCircle) = 0 := AddCircle.coe_period 1
    calc -(((((x : ℝ))) : UnitAddCircle))
        = ((((1 : ℝ))) : UnitAddCircle) - ((((x : ℝ))) : UnitAddCircle) := by
          rw [h1, zero_sub]
      _ = ((((1 - x : ℝ))) : UnitAddCircle) :=
          (AddCircle.coe_sub (1 : ℝ) (1 : ℝ) x).symm
  have hOdd := HurwitzZeta.hurwitzZetaOdd_eq
    ((((x : ℝ))) : UnitAddCircle) (-r)
  rw [hneg] at hOdd
  have hCombine :
      (HurwitzZeta.hurwitzZeta ((((x : ℝ))) : UnitAddCircle) (-r) -
        HurwitzZeta.hurwitzZeta ((((1 - x : ℝ))) : UnitAddCircle) (-r)) / 2
      = 2 * ((2 * ((Real.pi : ℂ))) ^ (-(r + 1))) * Complex.Gamma (r + 1) *
        Complex.cos (((Real.pi : ℂ)) * r / 2) *
        HurwitzZeta.sinZeta ((((x : ℝ))) : UnitAddCircle) (r + 1) := by
    rw [← hOdd]
    exact hFE
  have hLeft : chapter7Entry15Left r x hx0 hx1
      = (HurwitzZeta.hurwitzZeta ((((1 - x : ℝ))) : UnitAddCircle) (-r) -
          HurwitzZeta.hurwitzZeta ((((x : ℝ))) : UnitAddCircle) (-r)) /
        (4 * Complex.Gamma (r + 1)) := by
    unfold chapter7Entry15Left chapter7Phi
    change ((riemannZeta (-r) -
        HurwitzZeta.hurwitzZeta ((((x - 1 + 1 : ℝ))) : UnitAddCircle) (-r)) -
        (riemannZeta (-r) -
          HurwitzZeta.hurwitzZeta ((((-x + 1 : ℝ))) : UnitAddCircle) (-r))) /
        (4 * Complex.Gamma (r + 1)) = _
    have e1 : ((((x - 1 + 1 : ℝ))) : UnitAddCircle)
        = ((((x : ℝ))) : UnitAddCircle) := by
      congr 1
      ring
    have e2 : ((((-x + 1 : ℝ))) : UnitAddCircle)
        = ((((1 - x : ℝ))) : UnitAddCircle) := by
      congr 1
      ring
    rw [e1, e2,
      show ((riemannZeta (-r) -
        HurwitzZeta.hurwitzZeta ((((x : ℝ))) : UnitAddCircle) (-r)) -
        (riemannZeta (-r) -
          HurwitzZeta.hurwitzZeta ((((1 - x : ℝ))) : UnitAddCircle) (-r)))
        = (HurwitzZeta.hurwitzZeta ((((1 - x : ℝ))) : UnitAddCircle) (-r) -
          HurwitzZeta.hurwitzZeta ((((x : ℝ))) : UnitAddCircle) (-r)) by ring]
  have hSinT : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
        ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ (r + 1))
      atTop (𝓝 (HurwitzZeta.sinZeta ((((x : ℝ))) : UnitAddCircle) (r + 1))) :=
    sinIcc_limit hx0 hx1 hs1
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hbase : ∀ k : ℕ, (((((2 * Real.pi * k : ℝ))) : ℂ))
      = ((((2 * Real.pi : ℝ))) : ℂ) * (((((k : ℕ) : ℝ))) : ℂ) := by
    intro k
    rw [Complex.ofReal_mul]
  have h2pic : ((((2 * Real.pi : ℝ))) : ℂ) ^ (r + 1)
      = (2 * ((Real.pi : ℂ))) ^ (r + 1) := by
    congr 1
    push_cast
    ring
  have hmulcpow : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → ∀ (s : ℂ),
      Complex.cpow ((a : ℂ) * (b : ℂ)) s
        = Complex.cpow (a : ℂ) s * Complex.cpow (b : ℂ) s := by
    intro a b ha hb s
    exact Complex.mul_cpow_ofReal_nonneg ha hb s
  have hterm : ∀ k : ℕ, chapter7Entry15Term r x k
      = (2 * ((Real.pi : ℂ))) ^ (-(r + 1)) *
        (↑(Real.sin (2 * Real.pi * x * k)) / (k : ℂ) ^ (r + 1)) := by
    intro k
    unfold chapter7Entry15Term
    have harg : (2 * Real.pi * ((k : ℕ) : ℝ) * x) = 2 * Real.pi * x * k := by ring
    have hknn : (0 : ℝ) ≤ (((k : ℕ)) : ℝ) := by exact_mod_cast Nat.zero_le k
    rw [harg, hbase k, hmulcpow _ _ h2pi hknn (r + 1), Complex.ofReal_natCast]
    change ↑(Real.sin (2 * Real.pi * x * ↑k)) /
      ((((((2 * Real.pi : ℝ))) : ℂ) ^ (r + 1)) * ((k : ℂ) ^ (r + 1))) = _
    rw [h2pic, Complex.cpow_neg, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  have hPS : Tendsto (chapter7Entry15PartialSum r x) atTop
      (𝓝 ((2 * ((Real.pi : ℂ))) ^ (-(r + 1)) *
        HurwitzZeta.sinZeta ((((x : ℝ))) : UnitAddCircle) (r + 1))) := by
    have heq : ∀ N : ℕ, (2 * ((Real.pi : ℂ))) ^ (-(r + 1)) *
          (∑ k ∈ Finset.Icc 1 N,
            ((((Real.sin (2 * Real.pi * x * k) : ℝ))) : ℂ) / (k : ℂ) ^ (r + 1))
        = chapter7Entry15PartialSum r x N := by
      intro N
      simp only [chapter7Entry15PartialSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact (hterm k).symm
    have hC := (tendsto_const_nhds
      (x := (2 * ((Real.pi : ℂ))) ^ (-(r + 1)))).mul hSinT
    exact Tendsto.congr heq hC
  have hfin : chapter7Entry15Left r x hx0 hx1
      = -Complex.cos (((Real.pi : ℂ)) * r / 2) *
        ((2 * ((Real.pi : ℂ))) ^ (-(r + 1)) *
          HurwitzZeta.sinZeta ((((x : ℝ))) : UnitAddCircle) (r + 1)) := by
    rw [hLeft, div_eq_iff hG4]
    linear_combination -2 * hCombine
  refine ⟨(2 * ((Real.pi : ℂ))) ^ (-(r + 1)) *
      HurwitzZeta.sinZeta ((((x : ℝ))) : UnitAddCircle) (r + 1),
    ⟨hPS, hfin⟩, fun L' hL' => ?_⟩
  exact tendsto_nhds_unique hL'.1 hPS
/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 15.

Proves `Wanted` entry `ramanujan_part1_ch7_entry15_vonstaudtclausen`.
-/
theorem ramanujan_part1_ch7_entry15_vonstaudtclausen
    (r : ℂ) (x : ℝ) (hr : -1 < r.re) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃! L : ℂ,
      Tendsto (chapter7Entry15PartialSum r x) atTop (𝓝 L) ∧
        chapter7Entry15Left r x hx0 hx1 =
          -Complex.cos ((Real.pi : ℂ) * r / 2) * L := by
  exact entry15_of_re_gt_neg_one hr hx0 hx1

end
end Entry15Vonstaudtclausen
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
