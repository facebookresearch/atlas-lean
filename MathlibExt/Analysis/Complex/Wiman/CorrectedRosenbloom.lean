/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.CumulantMoments
public import MathlibExt.Analysis.Complex.Wiman.MaximumTermAttained
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Probability.Moments.Variance

@[expose] public section

namespace Complex

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- A probability measure on `ℕ` with uniformly bounded atoms is controlled by the variance of
the natural-valued random variable.  The additive `1` makes the estimate valid at zero variance. -/
private theorem one_le_eight_mul_atomBound_mul_one_add_sqrt_variance
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hLp : MemLp (fun n : ℕ => (n : ℝ)) 2 μ)
    (p : ℝ) (hp : 0 ≤ p) (hatom : ∀ n : ℕ, μ.real {n} ≤ p) :
    1 ≤ 8 * p * (1 + Real.sqrt
      (ProbabilityTheory.variance (fun n : ℕ => (n : ℝ)) μ)) := by
  let m : ℝ := ∫ n : ℕ, (n : ℝ) ∂μ
  let v : ℝ := ProbabilityTheory.variance (fun n : ℕ => (n : ℝ)) μ
  let s : ℝ := Real.sqrt v
  let c : ℝ := 1 + 2 * s
  let bad : Set ℕ := {n | c ≤ |(n : ℝ) - m|}
  have hm : 0 ≤ m := by
    dsimp [m]
    exact integral_nonneg fun n => Nat.cast_nonneg n
  have hv : 0 ≤ v := by
    dsimp [v]
    exact ProbabilityTheory.variance_nonneg _ _
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = v := by
    dsimp [s]
    exact Real.sq_sqrt hv
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcheb : μ bad ≤ ENNReal.ofReal (v / c ^ 2) := by
    simpa only [bad, c, v, m] using
      (ProbabilityTheory.meas_ge_le_variance_div_sq hLp hc)
  have hfrac : v / c ^ 2 ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hc)).2
    rw [← hs_sq]
    dsimp [c]
    nlinarith [sq_nonneg s]
  have hbad : μ.real bad ≤ (1 : ℝ) / 4 := by
    rw [measureReal_def]
    calc
      ENNReal.toReal (μ bad) ≤ ENNReal.toReal (ENNReal.ofReal (v / c ^ 2)) :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      _ = v / c ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg hv (sq_nonneg c))
      _ ≤ (1 : ℝ) / 4 := hfrac
  have hbadMeas : MeasurableSet bad := MeasurableSet.of_discrete
  have hgood : (3 : ℝ) / 4 ≤ μ.real badᶜ := by
    rw [measureReal_compl hbadMeas, probReal_univ]
    linarith
  let k : ℕ := ⌊m⌋₊
  let N : ℕ := ⌈c⌉₊
  let S : Finset ℕ := Finset.Icc (k - N) (k + N)
  have hsubset : badᶜ ⊆ (S : Set ℕ) := by
    intro n hn
    have hncenter : |(n : ℝ) - m| < c := by
      simpa only [bad, mem_compl_iff, mem_ofPred_eq, not_le] using hn
    have hfloor : |m - (k : ℝ)| ≤ 1 := by
      simpa only [k] using (Nat.abs_sub_floor_le hm)
    have hnk : |(n : ℝ) - (k : ℝ)| < c + 1 := by
      calc
        |(n : ℝ) - (k : ℝ)| = |((n : ℝ) - m) + (m - (k : ℝ))| := by
          congr 1
          ring
        _ ≤ |(n : ℝ) - m| + |m - (k : ℝ)| := abs_add_le _ _
        _ < c + 1 := add_lt_add_of_lt_of_le hncenter hfloor
    have hcN : c ≤ (N : ℝ) := by
      simpa only [N] using (Nat.le_ceil c)
    have hnkN : |(n : ℝ) - (k : ℝ)| < (N : ℝ) + 1 := by
      nlinarith
    have hbounds := abs_lt.mp hnkN
    change n ∈ S
    rw [Finset.mem_Icc]
    constructor
    · have hreal : (k : ℝ) < (n : ℝ) + (N : ℝ) + 1 := by
        linarith [hbounds.1]
      have hnat : k < n + N + 1 := by
        exact_mod_cast hreal
      omega
    · have hreal : (n : ℝ) < (k : ℝ) + (N : ℝ) + 1 := by
        linarith [hbounds.2]
      have hnat : n < k + N + 1 := by
        exact_mod_cast hreal
      omega
  have hcardNat : S.card ≤ 2 * N + 1 := by
    simp only [S, Nat.card_Icc]
    omega
  have hN : (N : ℝ) ≤ c + 1 := by
    calc
      (N : ℝ) ≤ ((⌊c⌋₊ : ℕ) : ℝ) + 1 := by
        exact_mod_cast Nat.ceil_le_floor_add_one c
      _ ≤ c + 1 := by
        gcongr
        exact Nat.floor_le hc.le
  have hcard : (S.card : ℝ) ≤ 2 * c + 3 := by
    calc
      (S.card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ = 2 * (N : ℝ) + 1 := by norm_num
      _ ≤ 2 * (c + 1) + 1 := by nlinarith
      _ = 2 * c + 3 := by ring
  have hgoodUpper : μ.real badᶜ ≤ (2 * c + 3) * p := by
    calc
      μ.real badᶜ ≤ μ.real (S : Set ℕ) := measureReal_mono hsubset
      _ = ∑ n ∈ S, μ.real {n} := (sum_measureReal_singleton S).symm
      _ ≤ ∑ n ∈ S, p := Finset.sum_le_sum fun n _ => hatom n
      _ = (S.card : ℝ) * p := by simp
      _ ≤ (2 * c + 3) * p := mul_le_mul_of_nonneg_right hcard hp
  have hmass : (3 : ℝ) / 4 ≤ (2 * c + 3) * p := hgood.trans hgoodUpper
  dsimp [c] at hmass
  nlinarith [mul_nonneg hp hs]

/-- **Corrected Rosenbloom estimate.** Let $f$ be an entire function with Taylor coefficients
$a_n = f^{(n)}(0)/n!$, radial majorant $M_f(r) = \sum_n |a_n|\,|r|^n$, maximum term
$\mu_f(r) = \sup_n |a_n|\,|r|^n$ and logarithmic majorant $g_f(x) = \log M_f(e^x)$. For every real
$x$, $M_f(e^x) \le 8\,\mu_f(e^x)\,\bigl(1 + \sqrt{g_f''(x)}\bigr)$.

The additive $1$ keeps the estimate valid when $g_f''(x) = 0$. -/
theorem wimanMajorant_le_eight_mul_maximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    wimanMajorant f (Real.exp x) ≤
      8 * wimanMaximumTerm f (Real.exp x) *
        (1 + Real.sqrt (iteratedDeriv 2 (wimanGrowth f) x)) := by
  by_cases hne : ∃ n, wimanTaylorCoefficient f n ≠ 0
  · rw [iteratedDeriv_two_wimanGrowth_eq_variance f hf hne x]
    let μ : Measure ℕ := wimanTiltedMeasure f x
    let _ : IsProbabilityMeasure μ := by
      dsimp [μ]
      exact isProbabilityMeasure_wimanTiltedMeasure f hf hne x
    obtain ⟨n₀, hn₀⟩ := hne
    have htermPos : 0 < wimanTerm f (Real.exp x) n₀ := by
      rw [wimanTerm, abs_of_pos (Real.exp_pos x)]
      exact mul_pos (norm_pos_iff.mpr hn₀) (pow_pos (Real.exp_pos x) _)
    have hmajorantPos : 0 < wimanMajorant f (Real.exp x) :=
      htermPos.trans_le (wimanTerm_le_wimanMajorant f hf (Real.exp x) n₀)
    have hmaximumPos : 0 < wimanMaximumTerm f (Real.exp x) :=
      htermPos.trans_le (wimanTerm_le_wimanMaximumTerm f hf (Real.exp x) n₀)
    let p : ℝ :=
      wimanMaximumTerm f (Real.exp x) / wimanMajorant f (Real.exp x)
    have hp : 0 ≤ p := by
      dsimp [p]
      positivity
    have hLp : MemLp (fun n : ℕ => (n : ℝ)) 2 μ := by
      have h := ProbabilityTheory.memLp_tilted_mul
          (X := fun n : ℕ => (n : ℝ)) (μ := wimanCoefficientMeasure f)
          (t := x) (mem_interior_integrableExpSet_wimanCoefficientMeasure f hf x) 2
      norm_num at h ⊢
      simpa only [μ, wimanTiltedMeasure] using h
    have hatom : ∀ n : ℕ, μ.real {n} ≤ p := by
      intro n
      have htermNonneg := wimanTerm_nonneg f (Real.exp x) n
      have hratioNonneg :
          0 ≤ wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x) :=
        div_nonneg htermNonneg hmajorantPos.le
      change ENNReal.toReal (wimanTiltedMeasure f x {n}) ≤ p
      rw [wimanTiltedMeasure_singleton f hf x n,
        ENNReal.toReal_ofReal hratioNonneg]
      dsimp [p]
      exact (div_le_div_iff_of_pos_right hmajorantPos).2
        (wimanTerm_le_wimanMaximumTerm f hf (Real.exp x) n)
    have hnormalized :=
      one_le_eight_mul_atomBound_mul_one_add_sqrt_variance μ hLp p hp hatom
    have hdiv :
        1 ≤
          (8 * wimanMaximumTerm f (Real.exp x) *
            (1 + Real.sqrt
              (ProbabilityTheory.variance (fun n : ℕ => (n : ℝ)) μ))) /
            wimanMajorant f (Real.exp x) := by
      calc
        1 ≤ 8 * p *
            (1 + Real.sqrt
              (ProbabilityTheory.variance (fun n : ℕ => (n : ℝ)) μ)) := hnormalized
        _ =
            (8 * wimanMaximumTerm f (Real.exp x) *
              (1 + Real.sqrt
                (ProbabilityTheory.variance (fun n : ℕ => (n : ℝ)) μ))) /
              wimanMajorant f (Real.exp x) := by
          dsimp [p]
          simp only [div_eq_mul_inv]
          ring
    have hmul := (le_div_iff₀ hmajorantPos).1 hdiv
    simpa only [one_mul, μ] using hmul
  · push Not at hne
    have hmajorant : wimanMajorant f (Real.exp x) = 0 := by
      simp [wimanMajorant, wimanTerm, hne]
    have hmaximumNonneg : 0 ≤ wimanMaximumTerm f (Real.exp x) :=
      (wimanTerm_nonneg f (Real.exp x) 0).trans
        (wimanTerm_le_wimanMaximumTerm f hf (Real.exp x) 0)
    rw [hmajorant]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hmaximumNonneg)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _))

end

end Complex
