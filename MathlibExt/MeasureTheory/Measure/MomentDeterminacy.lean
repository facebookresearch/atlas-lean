/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Compactly supported measures are determined by their moments

A finite measure carried by a compact interval is determined by its moments. Equality of moments
gives equality of all polynomial integrals; Weierstrass approximation extends this to bounded
continuous test functions; measure extensionality for finite measures then gives equality of the
measures. On the unit interval this is Hausdorff moment determinacy; the same argument applies to
two finite measures on `ℝ` supported in a common interval `[a, b]`. A finite measure whose even
moments grow at most like `C R²ᵏ` is supported in `[-R, R]`, by Markov's inequality applied to
`x²ᵏ` with `k → ∞`. Together these give the uniqueness half of the moment method: a measure with
the moments of a compactly supported law is that law.

## Main results

* `MeasureTheory.measure_eq_of_forall_integral_pow_eq`: two finite measures on `I` with the same
  moments of every order are equal.
* `MeasureTheory.measure_lt_abs_eq_zero_of_integral_pow_le`: if `∫ x²ᵏ dμ ≤ C R²ᵏ` for all `k`,
  then `μ {x | R < |x|} = 0`.
* `MeasureTheory.ext_of_forall_integral_pow_eq_of_compl_Icc`: two finite measures supported in
  `[a, b]` with equal moments are equal.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and
  Convergence*, Wiley (1986), ch. 4.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  §2.2.3 (the moment method) and §2.4.2, where these facts identify the limit in the
  semicircular law.
* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Theorem 30.1 (a law determined
  by its moments); compact support is the simplest sufficient condition.
-/

@[expose] public section

namespace MeasureTheory

open scoped unitInterval

/-- **Hausdorff moment determinacy on `[0, 1]`.** Two finite Borel measures on the unit interval
with the same moments `∫ x ^ n`, for every `n ≥ 0`, are equal. (The `n = 0` moment is the total
mass.) -/
theorem measure_eq_of_forall_integral_pow_eq (μ ν : Measure I) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ n : ℕ, ∫ x, (x : ℝ) ^ n ∂μ = ∫ x, (x : ℝ) ^ n ∂ν) :
    μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hpow : ∀ (m : Measure I) [IsFiniteMeasure m] (n : ℕ),
      Integrable (fun x : I => (x : ℝ) ^ n) m := fun m _ n =>
    integrableOn_univ.mp
      ((continuous_subtype_val.pow n).continuousOn.integrableOn_compact isCompact_univ)
  have hpoly : ∀ p : Polynomial ℝ,
      ∫ x, p.eval (x : ℝ) ∂μ = ∫ x, p.eval (x : ℝ) ∂ν := fun p => by
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [integral_finsetSum _ (fun i _ => ((hpow μ i).const_mul _)),
      integral_finsetSum _ (fun i _ => ((hpow ν i).const_mul _))]
    simp only [integral_const_mul, h]
  have hC : 0 ≤ μ.real Set.univ + ν.real Set.univ :=
    add_nonneg measureReal_nonneg measureReal_nonneg
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  refine eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _) fun c hc => ?_
  have hC1 : (0 : ℝ) < μ.real Set.univ + ν.real Set.univ + 1 := by linarith
  set δ : ℝ := c / (μ.real Set.univ + ν.real Set.univ + 1) with hδ
  have hδpos : 0 < δ := div_pos hc hC1
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f.toContinuousMap δ hδpos
  have hpt : ∀ x : I, ‖f x - p.eval (x : ℝ)‖ ≤ δ := fun x => by
    have h1 := ContinuousMap.norm_coe_le_norm
      (p.toContinuousMapOn (Set.Icc 0 1) - f.toContinuousMap) x
    have h2 : (p.toContinuousMapOn (Set.Icc 0 1) - f.toContinuousMap) x =
        p.eval (x : ℝ) - f x := by
      simp
    rw [norm_sub_rev, ← h2]
    exact le_trans h1 (le_of_lt hp)
  have hpfμ : Integrable (fun x : I => p.eval (x : ℝ)) μ := by
    simp_rw [Polynomial.eval_eq_sum_range]
    exact integrable_finsetSum _ (fun i _ => ((hpow μ i).const_mul _))
  have hpfν : Integrable (fun x : I => p.eval (x : ℝ)) ν := by
    simp_rw [Polynomial.eval_eq_sum_range]
    exact integrable_finsetSum _ (fun i _ => ((hpow ν i).const_mul _))
  have e1 : ‖(∫ x, f x ∂μ) - (∫ x, p.eval (x : ℝ) ∂μ)‖ ≤ δ * μ.real Set.univ := by
    rw [← integral_sub (f.integrable μ) hpfμ]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
  have e2 : ‖(∫ x, f x ∂ν) - (∫ x, p.eval (x : ℝ) ∂ν)‖ ≤ δ * ν.real Set.univ := by
    rw [← integral_sub (f.integrable ν) hpfν]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
  have hdecomp : (∫ x, f x ∂μ) - (∫ x, f x ∂ν) =
      ((∫ x, f x ∂μ) - (∫ x, p.eval (x : ℝ) ∂μ)) -
        ((∫ x, f x ∂ν) - (∫ x, p.eval (x : ℝ) ∂ν)) := by
    rw [hpoly p]; ring
  have hfin : δ * (μ.real Set.univ + ν.real Set.univ) ≤ c := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hC1]
    nlinarith [hc, hC]
  calc |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| = ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ :=
        (Real.norm_eq_abs _).symm
    _ = ‖((∫ x, f x ∂μ) - (∫ x, p.eval (x : ℝ) ∂μ)) -
        ((∫ x, f x ∂ν) - (∫ x, p.eval (x : ℝ) ∂ν))‖ := by rw [hdecomp]
    _ ≤ ‖(∫ x, f x ∂μ) - (∫ x, p.eval (x : ℝ) ∂μ)‖ +
        ‖(∫ x, f x ∂ν) - (∫ x, p.eval (x : ℝ) ∂ν)‖ := norm_sub_le _ _
    _ ≤ δ * μ.real Set.univ + δ * ν.real Set.univ := add_le_add e1 e2
    _ = δ * (μ.real Set.univ + ν.real Set.univ) := by ring
    _ ≤ c := hfin

section CompactSupport

open Set Filter Polynomial
open scoped Topology

/-- **Moment bounds confine the support.** If a finite measure `μ` on `ℝ` has integrable even
powers with `∫ x²ᵏ dμ ≤ C R²ᵏ` for every `k` (`R > 0`), then `μ` gives no mass to
`{x | R < |x|}` (Markov's inequality for `x²ᵏ`, letting `k → ∞`; Tao, *Topics in Random Matrix
Theory*, §2.2.3). -/
theorem measure_lt_abs_eq_zero_of_integral_pow_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    {C R : ℝ} (hR : 0 < R) (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ (2 * k)) μ)
    (hbound : ∀ k : ℕ, ∫ x, x ^ (2 * k) ∂μ ≤ C * R ^ (2 * k)) :
    μ {x | R < |x|} = 0 := by
  -- First, `μ {x | r ≤ |x|} = 0` for every `r > R`.
  have key : ∀ r : ℝ, R < r → μ {x | r ≤ |x|} = 0 := by
    intro r hr
    have hr0 : 0 < r := hR.trans hr
    have hle : ∀ k : ℕ, μ.real {x | r ≤ |x|} ≤ C * (R / r) ^ (2 * k) := by
      intro k
      have hpos : 0 < r ^ (2 * k) := by positivity
      have hmk := mul_meas_ge_le_integral_of_nonneg
        (Eventually.of_forall fun x : ℝ => (even_two_mul k).pow_nonneg x) (hint k) (r ^ (2 * k))
      have hsub : {x : ℝ | r ≤ |x|} ⊆ {x | r ^ (2 * k) ≤ x ^ (2 * k)} := by
        intro x hx
        change r ≤ |x| at hx
        change r ^ (2 * k) ≤ x ^ (2 * k)
        rw [pow_mul, pow_mul, ← sq_abs x]
        exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hr0.le hx 2) k
      have hmono : μ.real {x | r ≤ |x|} ≤ μ.real {x | r ^ (2 * k) ≤ x ^ (2 * k)} :=
        measureReal_mono hsub
      rw [div_pow, mul_div_assoc', le_div_iff₀ hpos]
      calc μ.real {x | r ≤ |x|} * r ^ (2 * k)
          ≤ μ.real {x | r ^ (2 * k) ≤ x ^ (2 * k)} * r ^ (2 * k) := by gcongr
        _ = r ^ (2 * k) * μ.real {x | r ^ (2 * k) ≤ x ^ (2 * k)} := mul_comm _ _
        _ ≤ ∫ x, x ^ (2 * k) ∂μ := hmk
        _ ≤ C * R ^ (2 * k) := hbound k
    have hlim : Tendsto (fun k : ℕ => C * (R / r) ^ (2 * k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => ((R / r) ^ 2) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
          (by rw [sq_lt_one_iff₀ (by positivity)]; exact (div_lt_one hr0).mpr hr)
      simpa [pow_mul] using h1.const_mul C
    have h0 : μ.real {x | r ≤ |x|} ≤ 0 := ge_of_tendsto' hlim hle
    exact (measureReal_eq_zero_iff).mp (le_antisymm h0 measureReal_nonneg)
  have hU : {x : ℝ | R < |x|} = ⋃ n : ℕ, {x | R + 1 / ((n : ℝ) + 1) ≤ |x|} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hU]
  exact measure_iUnion_null fun n => key _ (by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith)

/-- **Compactly supported measures are determined by their moments.** Two finite measures on
`ℝ` that give no mass outside `[a, b]` and have the same moments `∫ xᵏ` for every `k` are equal
(proved by Weierstrass approximation; for probability measures it is also implied by Billingsley,
*Probability and Measure*, 3rd ed., Theorem 30.1). -/
theorem ext_of_forall_integral_pow_eq_of_compl_Icc {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {a b : ℝ} (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    (heq : ∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) : μ = ν := by
  have hμK : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)
  have hνK : ν.restrict (Icc a b) = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)
  -- Polynomials have the same integral over `[a, b]` against both measures.
  have hpoly : ∀ p : ℝ[X], ∫ x in Icc a b, p.eval x ∂μ = ∫ x in Icc a b, p.eval x ∂ν := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [eval_add]
      rw [integral_add (p.continuous.integrableOn_Icc) (q.continuous.integrableOn_Icc),
        integral_add (p.continuous.integrableOn_Icc) (q.continuous.integrableOn_Icc), hp, hq]
    | monomial k c =>
      simp only [eval_monomial]
      rw [integral_const_mul, integral_const_mul, hμK, hνK, heq k]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [← hμK, ← hνK]
  set M := μ.real (Icc a b) + ν.real (Icc a b) with hM
  have hM0 : 0 ≤ M := by positivity
  have hclose : ∀ ε : ℝ, 0 < ε →
      |∫ x in Icc a b, f x ∂μ - ∫ x in Icc a b, f x ∂ν| ≤ ε * M := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f f.continuous.continuousOn ε hε
    have hfi : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ → IntegrableOn (fun x => f x) (Icc a b) ρ :=
      fun ρ _ => f.continuous.integrableOn_Icc
    have hest : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ →
        |∫ x in Icc a b, f x ∂ρ - ∫ x in Icc a b, p.eval x ∂ρ| ≤ ε * ρ.real (Icc a b) := by
      intro ρ hρ
      rw [← integral_sub (hfi ρ hρ) p.continuous.integrableOn_Icc, ← Real.norm_eq_abs]
      refine norm_setIntegral_le_of_norm_le_const (measure_lt_top ρ _) fun x hx => ?_
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact (hp x hx).le
    have h1 := hest μ inferInstance
    have h2 := hest ν inferInstance
    rw [hpoly p] at h1
    calc |∫ x in Icc a b, f x ∂μ - ∫ x in Icc a b, f x ∂ν|
        = |(∫ x in Icc a b, f x ∂μ - ∫ x in Icc a b, p.eval x ∂ν) -
            (∫ x in Icc a b, f x ∂ν - ∫ x in Icc a b, p.eval x ∂ν)| := by ring_nf
      _ ≤ |∫ x in Icc a b, f x ∂μ - ∫ x in Icc a b, p.eval x ∂ν| +
            |∫ x in Icc a b, f x ∂ν - ∫ x in Icc a b, p.eval x ∂ν| := abs_sub _ _
      _ ≤ ε * μ.real (Icc a b) + ε * ν.real (Icc a b) := add_le_add h1 h2
      _ = ε * M := by rw [hM]; ring
  by_contra hne
  have hd : 0 < |∫ x in Icc a b, f x ∂μ - ∫ x in Icc a b, f x ∂ν| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  set d := |∫ x in Icc a b, f x ∂μ - ∫ x in Icc a b, f x ∂ν|
  have := hclose (d / (2 * (M + 1))) (by positivity)
  have h3 : d / (2 * (M + 1)) * M < d := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end CompactSupport

end MeasureTheory
