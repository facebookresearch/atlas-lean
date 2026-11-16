/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Hausdorff moment determinacy on `[0, 1]`

A finite Borel measure on the unit interval is determined by all of its
moments `∫ x ^ n`, `n ≥ 0`. The proof is the standard one: equality of moments
gives equality of all polynomial integrals; Weierstrass approximation extends
this to bounded continuous test functions; measure extensionality for finite
measures then gives equality of the measures.

## Main result

* `measure_eq_of_forall_integral_pow_eq`: two finite measures on `I` with the
  same moments of every order are equal.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and
  Convergence*, Wiley (1986), ch. 4.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

open MeasureTheory
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

end MathlibExt.Biology.PopulationGenetics.Diffusion
