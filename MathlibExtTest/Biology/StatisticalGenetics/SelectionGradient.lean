/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.SelectionGradient
public import MathlibExt.Biology.StatisticalGenetics.SelectionGradientMultivariate

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.SelectionGradient
open scoped NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.SelectionGradient

/-! ### Stein's lemma with `g = id`: the variance (non-vacuity witness)

For `g x = x`, Stein's lemma reads `𝔼[(z - μ) z] = v`. -/

example (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) : ∫ x, (x - μ) * x ∂gaussianReal μ v = v := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hsq : Integrable (fun x : ℝ => x * x) (gaussianReal μ v) := by
    simpa [sq] using (memLp_id_gaussianReal 2).integrable_sq
  have hxg : Integrable (fun x : ℝ => (x - μ) * x) (gaussianReal μ v) := by
    refine (hsq.sub (hid.const_mul μ)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [integral_sub_mul_gaussianReal hv (g := fun x => x) (g' := fun _ => 1)
    (fun x => hasDerivAt_id x) hid hxg (integrable_const 1)]
  simp

/-! ### Constant fitness: no selection -/

/-- Constant fitness `W = 1`: mean fitness `1`. -/
theorem meanFitness_one (μ : ℝ) (v : ℝ≥0) : meanFitness (fun _ => 1) μ v = 1 := by
  simp [meanFitness]

/-- Constant fitness gives no selection differential. -/
theorem selectionDifferential_one (μ : ℝ) (v : ℝ≥0) :
    selectionDifferential (fun _ => 1) μ v = 0 := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  rw [selectionDifferential, meanFitness_one]
  simp only [mul_one, div_one]
  rw [integral_sub hid (integrable_const μ)]
  simp [integral_id_gaussianReal]

/-- The hypotheses of Lande's equation are satisfiable; here both sides vanish. -/
example (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (v : ℝ) * deriv (fun m => Real.log (meanFitness (fun _ => 1) m v)) μ = 0 := by
  rw [← selectionDifferential_eq_mul_deriv_log measurable_const ⟨1, fun _ => by simp⟩ hv
    (by rw [meanFitness_one]; exact one_ne_zero), selectionDifferential_one]

/-- The Lande–Arnold form with constant fitness: `S / v = 𝔼[W'] / w̄ = 0`. -/
example (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    selectionDifferential (fun _ => 1) μ v / v = 0 := by
  rw [selectionDifferential_div_eq (W' := fun _ => 0) (fun z => hasDerivAt_const z 1)
    ⟨1, fun _ => by simp⟩ hv (integrable_const 0)]
  simp

/-- Junk value outside the domain: zero fitness has zero mean fitness, and the selection
differential divides by zero and returns `0`. -/
example (μ : ℝ) (v : ℝ≥0) : selectionDifferential (fun _ => 0) μ v = 0 := by
  simp [selectionDifferential, meanFitness]

/-! ### Multivariate: constant fitness with identity covariance -/

/-- Constant fitness `W = 1` has mean fitness `1` for any trait law. -/
theorem meanFitnessMV_one (P : Matrix (Fin 2) (Fin 2) ℝ) (μ : EuclideanSpace ℝ (Fin 2)) :
    meanFitnessMV (fun _ => 1) P μ = 1 := by
  simp [meanFitnessMV]

/-- The hypotheses of the multivariate Lande equation are satisfiable (identity covariance,
constant fitness). -/
example (μ : EuclideanSpace ℝ (Fin 2)) :
    selectionDifferentialMV (fun _ => 1) 1 μ =
      Matrix.toEuclideanCLM (𝕜 := ℝ) 1
        (gradient (fun m => Real.log (meanFitnessMV (fun _ => 1) 1 m)) μ) :=
  selectionDifferentialMV_eq measurable_const ⟨1, fun _ => by simp⟩ Matrix.PosDef.one
    (by rw [meanFitnessMV_one]; exact one_ne_zero)

/-! ### Truncation fitness: Lande's equation applies, the Stein form does not -/

/-- The truncation fitness `W = 1_{z > 0}` is measurable and bounded. -/
example : Measurable ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) :=
  measurable_const.indicator measurableSet_Ioi

example : ∃ C, ∀ z, |(Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) z| ≤ C :=
  ⟨1, fun z => by by_cases h : z ∈ Set.Ioi (0 : ℝ) <;> simp [Set.indicator, h]⟩

/-- On `N(0, 1)`, truncation selection has differential `√(2/π)`. -/
example : selectionDifferential ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) 0 1 =
    Real.sqrt (2 / Real.pi) := by
  simpa only [selectionDifferential, meanFitness, sub_zero] using
    integral_mul_indicator_Ioi_div_eq_sqrt

/-- Hence Lande's equation applies and gives `d/dμ log w̄(0) = √(2/π)`. -/
example : Real.sqrt (2 / Real.pi) =
    (1 : NNReal) * deriv
      (fun m => Real.log (meanFitness ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) m 1)) 0 := by
  have hS : selectionDifferential ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) 0 1 =
      Real.sqrt (2 / Real.pi) := by
    simpa only [selectionDifferential, meanFitness, sub_zero] using
      integral_mul_indicator_Ioi_div_eq_sqrt
  have hmean : meanFitness ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) 0 1 ≠ 0 := by
    intro h
    rw [selectionDifferential, h, div_zero] at hS
    exact (Real.sqrt_pos.mpr (div_pos two_pos Real.pi_pos)).ne' hS.symm
  rw [← hS]
  exact selectionDifferential_eq_mul_deriv_log
    (measurable_const.indicator measurableSet_Ioi)
    ⟨1, fun z => by by_cases h : z ∈ Set.Ioi (0 : ℝ) <;> simp [Set.indicator, h]⟩
    one_ne_zero hmean

/-- The indicator has derivative `0` away from `0`, but no derivative at `0`; the Stein form's
everywhere-differentiability hypothesis fails. -/
example : HasDerivAt ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) 0 (1 : ℝ) :=
  hasDerivAt_indicator_Ioi_of_ne one_ne_zero

example : ¬ ∃ W' : ℝ → ℝ, ∀ z,
    HasDerivAt ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) (W' z) z :=
  not_forall_hasDerivAt_indicator_Ioi

#print axioms integral_mul_indicator_Ioi_div_eq_sqrt
#print axioms hasDerivAt_indicator_Ioi_of_ne
#print axioms not_forall_hasDerivAt_indicator_Ioi

end MathlibExtTest.Biology.StatisticalGenetics.SelectionGradient
