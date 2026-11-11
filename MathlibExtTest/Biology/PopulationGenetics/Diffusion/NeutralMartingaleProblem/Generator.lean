/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Generator

@[expose] public section

open MeasureTheory Set Polynomial
open scoped NNReal unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Generator

open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess

/-! ### The semigroup identity -/

-- The generator kills the identity polynomial, so the semigroup fixes the allele frequency.
private theorem wfSemigroup_X {T : ℝ} (hT : 0 ≤ T) :
    wfSemigroup T ((Polynomial.X : ℝ[X]).toContinuousMapOn I) =
      (Polynomial.X : ℝ[X]).toContinuousMapOn I := by
  have h := wfSemigroup_sub_eq_integral (Polynomial.X : ℝ[X]) hT
  have h0 : polyGenerator (Polynomial.X : ℝ[X]) = 0 := by simp [polyGenerator]
  have h00 : (0 : ℝ[X]).toContinuousMapOn I = 0 := by ext; simp
  rw [h0, h00] at h
  simp only [map_zero, intervalIntegral.integral_zero] at h
  exact sub_eq_zero.1 h

example : wfSemigroup 2 ((Polynomial.X : ℝ[X]).toContinuousMapOn I) =
    (Polynomial.X : ℝ[X]).toContinuousMapOn I :=
  wfSemigroup_X (by norm_num)

-- At time zero both sides of the identity vanish.
example (p : ℝ[X]) :
    wfSemigroup 0 (p.toContinuousMapOn I) - p.toContinuousMapOn I =
      ∫ u in (0 : ℝ)..0, wfSemigroup u ((polyGenerator p).toContinuousMapOn I) :=
  wfSemigroup_sub_eq_integral p le_rfl

/-! ### `C²` polynomial approximation -/

-- A non-polynomial `C²` function: the exponential.
example : ∃ p : ℝ[X], ∀ x ∈ Icc (0 : ℝ) 1,
    |p.eval x - Real.exp x| ≤ 1 / 100 ∧ |(derivative p).eval x - deriv Real.exp x| ≤ 1 / 100 ∧
      |(derivative (derivative p)).eval x - deriv (deriv Real.exp) x| ≤ 1 / 100 :=
  exists_polynomial_near_contDiff_two Real.contDiff_exp (by norm_num)

/-! ### Non-vacuity of the Markov hypothesis: the process absorbed at `0` -/

-- From `0` the semigroup stays at `0`: positivity plus `P_u X = X`.
private theorem wfSemigroup_apply_zero {u : ℝ} (hu : 0 ≤ u) (g : C(I, ℝ)) :
    wfSemigroup u g 0 = g 0 := by
  set x : C(I, ℝ) := (Polynomial.X : ℝ[X]).toContinuousMapOn I
  have hx : ∀ y : I, x y = (y : ℝ) := fun y => by simp [x]
  have hPx : wfSemigroup u x 0 = 0 := by
    rw [wfSemigroup_X hu, hx]
    rfl
  refine eq_of_forall_dist_le fun ε hε => ?_
  -- Continuity of `g` at `0`, and a linear bound away from `0`.
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuous_iff.1 g.continuous 0 ε hε
  set C := 2 * ‖g‖ / δ
  have hbound : ∀ y : I, |g y - g 0| ≤ ε + C * y := by
    intro y
    by_cases hy : dist y 0 < δ
    · have := (hgδ y hy).le
      rw [Real.dist_eq] at this
      have : 0 ≤ C * y := mul_nonneg (by positivity) y.2.1
      linarith
    · have hyδ : δ ≤ y := by
        rw [not_lt, Subtype.dist_eq, Real.dist_eq] at hy
        simpa [abs_of_nonneg y.2.1] using hy
      have h1 : |g y - g 0| ≤ 2 * ‖g‖ := by
        have := abs_sub (g y) (g 0)
        have := g.norm_coe_le_norm y
        have := g.norm_coe_le_norm 0
        rw [Real.norm_eq_abs] at *
        linarith
      have h2 : 2 * ‖g‖ ≤ C * y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
        exact mul_le_mul_of_nonneg_left hyδ (by positivity)
      linarith
  -- Positivity of the semigroup applied to the two one-sided bounds.
  have hup : 0 ≤ (ContinuousMap.const I ε + C • x) - (g - ContinuousMap.const I (g 0)) :=
    fun y => by
      have := (abs_le.1 (hbound y)).2
      simp [hx]
      linarith
  have hlo : 0 ≤ (g - ContinuousMap.const I (g 0)) + (ContinuousMap.const I ε + C • x) :=
    fun y => by
      have := (abs_le.1 (hbound y)).1
      simp [hx]
      linarith
  have hconst : ∀ c : ℝ, wfSemigroup u (ContinuousMap.const I c) = ContinuousMap.const I c :=
    fun c => by
      have h := wfSemigroup_apply_one u
      have : ContinuousMap.const I c = c • (1 : C(I, ℝ)) := by ext; simp
      rw [this, map_smul, h]
  have h1 := ContinuousMap.le_def.mp (wfSemigroup_nonneg u hup) 0
  have h2 := ContinuousMap.le_def.mp (wfSemigroup_nonneg u hlo) 0
  simp only [map_sub, map_add, map_smul, hconst] at h1 h2
  simp [hPx] at h1 h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

-- The constant process at `0` is Markov for the Wright–Fisher semigroup, so the main theorem
-- applies to it: the hypotheses are satisfiable.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    IsWrightFisherSolution 0 ℱ μ (fun _ _ => (0 : ℝ)) := by
  refine isWrightFisherSolution_zero_of_markov (fun _ _ => ⟨le_rfl, zero_le_one⟩)
    (fun _ => continuous_const) (fun _ => stronglyMeasurable_const) fun s t hst g => ?_
  rw [condExp_const (ℱ.le s)]
  refine Filter.Eventually.of_forall fun _ => ?_
  have h0 : projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := projIcc_left _
  simp only [h0]
  exact (wfSemigroup_apply_zero (sub_nonneg.2 (NNReal.coe_le_coe.2 hst)) g).symm

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Generator
