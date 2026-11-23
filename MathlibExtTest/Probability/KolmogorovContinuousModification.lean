/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovContinuousModification

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.KolmogorovContinuousModification

open MathlibExt.Probability.KolmogorovContinuousModification

private lemma min_one_pow_four_le (s t : NNReal) :
    dist (min (s : ℝ) 1) (min (t : ℝ) 1) ^ 4 ≤ dist s t ^ 2 := by
  let d := dist (min (s : ℝ) 1) (min (t : ℝ) 1)
  let e := dist s t
  have hd0 : 0 ≤ d := dist_nonneg
  have he0 : 0 ≤ e := dist_nonneg
  have hde : d ≤ e := by
    dsimp [d, e]
    rw [Real.dist_eq, NNReal.dist_eq]
    simpa using abs_min_sub_min_le_max (s : ℝ) 1 (t : ℝ) 1
  have hs0 : 0 ≤ min (s : ℝ) 1 := by positivity
  have ht0 : 0 ≤ min (t : ℝ) 1 := by positivity
  have hs1 : min (s : ℝ) 1 ≤ 1 := min_le_right _ _
  have ht1 : min (t : ℝ) 1 ≤ 1 := min_le_right _ _
  have hd1 : d ≤ 1 := by
    dsimp [d]
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hd2e2 : d ^ 2 ≤ e ^ 2 := by nlinarith
  have hd2one : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
  have hprod : 0 ≤ d ^ 2 * (1 - d ^ 2) :=
    mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd2one)
  have hd4d2 : d ^ 4 ≤ d ^ 2 := by nlinarith
  exact hd4d2.trans hd2e2

/-- The `M = 0` case produces one measurable, everywhere-continuous
modification with exact initial value and preservation of the closed range
`[2, 3]`. In particular, the exceptional-set fallback cannot be zero. -/
example :
    ∃ Y : NNReal → Unit → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous fun t => Y t ω) ∧
      (∀ t, Y t =ᵐ[Measure.dirac ()] fun _ => 2) ∧
      (∀ ω, Y 0 ω = 2) ∧
      (∀ ω t, Y t ω ∈ Set.Icc (2 : ℝ) 3) := by
  have hX : ProbabilityTheory.IsKolmogorovProcess
      (fun _ : NNReal => fun _ : Unit => (2 : ℝ)) (Measure.dirac ()) 4 2 0 :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
      (fun _ => measurable_const) (by
        intro s t
        simp) (by norm_num) (by norm_num)
  obtain ⟨Y, hmeas, hcont, hae, hzero, hrange⟩ :=
    exists_continuous_modification hX (by norm_num)
  refine ⟨Y, hmeas, hcont, hae, ?_, ?_⟩
  · intro ω
    simpa using hzero ω
  · intro ω
    rcases ω with ⟨⟩
    exact hrange (Set.Icc (2 : ℝ) 3) isClosed_Icc () (fun _ => by norm_num)

/-- The bounded nonconstant path `t ↦ min(t, 1)` satisfies a global
`p = 4`, `q = 2` Kolmogorov bound and receives an everywhere-continuous
`[0, 1]`-valued modification with exact initial value zero. -/
example :
    ∃ Y : NNReal → Unit → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous fun t => Y t ω) ∧
      (∀ t, Y t =ᵐ[Measure.dirac ()] fun _ => min (t : ℝ) 1) ∧
      (∀ ω, Y 0 ω = 0) ∧
      (∀ ω t, Y t ω ∈ Set.Icc (0 : ℝ) 1) := by
  have hX : ProbabilityTheory.IsKolmogorovProcess
      (fun t : NNReal => fun _ : Unit => min (t : ℝ) 1)
      (Measure.dirac ()) 4 2 1 :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
      (fun _ => measurable_const) (by
        intro s t
        rw [lintegral_dirac, ENNReal.coe_one, one_mul, edist_dist, edist_dist,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        apply ENNReal.ofReal_le_ofReal
        norm_num [Real.rpow_natCast]
        exact min_one_pow_four_le s t) (by norm_num) (by norm_num)
  obtain ⟨Y, hmeas, hcont, hae, hzero, hrange⟩ :=
    exists_continuous_modification hX (by norm_num)
  refine ⟨Y, hmeas, hcont, hae, ?_, ?_⟩
  · intro ω
    simpa using hzero ω
  · intro ω
    rcases ω with ⟨⟩
    apply hrange (Set.Icc (0 : ℝ) 1) isClosed_Icc ()
    intro t
    exact ⟨by positivity, min_le_right _ _⟩

end MathlibExtTest.Probability.KolmogorovContinuousModification
