/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.GaltonWatson

@[expose] public section

open MeasureTheory Filter Topology Set MathlibExt.Probability MathlibExt.Probability.GaltonWatson
open scoped ENNReal

namespace MathlibExtTest.Probability.BranchingProcess.GaltonWatson

/-! ### Definitions unfold as expected -/

/-- The process starts from one individual. -/
example (ν : Measure ℕ) : law ν 0 = Measure.dirac 1 := rfl

/-- One individual's offspring total is the offspring law: `ν^{∗1} = ν ∗ δ₀`. -/
example (ν : Measure ℕ) : convPow ν 1 = ν ∗ Measure.dirac 0 := rfl

/-- The generation laws are probability measures. -/
example (ν : Measure ℕ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (law ν 3) :=
  inferInstance

/-! ### Sterile offspring law `δ₀`: extinction in one generation -/

/-- `P(Z_1 = 0) = f(0) = 1` for `ν = δ₀`. -/
example : (law (Measure.dirac 0) 1).real {0} = 1 := by
  rw [law_real_zero, Function.iterate_one, pgf_zero id _ measurable_id]
  simp

/-- With sterile offspring the mean is `0` and extinction is certain. -/
example : extinctionProb (Measure.dirac 0) = 1 := by
  rw [extinctionProb_eq_one_iff _ (by simp)]
  simp [mean]

/-- `E Z_n = 0 ^ n` for `ν = δ₀`. -/
example (n : ℕ) : ∫⁻ k, (k : ℝ≥0∞) ∂(law (Measure.dirac 0) n) = 0 ^ n := by
  rw [lintegral_law]
  simp [mean]

/-! ### Binary splitting `δ₂`: the population doubles and never dies out -/

/-- The mean of `δ₂` is `2`. -/
example : mean (Measure.dirac 2) = 2 := by
  simp [mean]

/-- `E Z_n = 2 ^ n` for binary splitting. -/
example (n : ℕ) : ∫⁻ k, (k : ℝ≥0∞) ∂(law (Measure.dirac 2) n) = 2 ^ n := by
  rw [lintegral_law]
  simp [mean]

/-- The generating function of `δ₂` is `s ^ 2`. -/
example (s : ℝ) : pgf id (Measure.dirac 2) s = s ^ 2 := by
  simp [pgf]

/-- Binary splitting never dies out: the least fixed point of `s ↦ s ^ 2` is `0`. -/
example : extinctionProb (Measure.dirac 2) = 0 := by
  have h := (isLeast_extinctionProb (Measure.dirac 2)).2
    (show (0 : ℝ) ∈ {s | s ∈ Icc (0 : ℝ) 1 ∧ pgf id (Measure.dirac 2) s = s} from
      ⟨⟨le_rfl, zero_le_one⟩, by simp [pgf]⟩)
  exact le_antisymm h (isLeast_extinctionProb (Measure.dirac 2)).1.1.1

/-! ### The degenerate law `δ₁` is excluded from the criticality theorem -/

/-- With `ν = δ₁` every iterate of `f = id` at `0` is `0`, so extinction never happens although
`m = 1`; this is why `extinctionProb_eq_one_iff` assumes `ν {1} ≠ 1`. -/
example : extinctionProb (Measure.dirac 1) = 0 := by
  have h := (isLeast_extinctionProb (Measure.dirac 1)).2
    (show (0 : ℝ) ∈ {s | s ∈ Icc (0 : ℝ) 1 ∧ pgf id (Measure.dirac 1) s = s} from
      ⟨⟨le_rfl, zero_le_one⟩, by simp [pgf]⟩)
  exact le_antisymm h (isLeast_extinctionProb (Measure.dirac 1)).1.1.1

/-- `P(Z_n = 0)` converges to the extinction probability. -/
example (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    Tendsto (fun n => (law ν n).real {0}) atTop (𝓝 (extinctionProb ν)) :=
  tendsto_law_real_zero ν

/-- The generating function of `Z_2` under binary splitting is `s ^ 4`. -/
example (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : pgf id (law (Measure.dirac 2) 2) s = s ^ 4 := by
  rw [pgf_law _ 2 hs]
  simp [pgf]
  ring

/-- Iterates of the generating function stay in `[0, 1]`, and `P(Z_n = 0)` is monotone. -/
example (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    (pgf id ν)^[5] (1 / 2) ∈ Icc (0 : ℝ) 1 ∧ (law ν 2).real {0} ≤ (law ν 3).real {0} :=
  ⟨iterate_pgf_mem_Icc ν 5 ⟨by norm_num, by norm_num⟩, monotone_law_real_zero ν (by norm_num)⟩

end MathlibExtTest.Probability.BranchingProcess.GaltonWatson
