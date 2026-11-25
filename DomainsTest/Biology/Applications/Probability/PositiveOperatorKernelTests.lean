/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.TransitionKernel

/-! Wright–Fisher transition laws on the allele-frequency interval. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

namespace MathlibExt.Probability.PositiveOperatorKernelTest

open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

/-- One-half as a point of the Wright–Fisher allele-frequency interval. -/
noncomputable def halfFrequency : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-- Every Wright–Fisher transition from one-half has probability mass one. -/
example (t : ℝ) : wfTransitionKernel t halfFrequency Set.univ = 1 :=
  measure_univ

/-- At time zero, the actual Wright–Fisher transition from one-half is Dirac. -/
example : wfTransitionKernel 0 halfFrequency = Measure.dirac halfFrequency :=
  wfTransitionKernel_zero_apply halfFrequency

/-- The documented nonpositive-time convention gives the identity kernel. -/
example : wfTransitionKernel (-1) = (Kernel.id : Kernel I I) :=
  wfTransitionKernel_of_nonpos (by norm_num)

/-- The Chapman–Kolmogorov law specializes to concrete positive times on the interval. -/
example : wfTransitionKernel (1 + 2) = wfTransitionKernel 2 ∘ₖ wfTransitionKernel 1 := by
  exact wfTransitionKernel_add (by norm_num) (by norm_num)

/-- The actual Wright–Fisher transition from `1/2` has the block-counting moment formula. -/
example {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫ y, ((Polynomial.X ^ n : Polynomial ℝ).toContinuousMapOn I) y ∂
        wfTransitionKernel t halfFrequency =
      ∑ k : Fin (n + 1),
        NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) k *
          (halfFrequency : ℝ) ^ (k : ℕ) :=
  integral_wfTransitionKernel_X_pow ht n halfFrequency

end MathlibExt.Probability.PositiveOperatorKernelTest
