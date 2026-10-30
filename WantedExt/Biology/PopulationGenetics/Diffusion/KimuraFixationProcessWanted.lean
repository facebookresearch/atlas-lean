/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Process-level fixation probability and absorption time of the Wright–Fisher diffusion

`MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher` proves the analytic half of
Kimura's theory: Kimura's formula `kimuraFixation σ` is the unique solution of the backward
boundary-value problem `L_σ u = 0`, `u 0 = 0`, `u 1 = 1`, and the Kimura–Ohta function
`meanAbsorptionTime` solves `L_0 T = -1`, `T 0 = T 1 = 0`. This file records the probabilistic
half: these functions are the fixation probability and the mean absorption time of the
diffusion process itself.

The process is specified by the martingale problem of Stroock and Varadhan (Ethier–Kurtz
1986, ch. 4 and 8; ch. 10 for Wright–Fisher, where the problem is shown to be well posed): a
continuous `[0, 1]`-valued process `X`, adapted to a filtration `ℱ` indexed by time
`t : ℝ≥0` (units of `2N` generations), such that for every `C²` test function `f`,
`f (X t) - f (X 0) - ∫₀ᵗ (L_σ f) (X s) ds` is an `ℱ`-martingale, where
`L_σ f = x (1 - x) / 2 · f'' + σ x (1 - x) · f'` is `Diffusion.generator σ f` and
`σ = 2Ns` is the scaled genic selection coefficient (`IsWrightFisherSolution`). Such a process
started at `x` is absorbed at `0` or `1` in finite time almost surely, it is eventually equal
to `1` with probability `kimuraFixation σ x`, and in the neutral case its expected absorption
time is `meanAbsorptionTime x`.

Sources: M. Kimura, "On the probability of fixation of mutant genes in a population",
Genetics 47 (1962) 713–719; M. Kimura and T. Ohta, "The average number of generations until
fixation of a mutant gene in a finite population", Genetics 61 (1969) 763–771;
S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence* (1986),
ch. 4, 8 and 10; S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes* (1981),
ch. 15; W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed. (2004), ch. 4.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcessWanted

open MeasureTheory Filter Topology
open scoped NNReal

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator kimuraFixation
  meanAbsorptionTime)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `X` solves the **martingale problem for the Wright–Fisher diffusion** with scaled genic
selection coefficient `σ = 2Ns` (time in units of `2N` generations) with respect to the
filtration `ℱ` and the measure `μ`: `X` takes values in `[0, 1]`, has continuous paths, is
adapted to `ℱ`, and for every `C²` function `f` the process
`f (X t) - f (X 0) - ∫₀ᵗ generator σ f (X s) ds` is an `ℱ`-martingale. -/
def IsWrightFisherSolution (σ : ℝ) (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t ω, X t ω ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ ω, Continuous fun t => X t ω) ∧
    StronglyAdapted ℱ X ∧
    ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
      Martingale (fun t ω => f (X t ω) - f (X 0 ω) -
        ∫ s in (0 : ℝ)..(t : ℝ), generator σ f (X (Real.toNNReal s) ω)) ℱ μ

/-- The absorption time of a `[0, 1]`-valued path: the first time it is at `0` or `1`
(the infimum of the empty set is `0` in `ℝ≥0`; the path is absorbed almost surely, see
`ae_exists_absorbed`). -/
noncomputable def absorptionTime (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t | X t ω = 0 ∨ X t ω = 1}

/-- **Absorption in finite time.** A solution of the Wright–Fisher martingale problem is
almost surely absorbed: from some time on it is constantly `0` or constantly `1`.

Source: Ethier & Kurtz (1986), ch. 10; Karlin & Taylor (1981), ch. 15. -/
theorem_wanted ae_exists_absorbed {σ : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution σ ℱ μ X) :
    ∀ᵐ ω ∂μ, ∃ t₀ : ℝ≥0, (∀ t ≥ t₀, X t ω = 0) ∨ (∀ t ≥ t₀, X t ω = 1)

/-- **Kimura's fixation probability, process form.** For a solution of the Wright–Fisher
martingale problem with scaled selection coefficient `σ = 2Ns` started at frequency `x`, the
probability that the allele is eventually fixed is `(1 - e^{-2σx}) / (1 - e^{-2σ})` (`x` when
`σ = 0`).

Source: Kimura (1962); Ewens (2004), ch. 4. -/
theorem_wanted measureReal_fixation {σ x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution σ ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 1} = kimuraFixation σ x

/-- **Kimura–Ohta mean absorption time, process form.** For a solution of the neutral
Wright–Fisher martingale problem started at frequency `x`, the expected time to loss or
fixation, in units of `2N` generations, is `-2 (x log x + (1 - x) log (1 - x))`.

Source: Kimura & Ohta (1969); Ewens (2004), ch. 4. -/
theorem_wanted integral_absorptionTime {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    Integrable (fun ω => (absorptionTime X ω : ℝ)) μ ∧
      ∫ ω, (absorptionTime X ω : ℝ) ∂μ = meanAbsorptionTime x

end MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcessWanted
