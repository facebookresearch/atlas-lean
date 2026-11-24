/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
public import Domains.Biology.PopulationGenetics.Diffusion.KimuraFixationSelection
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Allele-label symmetry of the Wright–Fisher martingale problem

This module (`Domains.Biology.PopulationGenetics.Diffusion.LabelSymmetry`) states the
allele-label symmetry of the Wright–Fisher martingale problem with selection: reflecting a
solution `X ↦ 1 - X` exchanges the roles of the two alleles, so the focal allele after
reflection is the complementary allele. Writing `g(z) = f(1 - z)` for a test function `f`,
the chain rule gives `g'(y) = -f'(1 - y)` and `g''(y) = f''(1 - y)`; hence the neutral part
of the backward generator is invariant under `y ↦ 1 - y` while the genic drift changes sign.
Transporting the martingale clause along this conjugation shows the reflected process solves
the `-σ` martingale problem on the same measurable space, filtration, and measure.
Reflection swaps the absorbing states, so the loss probability of `X` is the fixation
probability of the reflection, and the absorption time is unchanged.

Conventions are those of `Domains.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess`:
scaled genic selection coefficient `σ = 2Ns` for a diploid population of `N` individuals and
time in units of `2N` generations, with continuous `[0, 1]`-valued paths. The formula-level
symmetry `kimuraFixation_neg (σ x : ℝ) : kimuraFixation σ x = 1 - kimuraFixation (-σ) (1 - x)`
proved in `Domains.Biology.PopulationGenetics.Diffusion.KimuraFixationSelection` is quoted, not
restated. The neutral case, where reflection preserves the selection coefficient, is
`NeutralMartingaleProblem.isWrightFisherSolution_one_sub` (with loss formula
`NeutralMartingaleProblem.measureReal_loss_eq`).

The reflection stays on the same measurable space, filtration, and
measure, and no new process is constructed. What is not claimed is
uniqueness in law or equality of path laws beyond the
solution-predicate transport `IsWrightFisherSolution.one_sub` stated below.

## Main results

* `generator_neg_one_sub`: conjugating the backward generator by `y ↦ 1 - y` negates the
  selection coefficient.
* `IsWrightFisherSolution.one_sub`: the reflected process `1 - X` solves the `-σ` martingale
  problem on the same space, filtration, and measure.
* `absorptionTime_one_sub`: reflection preserves the absorption time.
* `measureReal_loss`: an allele at frequency `x` is eventually lost with probability
  `1 - kimuraFixation σ x`.

## References

* M. Kimura, *On the probability of fixation of mutant genes in a population*,
  Genetics 47 (1962) 713–719.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 4.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

open MeasureTheory
open scoped NNReal
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)

/-- Conjugation of the backward generator by allele relabeling: for an
arbitrary test function `f` and every `y`,
`generator (-σ) f (1 - y) = generator σ (fun z => f (1 - z)) y`. The neutral
part is invariant under `y ↦ 1 - y` while the genic drift changes sign. No
regularity is needed: the derivative is total (`deriv h x = 0` where `h` is not
differentiable at `x`, applied twice for the second-order term), and the identity holds for
these total derivatives; `IsWrightFisherSolution.one_sub` applies it to `C²` test functions. -/
theorem generator_neg_one_sub (σ : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    generator (-σ) f (1 - y) = generator σ (fun z => f (1 - z)) y := by
  have h1 : deriv (fun z => f (1 - z)) = fun z => -deriv f (1 - z) :=
    funext fun z => deriv_comp_const_sub f 1 z
  have h2 : deriv (fun z => -deriv f (1 - z)) y = deriv (deriv f) (1 - y) := by
    rw [show (fun z => -deriv f (1 - z)) = -(fun z => deriv f (1 - z)) from rfl,
      deriv.neg']
    simp only [deriv_comp_const_sub (deriv f) 1 y, neg_neg]
  simp only [generator, h1, h2]
  ring

/-- **Allele relabeling with selection.** If `X` solves the Wright–Fisher martingale problem
with scaled selection coefficient `σ`, then `1 - X` solves it with `-σ`, on the same
measurable space, filtration, and measure (`μ` any measure); the focal allele after reflection
is the complementary allele. No new process is constructed and no uniqueness in law is claimed.

Source: Ewens (2004), ch. 4. The neutral case is
`NeutralMartingaleProblem.isWrightFisherSolution_one_sub`. -/
theorem IsWrightFisherSolution.one_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution σ ℱ μ X) :
    IsWrightFisherSolution (-σ) ℱ μ (fun t ω => 1 - X t ω) := by
  refine ⟨fun t ω => ?_, fun ω => continuous_const.sub (hX.2.1 ω),
    fun t => stronglyMeasurable_const.sub (hX.2.2.1 t), fun f hf => ?_⟩
  · have h := hX.1 t ω
    constructor <;> linarith [h.1, h.2]
  · have hg : ContDiff ℝ 2 (fun z => f (1 - z)) := hf.comp (contDiff_const.sub contDiff_id)
    simpa only [generator_neg_one_sub σ f] using hX.2.2.2 _ hg

/-- Reflection preserves the absorption time: the first time `1 - X` is at `0` or `1` is the
first time `X` is at `1` or `0`. Stated as equality of the two `Ω → ℝ≥0` functions, for every
process `X`; both sides use `sInf ∅ = 0`, so it also holds for paths that are never absorbed. -/
theorem absorptionTime_one_sub {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} :
    absorptionTime (fun t ω => 1 - X t ω) = absorptionTime X := by
  funext ω
  simp only [absorptionTime]
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq]
  constructor <;> rintro (h | h)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

/-- **Kimura's loss probability, process form.** Under a probability measure `μ`, for a solution of
the Wright–Fisher martingale problem with scaled selection coefficient `σ = 2Ns` and `X 0 = x`
almost surely, the probability that the allele is eventually lost is `1 - kimuraFixation σ x`: the
loss probability of `X` is the fixation probability of the reflected process `1 - X`.

Source: Kimura (1962); Ewens (2004), ch. 4. -/
theorem measureReal_loss {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ x : ℝ}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution σ ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 0} = 1 - kimuraFixation σ x := by
  have h := KimuraFixationProcess.measureReal_fixation
    (IsWrightFisherSolution.one_sub hX) (x := 1 - x)
    (hX0.mono fun ω hω => by simp [hω])
  have hset : {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, (fun t ω => 1 - X t ω) t ω = 1}
      = {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> rintro ⟨t₀, ht₀⟩ <;> exact ⟨t₀, fun t ht => by linarith [ht₀ t ht]⟩
  rw [hset] at h
  exact h.trans (by linarith [kimuraFixation_neg σ x])

end MathlibExt.Biology.PopulationGenetics.Diffusion
