/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Fixation and absorption of the neutral Wright–Fisher martingale problem

`MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess` proves, for any
solution `X` of the Wright–Fisher martingale problem `IsWrightFisherSolution σ ℱ μ X`, that the
fixation probability is `kimuraFixation σ x` and, when `σ = 0`, that the mean absorption time
is `meanAbsorptionTime x`. This file specializes those results to the neutral case `σ = 0`,
which is the case the neutral-diffusion construction targets. The solution `X` is a hypothesis
throughout; no particular realization is assumed.

For any initial frequency `x`, the allele is eventually fixed with probability `x` and
eventually lost with probability `1 - x` (`measureReal_fixation_eq`, `measureReal_loss_eq`),
and the absorption time is integrable with mean `-2 (x log x + (1 - x) log (1 - x))`
(`integral_absorptionTime_eq`). For an interior initial frequency `x ∈ (0, 1)`, the
absorption time is almost surely positive and its mean is strictly positive
(`ae_absorptionTime_pos`, `integral_absorptionTime_pos`).

At the boundary `x ∈ {0, 1}` the path is almost surely frozen at `x` for all time
(`ae_forall_eq_zero`, `ae_forall_eq_one`) and the absorption time is almost surely `0`
(`ae_absorptionTime_eq_zero`).

## Main results

* `martingale_of_neutral`: in the neutral case the allele frequency is
  itself an `ℱ`-martingale (test function `f = id`, for which `L_0 f = 0`).
* `isWrightFisherSolution_one_sub`: the neutral problem is invariant under relabeling
  the two alleles, `X ↦ 1 - X`.
* `measureReal_fixation_eq`, `measureReal_loss_eq`, `integral_absorptionTime_eq`,
  `integral_absorptionTime_pos`, `ae_absorptionTime_pos`: interior initial frequencies.
* `ae_forall_eq_zero`, `ae_forall_eq_one`, `ae_absorptionTime_eq_zero`: boundary behaviour.

Selection (`σ ≠ 0`) is out of scope here; the general fixation formula is
`KimuraFixationProcess.measureReal_fixation`.

## References

* M. Kimura, *On the probability of fixation of mutant genes in a population*,
  Genetics 47 (1962) 713–719.
* M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene in
  a finite population*, Genetics 61 (1969) 763–771.
* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 10.
* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 4.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem

open MeasureTheory Filter Set
open scoped NNReal

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator kimuraFixation
  meanAbsorptionTime)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {x : ℝ}

/-- The neutral generator kills affine test functions; in particular `L_0 id = 0`. -/
private lemma generator_zero_id : generator 0 id = 0 := by
  funext y
  simp [generator]

/-- The neutral generator commutes with the reflection `y ↦ 1 - y`. -/
private lemma generator_zero_comp_one_sub (f : ℝ → ℝ) (y : ℝ) :
    generator 0 (fun z => f (1 - z)) y = generator 0 f (1 - y) := by
  have h1 : deriv (fun z => f (1 - z)) = fun z => -deriv f (1 - z) :=
    funext fun z => deriv_comp_const_sub f 1 z
  have h2 : deriv (fun z => -deriv f (1 - z)) y = deriv (deriv f) (1 - y) := by
    rw [show (fun z => -deriv f (1 - z)) = -(fun z => deriv f (1 - z)) from rfl, deriv.neg']
    simp only [deriv_comp_const_sub (deriv f) 1 y, neg_neg]
  simp only [generator, h1, h2, zero_mul, add_zero]
  ring

/-- Each coordinate of a solution is integrable (it is measurable and bounded by `1`). -/
private lemma integrable_apply' [IsFiniteMeasure μ] {σ : ℝ}
    (hX : IsWrightFisherSolution σ ℱ μ X) (t : ℝ≥0) : Integrable (X t) μ :=
  Integrable.of_bound ((hX.2.2.1 t).mono (ℱ.le t)).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      have h := hX.1 t ω
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h.1, h.2])

/-- **The neutral allele frequency is a martingale.** For a solution of the neutral
Wright–Fisher martingale problem, `X` itself is an `ℱ`-martingale: apply the martingale
property to `f = id`, for which `L_0 f = 0`.

Source: Ewens (2004), ch. 4; Ethier & Kurtz (1986), ch. 10. -/
theorem martingale_of_neutral [IsFiniteMeasure μ] (hX : IsWrightFisherSolution 0 ℱ μ X) :
    Martingale X ℱ μ := by
  have hM := hX.2.2.2 id contDiff_id
  simp only [generator_zero_id, Pi.zero_apply, intervalIntegral.integral_zero, sub_zero,
    id] at hM
  have hC : Martingale (fun _ => X 0) ℱ μ :=
    martingale_const_fun ℱ μ (hX.2.2.1 0) (integrable_apply' hX 0)
  convert hM.add hC using 1
  funext t ω
  simp

/-- **Allele relabeling.** If `X` solves the neutral Wright–Fisher martingale problem then so
does `1 - X`, the frequency of the other allele: `L_0` commutes with `y ↦ 1 - y`.

Source: Ewens (2004), ch. 4 (symmetry of the neutral diffusion). -/
theorem isWrightFisherSolution_one_sub (hX : IsWrightFisherSolution 0 ℱ μ X) :
    IsWrightFisherSolution 0 ℱ μ (fun t ω => 1 - X t ω) := by
  refine ⟨fun t ω => ?_, fun ω => continuous_const.sub (hX.2.1 ω),
    fun t => stronglyMeasurable_const.sub (hX.2.2.1 t), fun f hf => ?_⟩
  · have h := hX.1 t ω
    constructor <;> linarith [h.1, h.2]
  · have hg : ContDiff ℝ 2 (fun z => f (1 - z)) := hf.comp (contDiff_const.sub contDiff_id)
    simpa only [generator_zero_comp_one_sub] using hX.2.2.2 _ hg

/-- In the neutral case the mean allele frequency is constant: `E[X t] = x`. -/
theorem integral_apply_eq [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) (t : ℝ≥0) : ∫ ω, X t ω ∂μ = x := by
  have h := (martingale_of_neutral hX).setIntegral_eq (zero_le (a := t)) MeasurableSet.univ
  simp only [setIntegral_univ] at h
  rw [← h, integral_congr_ae hX0]
  simp

/-- A nonnegative process with continuous paths whose mean vanishes at every time is almost
surely identically zero. -/
private lemma ae_forall_eq_zero_of_integral {Y : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Y t ω)
    (hnn : ∀ t ω, 0 ≤ Y t ω) (hi : ∀ t, Integrable (Y t) μ) (h0 : ∀ t, ∫ ω, Y t ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∀ t, Y t ω = 0 := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hpt : ∀ᵐ ω ∂μ, ∀ n, Y (u n) ω = 0 := ae_all_iff.2 fun n =>
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (hnn (u n))) (hi (u n))).1 (h0 (u n))
  filter_upwards [hpt] with ω hω t
  have := Continuous.ext_on hu (hc ω) continuous_const (by rintro _ ⟨n, rfl⟩; exact hω n)
  exact congrFun this t

/-- **Boundary `x = 0`.** A neutral solution started at `0` stays at `0` for all time,
almost surely: the nonnegative martingale `X` has mean `0` at every time. -/
theorem ae_forall_eq_zero [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0) : ∀ᵐ ω ∂μ, ∀ t, X t ω = 0 :=
  ae_forall_eq_zero_of_integral hX.2.1 (fun t ω => (hX.1 t ω).1) (integrable_apply' hX)
    (integral_apply_eq hX hX0)

/-- **Boundary `x = 1`.** A neutral solution started at `1` stays at `1` for all time,
almost surely (apply `ae_forall_eq_zero` to `1 - X`). -/
theorem ae_forall_eq_one [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = 1) : ∀ᵐ ω ∂μ, ∀ t, X t ω = 1 := by
  have h := ae_forall_eq_zero (isWrightFisherSolution_one_sub hX)
    (hX0.mono fun ω hω => by simp [hω])
  filter_upwards [h] with ω hω t
  linarith [hω t]

/-- **Neutral fixation probability.** A neutral allele at initial frequency `x` is eventually
fixed with probability `x`.

Source: Kimura (1962) with `s = 0`; Ewens (2004), ch. 4. -/
theorem measureReal_fixation_eq [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 1} = x :=
  (KimuraFixationProcess.measureReal_fixation hX hX0).trans (Diffusion.kimuraFixation_neutral x)

/-- **Neutral loss probability.** A neutral allele at initial frequency `x` is eventually lost
with probability `1 - x` (fixation of the other allele, via `isWrightFisherSolution_one_sub`). -/
theorem measureReal_loss_eq [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 0} = 1 - x := by
  have h := measureReal_fixation_eq (isWrightFisherSolution_one_sub hX) (x := 1 - x)
    (hX0.mono fun ω hω => by simp [hω])
  simpa only [sub_eq_self, show ∀ a : ℝ, 1 - a = 1 ↔ a = 0 from fun a => by
    constructor <;> intro h <;> linarith] using h

/-- **Neutral mean absorption time (Kimura–Ohta).** For a neutral solution started at `x`, the
absorption time is integrable and its mean, in units of `2N` generations, is
`-2 (x log x + (1 - x) log (1 - x))`. This is the unfolded form of
`KimuraFixationProcess.integral_absorptionTime`, with `meanAbsorptionTime` expanded; it adds no
new content.

Source: Kimura & Ohta (1969); Ewens (2004), ch. 4. -/
theorem integral_absorptionTime_eq [IsProbabilityMeasure μ]
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    Integrable (fun ω => (absorptionTime X ω : ℝ)) μ ∧
      ∫ ω, (absorptionTime X ω : ℝ) ∂μ =
        -2 * (x * Real.log x + (1 - x) * Real.log (1 - x)) :=
  KimuraFixationProcess.integral_absorptionTime hX hX0

/-- From an interior initial frequency `x ∈ (0, 1)` the mean absorption time is strictly
positive. -/
theorem integral_absorptionTime_pos [IsProbabilityMeasure μ]
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < ∫ ω, (absorptionTime X ω : ℝ) ∂μ := by
  rw [(integral_absorptionTime_eq hX hX0).2]
  have h1 : x * Real.log x < 0 := mul_neg_of_pos_of_neg hx.1 (Real.log_neg hx.1 hx.2)
  have h2 : (1 - x) * Real.log (1 - x) < 0 :=
    mul_neg_of_pos_of_neg (by linarith [hx.2]) (Real.log_neg (by linarith [hx.2])
      (by linarith [hx.1]))
  linarith

/-- From an interior initial frequency `x ∈ (0, 1)` the absorption time is almost surely
positive: the path is absorbed (`ae_exists_absorbed`), the set of absorbed times is closed by
continuity, and it does not contain `0`. -/
theorem ae_absorptionTime_pos [IsProbabilityMeasure μ] (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂μ, 0 < absorptionTime X ω := by
  filter_upwards [hX0, KimuraFixationProcess.ae_exists_absorbed hX] with ω h0 ⟨t₀, ht₀⟩
  have hcl : IsClosed {t | X t ω = 0 ∨ X t ω = 1} :=
    (isClosed_eq (hX.2.1 ω) continuous_const).union (isClosed_eq (hX.2.1 ω) continuous_const)
  have hne : {t | X t ω = 0 ∨ X t ω = 1}.Nonempty := by
    rcases ht₀ with h | h
    · exact ⟨t₀, Or.inl (h t₀ le_rfl)⟩
    · exact ⟨t₀, Or.inr (h t₀ le_rfl)⟩
  have hmem := hcl.csInf_mem hne (OrderBot.bddBelow _)
  refine pos_iff_ne_zero.2 fun hτ => ?_
  rw [show sInf {t | X t ω = 0 ∨ X t ω = 1} = absorptionTime X ω from rfl, hτ] at hmem
  rcases hmem with h | h <;> rw [h0] at h
  · exact hx.1.ne' h
  · exact hx.2.ne h

/-- **Boundary absorption time.** Started at `0` or `1`, the absorption time is almost
surely `0`. -/
theorem ae_absorptionTime_eq_zero (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) (hx : x = 0 ∨ x = 1) :
    ∀ᵐ ω ∂μ, absorptionTime X ω = 0 := by
  filter_upwards [hX0] with ω h0
  exact le_antisymm (csInf_le (OrderBot.bddBelow _) (show X 0 ω = 0 ∨ X 0 ω = 1 from h0 ▸ hx))
    zero_le

end MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
