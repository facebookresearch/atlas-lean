/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.GeneralDiffusion

/-!
# Dominance specializations of Kimura's fixation formula

Kimura's two-allele model with dominance (Kimura 1962, as formalized in
`GeneralDiffusion.lean`): genotype fitnesses `1`, `1 + h s`, `1 + s` for zero, one and two
copies of the focal allele; `c = N s` with `N` diploid individuals; time in units of `2N`
generations; infinitesimal variance `x (1 - x)` at frequency `x`; drift
`dominanceDrift c h x = 2 c x (1 - x) (h + (1 - 2h) x)`. At `h = 1 / 2` the model is genic
selection with `σ = c` (the `s` in this dominance convention is not the per-allele `s` of
genic selection).

Each statement below is a specialization of `fixationProb_dominance` — the analytic
scale-function ratio for this diffusion — to fixed parameter values: the genic (`h = 1 / 2`),
recessive (`h = 0`), dominant (`h = 1`), and neutral (`c = 0`) cases, obtained by
substituting the parameter values and simplifying the exponent.

`fixationProb` is the analytic scale-function ratio defined in `GeneralDiffusion.lean`. As in
that module, no diffusion process is constructed here (Mathlib has no stochastic differential
equations); these statements claim nothing about a constructed stochastic process beyond what
that module states.

## Main results

* `fixationProb_dominance_half`: the genic case `h = 1 / 2`.
* `fixationProb_dominance_zero_h`: the recessive case `h = 0`.
* `fixationProb_dominance_one_h`: the dominant case `h = 1`.
* `fixationProb_dominance_zero_c`: the neutral case `c = 0`.

## References

* M. Kimura, *On the probability of fixation of mutant genes in a population*, Genetics 47
  (1962) 713–719.
-/

@[expose] public section

open Real Set

open MathlibExt.Biology.PopulationGenetics.Diffusion (dominanceDrift fixationProb
  kimuraFixation)

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Genic case (`h = 1 / 2`): for `p ∈ [0, 1]` the dominance scale-function ratio is Kimura's
genic fixation formula. At `h = 1 / 2` dominance selection is genic selection with scaled
coefficient `σ = c` in the dominance convention above. -/
theorem fixationProb_dominance_half (c : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb (dominanceDrift c (1 / 2)) (fun x => x * (1 - x)) p =
      kimuraFixation c p := by
  have hdrift : dominanceDrift c (1 / 2) = fun x => c * x * (1 - x) := by
    funext x
    simp only [dominanceDrift]
    ring
  rw [hdrift]
  exact MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_wrightFisher c hp

/-- Recessive case (`h = 0`): for `p ∈ [0, 1]` the scale exponent simplifies to `-2 c x ^ 2`, so
the scale-function ratio is `(∫₀ᵖ exp (-2 c x ^ 2) dx) / (∫₀¹ exp (-2 c x ^ 2) dx)`. -/
theorem fixationProb_dominance_zero_h (c : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb (dominanceDrift c 0) (fun x => x * (1 - x)) p =
      (∫ x in (0 : ℝ)..p, exp (-2 * c * x ^ 2)) /
        ∫ x in (0 : ℝ)..1, exp (-2 * c * x ^ 2) := by
  have hdom :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_dominance c 0 hp
  rw [hdom]
  have hpt : ∀ x : ℝ, exp (-2 * c * (2 * (0 : ℝ) - 1) * x * (1 - x) - 2 * c * x)
      = exp (-2 * c * x ^ 2) := fun x => by
    congr 1
    ring
  simp only [hpt]

/-- Dominant case (`h = 1`): for `p ∈ [0, 1]` the scale exponent simplifies to
`2 c x ^ 2 - 4 c x`, so the scale-function ratio is
`(∫₀ᵖ exp (2 c x ^ 2 - 4 c x) dx) / (∫₀¹ exp (2 c x ^ 2 - 4 c x) dx)`. -/
theorem fixationProb_dominance_one_h (c : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb (dominanceDrift c 1) (fun x => x * (1 - x)) p =
      (∫ x in (0 : ℝ)..p, exp (2 * c * x ^ 2 - 4 * c * x)) /
        ∫ x in (0 : ℝ)..1, exp (2 * c * x ^ 2 - 4 * c * x) := by
  have hdom :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_dominance c 1 hp
  rw [hdom]
  have hpt : ∀ x : ℝ, exp (-2 * c * (2 * (1 : ℝ) - 1) * x * (1 - x) - 2 * c * x)
      = exp (2 * c * x ^ 2 - 4 * c * x) := fun x => by
    congr 1
    ring
  simp only [hpt]

/-- Neutral case (`c = 0`): for `p ∈ [0, 1]` the scale-function ratio is `p` for every
dominance coefficient `h` (with no selection there is nothing for dominance to act on). -/
theorem fixationProb_dominance_zero_c (h : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb (dominanceDrift 0 h) (fun x => x * (1 - x)) p = p := by
  have hdom :=
    MathlibExt.Biology.PopulationGenetics.Diffusion.fixationProb_dominance 0 h hp
  rw [hdom]
  have hpt : ∀ x : ℝ, exp (-2 * (0 : ℝ) * (2 * h - 1) * x * (1 - x) - 2 * 0 * x)
      = (1 : ℝ) := by
    intro x
    have hz : -2 * (0 : ℝ) * (2 * h - 1) * x * (1 - x) - 2 * 0 * x = 0 := by
      ring
    rw [hz, exp_zero]
  simp only [hpt]
  simp [intervalIntegral.integral_const, smul_eq_mul]

end MathlibExt.Biology.PopulationGenetics.Diffusion
