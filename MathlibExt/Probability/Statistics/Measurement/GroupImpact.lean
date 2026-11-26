/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.LatentMoments

/-!
# Group impact under equal item curves

Two groups on one common latent scale can have different marginal
success probabilities on an item whose conditional curve is identical
in both groups: the marginal difference is exactly the latent-law
difference weighted by the common curve.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory

/-- **Group impact under equal item curves.** Two groups are placed on one
common latent scale: both latent laws `piA`, `piB` are finite PMFs on the same
state type `Z`, and each group's responses follow the latent-mixture law
`pi.bind (fun z => localIndepPMF (q z) ..)` with its own item curves
`qA`, `qB` in `[0, 1]`. If item `i` has the same conditional curve in both
groups (`qA z i = qB z i` for every latent state `z`), then the difference of
the groups' marginal success probabilities on item `i` is the latent-law
difference weighted by that common curve,
`∑ z, (piA z - piB z) * qA z i`. Equal curves therefore still allow a nonzero
marginal difference, and differing curves can still give equal marginals.
The identity needs the latent states of both groups to be the same scale
points; it says nothing about groups whose latent scales are not anchored to
each other. -/
theorem impact_difference_of_equal_curves {Z ι : Type*} [Fintype Z] [Fintype ι]
    [DecidableEq ι] (piA piB : PMF Z) (qA qB : Z → ι → ℝ)
    (hqA0 : ∀ z i, 0 ≤ qA z i) (hqA1 : ∀ z i, qA z i ≤ 1)
    (hqB0 : ∀ z i, 0 ≤ qB z i) (hqB1 : ∀ z i, qB z i ≤ 1)
    (i : ι) (hcurve : ∀ z, qA z i = qB z i) :
    ∫ x, (if x i then (1 : ℝ) else 0)
        ∂(piA.bind fun z => localIndepPMF (qA z) (hqA0 z) (hqA1 z)).toMeasure
      - ∫ x, (if x i then (1 : ℝ) else 0)
        ∂(piB.bind fun z => localIndepPMF (qB z) (hqB0 z) (hqB1 z)).toMeasure
      = ∑ z, ((piA z).toReal - (piB z).toReal) * qA z i := by
  have hA := (latentMixture_coordinate_moments piA qA hqA0 hqA1).1 i
  have hB := (latentMixture_coordinate_moments piB qB hqB0 hqB1).1 i
  rw [hA, hB]
  simp only [MathlibExt.Probability.FiniteProbability.expectation, ← hcurve]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring

end MathlibExt.Probability.Statistics.Measurement
