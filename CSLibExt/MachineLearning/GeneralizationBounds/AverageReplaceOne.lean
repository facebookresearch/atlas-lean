/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.Stability
public import Mathlib.Probability.UniformOn

/-!
# On-average replace-one stability

This is the fixed-sample-size form of on-average replace-one stability, with an independent
seed to cover randomized learners.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CSLibExt.MachineLearning.GeneralizationBounds

/-- **On-average replace-one stability.** Fix a positive sample size `m`, a real-valued
loss `L`, a learner `A` and a probability law `ρ` on its seeds. For each data probability
law `ν`, draw a sample `S` of `m` i.i.d. examples, a fresh example `z'` from `ν`, a uniform
coordinate `i`, and a seed `r` from `ρ`, independently. The learner is on-average
replace-one stable at `ε` if, for every `ν` for which both loss terms are integrable under
this product law, the expected signed difference
`L (A (Function.update S i z') r) (S i) - L (A S r) (S i)` is at most `ε`.
Both runs use the same seed and both losses are evaluated at the original `S i`.

Source: Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to
Algorithms*, §13.2, Definition 13.3 and the right-hand side of Eq. (13.6). The book states
the definition without seeds, with a decreasing rate across sample sizes. This predicate
is the bound at one positive size, with an explicit extension to randomized learners. -/
def IsOnAverageReplaceOneStable {𝒵 H R : Type*} [MeasurableSpace 𝒵] [MeasurableSpace R]
    {m : ℕ} [NeZero m] (L : H → 𝒵 → ℝ) (A : (Fin m → 𝒵) → R → H)
    (ρ : Measure R) [IsProbabilityMeasure ρ] (ε : ℝ) : Prop :=
  ∀ (ν : Measure 𝒵) [IsProbabilityMeasure ν],
    let μ := (Measure.pi fun _ : Fin m => ν).prod
      (ν.prod ((uniformOn (Set.univ : Set (Fin m))).prod ρ))
    let replaced : (Fin m → 𝒵) × 𝒵 × Fin m × R → ℝ := fun (S, z', i, r) =>
      L (A (Function.update S i z') r) (S i)
    let original : (Fin m → 𝒵) × 𝒵 × Fin m × R → ℝ := fun (S, _, i, r) =>
      L (A S r) (S i)
    Integrable replaced μ → Integrable original μ →
      (∫ x, (replaced x - original x) ∂μ) ≤ ε

end CSLibExt.MachineLearning.GeneralizationBounds
