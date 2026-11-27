/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`lean/ComparatorChallenges/GaussianReplacement.lean` (openai/math,
revision `3344da59991ed94f9ba711217b29c1d760badfa6`): the statement of `actualRowRefinement`.
No copyright notice is stated for this source file at that revision.
Licensed under the Apache License, Version 2.0 (see `lean/LICENSE` in openai/math).
Authors: OpenAI (project attribution in `lean/formalization.yaml`).
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Gaussian row relative entropy and deterministic message refinement -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace InformationTheory

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Row relative entropy under deterministic message refinement.** For natural `d` and `m`,
let `P` be the joint probability law of a signal `S` on the Euclidean unit sphere in dimension
`d`, a message `W`, and `m` Euclidean rows `X`. The original and extra message spaces are countable
with measurable singletons. Append the measurable deterministic value `e(S,W)` to `W` to obtain
`P'`. If `(W,e(S,W))` has finite Shannon entropy in nats, relative entropy is unchanged when each
actual law is compared with its signal–message marginal times the law of `m` independent standard
Gaussian rows. The actual rows need not have a Gaussian marginal or be independent of `(S,W)`.
The equality is in the extended nonnegative reals and does not assert finiteness.

Source: [GaussianReplacement.lean, actualRowRefinement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L457-L466).
-/
theorem gaussianRowKL_messageRefinement {d m : ℕ} {W E : Type*}
    [MeasurableSpace W] [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × W) ×
      (Fin m → EuclideanSpace ℝ (Fin d)))) [IsProbabilityMeasure P]
    (e : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × W → E) (he : Measurable e) :
    let P' := P.map (fun z => ((z.1.1, (z.1.2, e z.1)), z.2))
    let π := P'.map (fun z => z.1.2)
    let γ := Measure.pi (fun _ : Fin m => stdGaussian (EuclideanSpace ℝ (Fin d)))
    (∫⁻ v, ENNReal.ofReal (-Real.log (π {v}).toReal) ∂π) ≠ ∞ →
      klDiv P' (P'.fst.prod γ) = klDiv P (P.fst.prod γ) := by
  intro P' π γ _
  let f₀ := fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × W =>
    (z.1, (z.2, e z))
  let f := Prod.map f₀ (id : (Fin m → EuclideanSpace ℝ (Fin d)) → _)
  let g := Prod.map (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × (W × E) =>
    (z.1, z.2.1)) (id : (Fin m → EuclideanSpace ℝ (Fin d)) → _)
  have hf₀ : Measurable f₀ := measurable_fst.prodMk (measurable_snd.prodMk he)
  have hf : Measurable f := hf₀.prodMap measurable_id
  have hg : Measurable g :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMap measurable_id
  have hm : (P.map f).fst = P.fst.map f₀ := by
    simp only [Measure.fst, Measure.map_map measurable_fst hf, Measure.map_map hf₀ measurable_fst]
    rfl
  have hγ : IsProbabilityMeasure γ := by dsimp [γ]; infer_instance
  change klDiv (P.map f) ((P.map f).fst.prod γ) = klDiv P (P.fst.prod γ)
  rw [hm, ← Measure.map_id (μ := γ), Measure.map_prod_map _ _ hf₀ measurable_id]
  rw [Measure.map_id]
  apply le_antisymm (klDiv_map_le _ _ hf)
  have h := klDiv_map_le (P.map f) ((P.fst.prod γ).map f) hg
  simpa only [Measure.map_map hg hf, show g ∘ f = id from rfl, Measure.map_id] using h

end InformationTheory
