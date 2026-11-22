/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Data-processing inequality for mutual information

`measureMutualInformation μ` is the divergence of a joint law `μ` of `(X, Y)` from the product of
its marginals, in bits. This file derives the data-processing inequality for it from Mathlib's
data-processing inequality for the Kullback–Leibler divergence (`klDiv_comp_right_le`,
`klDiv_map_le`).

A Markov chain `X → Y → Z` is modeled by a joint law `μ` of `(X, Y)` and a Markov kernel
`κ : Y → Z` (a channel) that produces `Z` from `Y` alone. The joint law of `(X, Z)` is then
`(Kernel.id ∥ₖ κ) ∘ₘ μ`: keep `X`, pass `Y` through `κ`.

## Main results

* `measureMutualInformation_map_swap`: `I(Y; X) = I(X; Y)`.
* `measureMutualInformation_comp_le` (**data-processing inequality**): for a Markov chain
  `X → Y → Z`, `I(X; Z) ≤ I(X; Y)`.
* `measureMutualInformation_map_le`: `I(X; g(Y)) ≤ I(X; Y)` for a measurable `g`.

The bound `I(X; Z) ≤ I(Y; Z)` on the other side of the chain needs the reversed chain
`Z → Y → X`, which in general needs a disintegration of `μ`; for finite alphabets it is
`finiteMutualInformation_le_right_of_markov` in
`MathlibExt.InformationTheory.ConditionalMutualInformation`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
  §2.8 (data-processing inequality).
-/

@[expose] public section

namespace InformationTheory

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- **Symmetry of mutual information**: `I(Y; X) = I(X; Y)`. -/
theorem measureMutualInformation_map_swap (μ : ProbabilityMeasure (X × Y)) :
    measureMutualInformation (μ.map Prod.swap) =
      measureMutualInformation μ := by
  unfold measureMutualInformation
  simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
  set m : Measure (X × Y) := (μ : Measure (X × Y))
  have h1 : (m.map Prod.swap).map Prod.fst = m.map Prod.snd := by
    rw [Measure.map_map measurable_fst measurable_swap]; rfl
  have h2 : (m.map Prod.swap).map Prod.snd = m.map Prod.fst := by
    rw [Measure.map_map measurable_snd measurable_swap]; rfl
  rw [h1, h2, ← Measure.prod_swap]
  congr 1
  apply le_antisymm (klDiv_map_le _ _ measurable_swap)
  have := klDiv_map_le (m.map Prod.swap) (((m.map Prod.fst).prod (m.map Prod.snd)).map Prod.swap)
    measurable_swap
  rwa [Measure.map_map measurable_swap measurable_swap, Measure.map_map measurable_swap
    measurable_swap, Prod.swap_swap_eq, Measure.map_id, Measure.map_id] at this

/-- The first marginal of `(Kernel.id ∥ₖ κ) ∘ₘ μ` is that of `μ`. -/
private theorem map_fst_parallelComp (μ : Measure (X × Y)) (κ : Kernel Y Z) [IsMarkovKernel κ] :
    ((Kernel.id ∥ₖ κ) ∘ₘ μ).map Prod.fst = μ.map Prod.fst := by
  rw [Measure.map_comp _ _ measurable_fst, ← Measure.deterministic_comp_eq_map measurable_fst]
  congr 1
  ext z s hs
  rw [Kernel.map_apply _ measurable_fst, Kernel.parallelComp_apply, Kernel.id_apply,
    Measure.map_fst_prod, Kernel.deterministic_apply]
  simp

/-- The second marginal of `(Kernel.id ∥ₖ κ) ∘ₘ μ` is `κ` applied to that of `μ`. -/
private theorem map_snd_parallelComp (μ : Measure (X × Y)) (κ : Kernel Y Z) [IsMarkovKernel κ] :
    ((Kernel.id ∥ₖ κ) ∘ₘ μ).map Prod.snd = κ ∘ₘ (μ.map Prod.snd) := by
  rw [Measure.map_comp _ _ measurable_snd, ← Measure.deterministic_comp_eq_map measurable_snd,
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
  congr 1
  ext z s hs
  rw [Kernel.map_apply _ measurable_snd, Kernel.parallelComp_apply, Kernel.id_apply,
    Measure.map_snd_prod, Kernel.comap_apply]
  simp

/-- **Data-processing inequality**: if `Z` is produced from `Y` by a channel `κ` that does not see
`X` (a Markov chain `X → Y → Z`), then `I(X; Z) ≤ I(X; Y)`. The joint law of `(X, Z)` is
`(Kernel.id ∥ₖ κ) ∘ₘ μ`. -/
theorem measureMutualInformation_comp_le (μ : ProbabilityMeasure (X × Y)) (κ : Kernel Y Z)
    [IsMarkovKernel κ] :
    measureMutualInformation
        (⟨(Kernel.id ∥ₖ κ) ∘ₘ (μ : Measure (X × Y)), inferInstance⟩ :
          ProbabilityMeasure (X × Z)) ≤
      measureMutualInformation μ := by
  unfold measureMutualInformation
  simp only [ProbabilityMeasure.coe_mk]
  rw [map_fst_parallelComp, map_snd_parallelComp, Measure.prod_comp_right]
  exact ENNReal.div_le_div_right (klDiv_comp_right_le _ _ _) _

/-- **Processing cannot increase information**: `I(X; g(Y)) ≤ I(X; Y)` for a measurable `g`. -/
theorem measureMutualInformation_map_le (μ : ProbabilityMeasure (X × Y)) {g : Y → Z}
    (hg : Measurable g) :
    measureMutualInformation (μ.map (Prod.map id g)) ≤
      measureMutualInformation μ := by
  have h : (μ.map (Prod.map id g) : Measure (X × Z)) =
      (Kernel.id ∥ₖ Kernel.deterministic g hg) ∘ₘ (μ : Measure (X × Y)) := by
    rw [Kernel.id, Kernel.deterministic_parallelComp_deterministic,
      Measure.deterministic_comp_eq_map]
    rfl
  have := measureMutualInformation_comp_le μ (Kernel.deterministic g hg)
  refine le_of_eq_of_le ?_ this
  congr 1
  exact ProbabilityMeasure.toMeasure_injective h

end InformationTheory
