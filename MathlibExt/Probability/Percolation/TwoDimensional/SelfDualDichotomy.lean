/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.KestenHalf
public import MathlibExt.Probability.Percolation.RSW.SelfDuality

/-!
# Self-dual events at `p = 1/2` and the quarter-turn rotation of configurations

At `p = 1/2` the Bernoulli product measure is invariant under any edge permutation and under
complementation, so an event `H` exchanged with its complement by such a map has probability
exactly `1/2` (`StatMech.Universality.half_crossingProb_of_selfDual_dichotomy`). This file adds
the quarter-turn rotation of configurations, proves that it preserves `halfMeasure`, and states
the balance `ℙ(H) = 1/2` for families of such events.

## Main definitions

* `StatMech.TwoDim.kdi_rotConfig`: the configuration rotated by a quarter turn,
  `(kdi_rotConfig ω) e = ω (crossEdge.symm e)`.

## Main results

* `StatMech.TwoDim.kdi_rotConfig_measurePreserving`: the rotation preserves `halfMeasure`.
* `StatMech.TwoDim.kdi_crossing_balance_family`: events with `Hᶜ = (R ∘ dualConfig)⁻¹' H` for a
  measure-preserving `R` have probability `1/2`.

## Implementation notes

`kdi_rotConfig ∘ dualConfig` sends `ω` to `e ↦ ¬ ω (-e)` (complement composed with the half-turn
`x ↦ -x`), not geometric crossing duality. The half-turn fixes no nearest-neighbour edge, so
there is a configuration `ω₀` with `ω₀ e = ¬ ω₀ (-e)` on every nearest-neighbour edge. For an
event `H` determined only by these edges, `Hᶜ = (kdi_rotConfig ∘ dualConfig)⁻¹' H` would imply
`ω₀ ∈ H ↔ ω₀ ∈ Hᶜ`. Thus this rotation/complement dichotomy is not a crossing API. This is an
informal obstruction, not a Lean theorem here. The test module checks a concrete single-bond
counterexample and a valid inverse-rotation witness for the retained general-`R` result.
-/

@[expose] public section

open MeasureTheory Set Filter Topology SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality

/-- The configuration rotated by a quarter turn about the origin:
`(kdi_rotConfig ω) e = ω (crossEdge.symm e)`. -/
noncomputable def kdi_rotConfig :
    ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) crossEdge

/-- The quarter-turn rotation of configurations is measurable. -/
theorem kdi_measurable_rotConfig : Measurable kdi_rotConfig :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) crossEdge).measurable

/-- The quarter-turn rotation preserves the Bernoulli(1/2) product measure. -/
theorem kdi_map_rotConfig :
    Measure.map kdi_rotConfig halfMeasure = halfMeasure := by
  rw [kdi_rotConfig, halfMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one) crossEdge

/-- The quarter-turn rotation is measure preserving for `halfMeasure`. -/
theorem kdi_rotConfig_measurePreserving :
    MeasurePreserving kdi_rotConfig halfMeasure halfMeasure :=
  ⟨kdi_measurable_rotConfig, kdi_map_rotConfig⟩

/-- Family version of `StatMech.Universality.half_crossingProb_of_selfDual_dichotomy`: if each
`boxFam n` is exchanged with its complement by `R ∘ dualConfig` for a measure-preserving `R`,
then every `boxFam n` has `halfMeasure`-probability `1/2`. -/
theorem kdi_crossing_balance_family
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n)) :
    ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2 := fun n =>
  half_crossingProb_of_selfDual_dichotomy (hHm n) hRmeas hRpres (hdich n)

end TwoDim

end StatMech
