/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.STT
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice

/-!
# Law of the rotated complement configuration

`StatMech.Lattice.dualConfig ω` is the configuration on `ℤ²` in which an edge is open exactly when
its preimage under the quarter turn is closed in `ω`. It is the planar dual configuration
transported back to the primal lattice by a rotation (not the dual configuration itself: the
rotation sends edges to edges, not to the dual edges crossing them). This file computes its law:
under the Bernoulli product measure `ℙ_p` it is `ℙ_{1-p}`, so `ℙ_{1/2}` is invariant, and
`p = 1/2` is the only self-dual density.

## Main results

* `StatMech.Universality.map_dualConfig`: `dualConfig` pushes `ℙ_p` to `ℙ_{1-p}`.
* `StatMech.Universality.bernoulliProductMeasure_selfDual_half`: `ℙ_{1/2}` is
  `dualConfig`-invariant.
* `StatMech.Universality.selfDual_density_iff`: `1 - p = p ↔ p = 1/2`.
* `StatMech.Universality.map_dualConfig_dualConfig`: applying `dualConfig` twice preserves `ℙ_p`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice

/-- `dualConfig` is negation of all coordinates after reindexing by the quarter turn of edges. -/
theorem dualConfig_eq_comp :
    (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      = (fun η e => !(η e)) ∘ (Equiv.piCongrLeft (fun _ => Bool) crossEdge) := by
  funext ω e
  simp only [Function.comp_apply, dualConfig]
  rw [Equiv.piCongrLeft_apply]
  simp

/-- Negating every coordinate of a configuration is measurable. -/
theorem measurable_complement :
    Measurable (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) := by
  fun_prop

/-- Reindexing a configuration by the quarter turn of edges is measurable. -/
theorem measurable_reindex :
    Measurable
      (Equiv.piCongrLeft (fun _ => Bool) (crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2))) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) crossEdge).measurable

/-- Negating every coordinate pushes `ℙ_p` to `ℙ_{1-p}`. -/
theorem map_complement (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e))
        (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure (1 - p) tsub_le_self := by
  unfold bernoulliProductMeasure
  rw [Measure.infinitePi_map_pi (μ := fun _ : Sym2 (Site 2) => bernoulliMeasure p hp)
      (f := fun _ : Sym2 (Site 2) => (fun b : Bool => !b)) (fun _ => measurable_of_countable _)]
  congr 1
  funext e
  exact bernoulliMeasure_map_not p hp

/-- `ℙ_p` is invariant under reindexing by the quarter turn of edges. -/
theorem map_reindex (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (Equiv.piCongrLeft (fun _ => Bool) crossEdge)
        (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure p hp := by
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure p hp) crossEdge

/-- `dualConfig` pushes `ℙ_p` to `ℙ_{1-p}`. -/
theorem map_dualConfig (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map dualConfig (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure (1 - p) tsub_le_self := by
  rw [dualConfig_eq_comp,
    ← Measure.map_map measurable_complement measurable_reindex,
    map_reindex p hp, map_complement p hp]

/-- The law of `dualConfig` under `ℙ_p` is a probability measure. -/
instance isProbabilityMeasure_map_dualConfig (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (Measure.map dualConfig (bernoulliProductMeasure p hp)) := by
  rw [map_dualConfig p hp]; infer_instance

/-- The only self-dual density in `[0, 1]` is `1/2`. -/
theorem selfDual_density_iff (p : ℝ≥0) (hp : p ≤ 1) : 1 - p = p ↔ p = 2⁻¹ := by
  constructor
  · intro h
    apply NNReal.coe_injective
    have hr : (1 : ℝ) - (p : ℝ) = (p : ℝ) := by
      have := congrArg NNReal.toReal h
      rwa [NNReal.coe_sub hp, NNReal.coe_one] at this
    push_cast
    linarith
  · intro h
    subst h
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by norm_num)]
    push_cast
    norm_num

/-- Real form of `selfDual_density_iff`. -/
theorem selfDual_density_iff_real (p : ℝ) : 1 - p = p ↔ p = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- `ℙ_{1/2}` is invariant under `dualConfig`. -/
theorem bernoulliProductMeasure_selfDual_half :
    Measure.map dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := by
  rw [map_dualConfig (2⁻¹ : ℝ≥0) half_le_one]
  congr 1
  exact one_sub_half

/-- `1/2` is the unique self-dual density, and `ℙ_{1/2}` is `dualConfig`-invariant. -/
theorem selfDual_point_unique (p : ℝ≥0) (hp : p ≤ 1) :
    (1 - p = p ↔ p = 2⁻¹) ∧
      Measure.map dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
        = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one :=
  ⟨selfDual_density_iff p hp, bernoulliProductMeasure_selfDual_half⟩

/-- Applying `dualConfig` twice preserves `ℙ_p` (it is the half-turn of the configuration). -/
theorem map_dualConfig_dualConfig (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map dualConfig (Measure.map dualConfig (bernoulliProductMeasure p hp))
      = bernoulliProductMeasure p hp := by
  rw [map_dualConfig p hp, map_dualConfig (1 - p) tsub_le_self]
  congr 1
  apply NNReal.coe_injective
  rw [NNReal.coe_sub tsub_le_self, NNReal.coe_sub hp, NNReal.coe_one]
  ring

end Universality

end StatMech
