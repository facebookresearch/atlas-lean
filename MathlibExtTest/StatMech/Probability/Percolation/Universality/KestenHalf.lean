/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.KestenHalf

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.KestenHalf`

* The self-duality lemma `half_crossingProb_of_selfDual_dichotomy` is instantiated with a
  nontrivial self-dual event: `H = {ω | ω e₀ = true}` for one edge `e₀`, and `R` the reindexing by
  the quarter turn, for which `R ∘ dualConfig` negates every coordinate. It gives
  `ℙ_{1/2}(H) = 1/2`, so its hypotheses are satisfiable.
* `percolationProbability` agrees with `StatMech.Percolation.theta`.
* Not covered: `kesten_pc_eq_half_of_bxp` and `kesten_no_percolation_at_pc`; their inputs
  (Harris's `θ(1/2) = 0`, subcritical crossing decay, an exactly self-dual crossing family) are not
  available in Atlas.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.KestenHalf

/-- Reindexing by the quarter turn of edges: `(R η) e = η (crossEdge e)`. -/
noncomputable def R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) crossEdge.symm

theorem measurable_R : Measurable R :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) crossEdge.symm).measurable

theorem map_R : Measure.map R halfMeasure = halfMeasure := by
  unfold R halfMeasure bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one) crossEdge.symm

/-- The edge `{(0, 0), (1, 0)}`. -/
noncomputable def e₀ : Sym2 (Site 2) := s(![0, 0], ![1, 0])

/-- The event that `e₀` is open. -/
def H : Set (ConfigSpace (Sym2 (Site 2))) := (fun ω => ω e₀) ⁻¹' {true}

theorem dich : Hᶜ = (R ∘ dualConfig) ⁻¹' H := by
  ext ω
  simp [H, R, dualConfig, Equiv.piCongrLeft_apply]

example : halfMeasure.real H = 1 / 2 :=
  half_crossingProb_of_selfDual_dichotomy ((measurable_pi_apply e₀) (measurableSet_singleton _))
    measurable_R map_R dich

example (p : ℝ≥0) (hp : p ≤ 1) :
    (percolationProbability 2 p hp).toReal = StatMech.Percolation.theta 2 p hp :=
  percolationProbability_toReal 2 p hp

example (p : ℝ≥0) (hp : p ≤ 1) :
    percolationProbability 2 p hp = 0 ↔ StatMech.Percolation.theta 2 p hp = 0 :=
  percolationProbability_eq_zero_iff_theta 2 p hp

end MathlibExtTest.StatMech.Probability.Percolation.Universality.KestenHalf
