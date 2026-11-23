/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Gibbs

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Gibbs`

On the single edge `⊤ : SimpleGraph (Fin 2)`:
* `spin` and `bond` take the values `±1`;
* `hamiltonian` of the all-plus configuration is `-1 - 2h` and of a configuration with opposite
  spins is `1`;
* at infinite temperature (`β = 0`) the partition function `isingZ` is the number of
  configurations, `4`, and `isingProb` is uniform, `1/4`;
* at `β = 1`, `h = 0` the aligned configuration is more likely than the anti-aligned one;
* `isingPMF` is a probability mass function whose values are the Gibbs probabilities.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Gibbs

open _root_.StatMech _root_.StatMech.Ising

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- The all-plus configuration on two sites. -/
def plus : ConfigSpace (Fin 2) := fun _ => true

/-- The configuration with spin `+1` at `0` and `-1` at `1`. -/
def mixed : ConfigSpace (Fin 2) := fun i => decide (i = 0)

-- The spin of a plus site is `1` and of a minus site is `-1`.
example : spin mixed 0 = 1 ∧ spin mixed 1 = -1 := by
  simp [spin, mixed]

-- The bond of an anti-aligned edge is `-1`.
example : bond mixed s(0, 1) = -1 := by
  simp [bond_mk, spin, mixed]

/-- The edge set of the single edge is `{s(0, 1)}`. -/
lemma edgeFinset_edge : edge.edgeFinset = {s(0, 1)} := by
  decide

-- The energy of the all-plus configuration is `-1 - 2h` (one satisfied bond, two aligned spins).
example (h : ℝ) : hamiltonian edge h plus = -1 - 2 * h := by
  rw [hamiltonian, edgeFinset_edge]
  simp [plus, spin]
  ring

-- The energy of the anti-aligned configuration is `1`: one frustrated bond, zero magnetization.
example (h : ℝ) : hamiltonian edge h mixed = 1 := by
  rw [hamiltonian, edgeFinset_edge]
  simp [mixed, spin]

-- At `β = 0` the partition function counts the `2 ^ 2 = 4` configurations.
example (h : ℝ) : isingZ edge 0 h = 4 := by
  simp [isingZ, isingWeight]

-- At `β = 0` the Gibbs distribution is uniform.
example (h : ℝ) (s : ConfigSpace (Fin 2)) : isingProb edge 0 h s = 1 / 4 := by
  simp [isingProb, isingZ, isingWeight]

-- At `β = 1`, `h = 0` the ferromagnet prefers the aligned configuration.
example : isingProb edge 1 0 mixed < isingProb edge 1 0 plus := by
  unfold isingProb
  apply div_lt_div_of_pos_right _ (isingZ_pos edge 1 0)
  simp only [isingWeight, hamiltonian, edgeFinset_edge, Finset.sum_singleton, bond_mk]
  apply Real.exp_lt_exp.mpr
  simp [spin, plus, mixed]

-- `isingPMF` is the Gibbs distribution, read as a `PMF`.
example (β h : ℝ) (s : ConfigSpace (Fin 2)) :
    (isingPMF edge β h s).toReal = isingProb edge β h s := by
  simp [ENNReal.toReal_ofReal (isingProb_nonneg edge β h s)]

end PhyslibExtTest.CondensedMatter.IsingModel.Gibbs
