/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Theta
public import MathlibExt.Probability.Percolation.PcNontrivial

/-!
# Tests for `MathlibExt.Probability.Percolation.Theta`

Tests the definitions `StatMech.Percolation.theta`, `percolationEvent`, `subcriticalSet` and
`pc`: `0 ≤ θ ≤ 1`; `θ_2(0) = 0` and `θ_2(1/5) = 0` (via `theta_eq_zero_of_lt` from `PcNontrivial`);
in dimension `0` the lattice is a point, so `percolationEvent 0 = ∅`, `θ_0 ≡ 0` and `p_c(0) = 1`;
and `cluster_eq_gcluster` at the origin. `θ_d(1) = 1` is tested with `SharpnessUnconditional`.
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.Theta

-- Range of `θ`.
example (hp : (1 / 2 : ℝ≥0) ≤ 1) : 0 ≤ theta 2 (1 / 2) hp ∧ theta 2 (1 / 2) hp ≤ 1 :=
  ⟨theta_nonneg _ _ _, theta_le_one _ _ _⟩

-- `θ_2(0) = 0`: with all edges closed the origin does not percolate.
example (h0 : (0 : ℝ≥0) ≤ 1) : theta 2 0 h0 = 0 :=
  theta_eq_zero_of_lt two_pos 0 h0 (by simp)

-- `θ_2(1/5) = 0`, since `2d · p = 4/5 < 1`.
example (hp : (1 / 5 : ℝ≥0) ≤ 1) : theta 2 (1 / 5) hp = 0 :=
  theta_eq_zero_of_lt two_pos _ hp (by push_cast; norm_num)

-- In dimension `0` every cluster is finite, so the percolation event is empty.
theorem percolationEvent_zero : percolationEvent 0 = ∅ := by
  ext ω
  simp only [mem_percolationEvent, Set.mem_empty_iff_false, iff_false, Set.not_infinite]
  exact Set.toFinite _

example (p : ℝ≥0) (hp : p ≤ 1) : theta 0 p hp = 0 := by
  simp [theta, percolationEvent_zero]

-- `p_c(0) = 1`: every density is subcritical in dimension `0`.
example : pc 0 = 1 := by
  have hmem : ∀ p : ℝ≥0, p ≤ 1 → p ∈ subcriticalSet 0 := fun p hp =>
    ⟨hp, by simp [theta, percolationEvent_zero]⟩
  refine le_antisymm (csSup_le ⟨0, hmem 0 zero_le_one⟩ fun p hp => hp.1) ?_
  exact le_csSup subcriticalSet_bddAbove (hmem 1 le_rfl)

-- The lattice cluster is the graph-percolation cluster on `hypercubicLattice d`.
example (ω : ConfigSpace (Sym2 (Site 2))) :
    cluster 2 ω (origin 2) =
      MathlibExt.Probability.ProductBondPercolation.gcluster (hypercubicLattice 2) ω (origin 2) :=
  cluster_eq_gcluster ω (origin 2)

end MathlibExtTest.StatMech.Probability.Percolation.Theta
