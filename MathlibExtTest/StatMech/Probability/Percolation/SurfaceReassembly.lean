/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.SurfaceReassembly
public import MathlibExt.Probability.Percolation.SharpnessTheorem

/-!
# Tests for `MathlibExt.Probability.Percolation.SurfaceReassembly`

Tests the first Duminil-Copin–Tassion item: `StatMech.Percolation.subcritical_oneStep`,
`subcritical_geometric` and `crossProb_exp_decay_of_phi_lt_one` at `d = 2`, `p = 1/9`, `S = {0}`,
`L = 1`. The hypotheses `0 ∈ S`, `S ⊆ Λ_{L-1}` and `φ_p(S) < 1` are all proved (the last from the
boundary-edge count `|∂{0}| ≤ 4`).
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.SurfaceReassembly

-- The singleton `{0}` lies in `Λ_0`.
theorem singleton_subset_box : (({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 (1 - 1) := by
  intro x hx
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
  subst hx
  rw [mem_box]; intro i; simp [origin]

-- `φ_{1/9}({0}) < 1` in `ℤ²`: at most four boundary edges, each weighted by at most `1/9`.
theorem phi_nineth_lt_one (hp : (1 / 9 : ℝ≥0) ≤ 1) : phi 2 (1 / 9) hp {origin 2} < 1 := by
  have hcard : ((boundaryEdges 2 {origin 2}).card : ℝ) ≤ 4 := by
    have := card_boundaryEdges_le (d := 2) {origin 2}
    rw [Finset.card_singleton] at this
    exact_mod_cast this
  calc phi 2 (1 / 9) hp {origin 2}
      ≤ ((1 / 9 : ℝ≥0) : ℝ) * (boundaryEdges 2 {origin 2}).card := phi_le_mul_card _ hp _
    _ ≤ ((1 / 9 : ℝ≥0) : ℝ) * 4 := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ < 1 := by push_cast; norm_num

-- The one-step recursion with `S = {0}`, `L = 1`, `k = 1`: `crossProb 2 ≤ φ · crossProb 1`.
example (hp : (1 / 9 : ℝ≥0) ≤ 1) :
    crossProb 2 (1 / 9) hp 2 ≤ phi 2 (1 / 9) hp {origin 2} * crossProb 2 (1 / 9) hp 1 := by
  simpa using subcritical_oneStep (1 / 9) hp {origin 2} (by simp) 1 le_rfl singleton_subset_box 1
    le_rfl

-- Geometric decay along multiples of `L = 1`.
example (hp : (1 / 9 : ℝ≥0) ≤ 1) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ k, crossProb 2 (1 / 9) hp (k * 1) ≤ r⁻¹ * r ^ k :=
  subcritical_geometric _ hp {origin 2} (by simp) (phi_nineth_lt_one hp) 1 le_rfl
    singleton_subset_box

-- The headline: exponential decay of the one-arm probability at `p = 1/9`, `d = 2`.
example (hp : (1 / 9 : ℝ≥0) ≤ 1) :
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 (1 / 9) hp n ≤ C * Real.exp (-c * n) :=
  crossProb_exp_decay_of_phi_lt_one _ hp {origin 2} (by simp) (phi_nineth_lt_one hp) 1 le_rfl
    singleton_subset_box

end MathlibExtTest.StatMech.Probability.Percolation.SurfaceReassembly
