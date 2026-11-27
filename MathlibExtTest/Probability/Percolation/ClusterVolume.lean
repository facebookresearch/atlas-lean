/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Theta

@[expose] public section

open MeasureTheory StatMech StatMech.Lattice StatMech.Percolation
open scoped NNReal

namespace MathlibExtTest.Probability.Percolation.ClusterVolume

/-- The cluster of the origin always has at least one site, so `ℙ_p(|C(0)| ≥ 1) = 1`. This is why
`MathlibExt.Probability.Percolation.ClusterVolumeDecayWanted.cluster_volume_exp_decay` carries a
prefactor `C`: without it the bound `≤ e^{-c}` at `n = 1` would fail. -/
example (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        {ω | ((1 : ℕ) : ℕ∞) ≤ (cluster d ω (origin d)).encard} = 1 := by
  have huniv : {ω : ConfigSpace (Sym2 (Site d)) |
      ((1 : ℕ) : ℕ∞) ≤ (cluster d ω (origin d)).encard} = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, Nat.cast_one,
      Set.one_le_encard_iff_nonempty]
    exact ⟨origin d, connected_refl ω (origin d)⟩
  rw [huniv, probReal_univ]

/-- The prefactor form is consistent at `n = 1`: with `C = e^c` the bound `C e^{-c n}` equals `1`
there. -/
example (c : ℝ) : Real.exp c * Real.exp (-c * (1 : ℕ)) = 1 := by
  rw [← Real.exp_add]; simp

end MathlibExtTest.Probability.Percolation.ClusterVolume
