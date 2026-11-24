/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Percolation.ClusterVolumeDecay
import MathlibExt.Probability.Percolation.PcNontrivial

open MeasureTheory StatMech StatMech.Lattice StatMech.Percolation
open MathlibExt.Probability.Percolation.ClusterVolumeDecayWanted
open scoped NNReal

-- Zero density in dimension two is subcritical. Even here the volume is at least one,
-- forcing the constants supplied by the theorem to satisfy exp c ≤ C.
example : ∃ c > 0, ∃ C ≥ Real.exp c, ∀ n : ℕ,
    (bernoulliProductMeasure (E := Sym2 (Site 2)) 0 zero_le_one).real
      {ω | (n : ℕ∞) ≤ (cluster 2 ω (origin 2)).encard} ≤ C * Real.exp (-c * n) := by
  obtain ⟨c, hc, C, _, h⟩ := cluster_volume_exp_decay (d := 2) (hd := by decide)
    (p := 0) (hp := zero_le_one) (hlt := pc_pos (by decide))
  refine ⟨c, hc, C, ?_, h⟩
  have hne (ω : ConfigSpace (Sym2 (Site 2))) : (cluster 2 ω (origin 2)).Nonempty :=
    ⟨_, self_mem_cluster ω _⟩
  have h₁ : 1 ≤ C * Real.exp (-c) := by
    simpa [Set.one_le_encard_iff_nonempty, hne] using h 1
  simpa [mul_assoc, ← Real.exp_add] using mul_le_mul_of_nonneg_right h₁ (Real.exp_pos c).le
