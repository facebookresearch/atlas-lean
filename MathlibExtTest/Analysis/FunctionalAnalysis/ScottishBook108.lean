/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook108
import MathlibExt.Analysis.Normed.Lp.SchauderBasis

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook108Wanted.Tests

open MathlibExt.Analysis.Normed.Lp.SchauderBasis
open Filter Topology

-- A bundled basis supplies the unique ordered expansion required by the predicate.
private theorem isBasis_of_bundled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : SchauderBasis ℝ E) : IsSchauderBasis b := by
  intro x
  refine ⟨fun i => b.coord i x, ?_, ?_⟩
  · simpa only [SchauderBasis.proj_apply] using b.tendsto_proj x
  · intro a ha
    funext i
    have h := ((b.coord i).continuous.tendsto x).comp ha
    apply tendsto_nhds_unique _ h
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with N hN
    simp [map_sum, b.ortho, Pi.single_apply, Finset.mem_range.mpr hN]

-- Deleting the first unit vector from real ℓ² forces the theorem to supply a different basis.
example : ∃ b : ℕ → lp (fun _ : ℕ => ℝ) 2, IsSchauderBasis b ∧
    ∀ n, b n ≠ lp.single 2 0 (1 : ℝ) := by
  let E := lp (fun _ : ℕ => ℝ) 2
  let b : SchauderBasis ℝ E := lpSchauderBasis (by norm_num)
  have : Nontrivial E := nontrivial_of_ne _ _ (b.linearIndependent.ne_zero 0)
  have h := (krein_basis_in_dense_set E ⟨b, isBasis_of_bundled b⟩).1
  exact h _ (dense_compl_singleton (b 0))

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook108Wanted.Tests
