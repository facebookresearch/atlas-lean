/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.PengCentralLimitTheorem
import MathlibExtTest.Probability.SublinearExpectationSpace

open Filter Topology Finset
open MathlibExt.Probability.SublinearExpectation
open MathlibExtTest.Probability.SublinearExpectationSpace

namespace MathlibExtTest.Probability.PengCentralLimitTheorem

private def X (i : ℕ) (b : Bool) : ℝ := if b then (i : ℝ) + 1 else 0

-- At zero variance the sample variables may differ away from the support. The limiting
-- variable may also live on a different space. Both Dirac expectations see only zero.
example {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    Tendsto (fun n : ℕ ↦ (dirac false).E (fun b ↦ φ ((∑ i ∈ range n, X i b) / Real.sqrt n)))
      atTop (𝓝 (φ 0)) := by
  have hξ : (dirac (0 : ℝ)).IsGNormal id :=
    ⟨Set.mem_univ _, id, Set.mem_univ _, fun _ _ ↦ rfl, dirac_indepFrom 0 _ _,
      fun _ _ _ _ g _ ↦ by simp [dirac]⟩
  exact PengLimitTheoremsWanted.clt (dirac false) X (fun _ ↦ Set.mem_univ _)
    (fun _ _ _ ↦ rfl) (fun _ ↦ dirac_indepFrom false _ _) rfl (by simp [dirac, X])
    (dirac (0 : ℝ)) id hξ rfl rfl hφ

end MathlibExtTest.Probability.PengCentralLimitTheorem
