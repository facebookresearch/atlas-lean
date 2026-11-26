/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.Connected
import MathlibExt.Topology.ScottishBook46

/-!
# Test for unicoherence of the unit sphere

The theorem applies to the real square-summable sequence space with a singleton cover member.
-/

open Set Metric
open MathlibExt.Topology.ScottishBook46Wanted

example : IsConnected
    (sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1 ∩ {lp.single 2 (0 : ℕ) (1 : ℝ)}) := by
  let E := lp (fun _ : ℕ ↦ ℝ) 2
  let S := sphere (0 : E) 1
  let x : E := lp.single 2 (0 : ℕ) (1 : ℝ)
  change IsConnected (S ∩ {x})
  have hinf : ¬ Module.Finite ℝ E := by
    intro h
    let b : HilbertBasis ℕ ℝ E := default
    exact h.not_linearIndependent_of_infinite b b.orthonormal.linearIndependent
  have hrank : 1 < Module.rank ℝ E :=
    Cardinal.one_lt_aleph0.trans_le
      (le_of_not_gt fun hlt ↦ hinf (Module.rank_lt_aleph0_iff.mp hlt))
  have hx : x ∈ S := by
    change x ∈ sphere (0 : E) 1
    rw [mem_sphere_zero_iff_norm]
    rw [show x = lp.single 2 (0 : ℕ) (1 : ℝ) from rfl, lp.norm_single (by norm_num), norm_one]
  have hsub : {x} ⊆ S := singleton_subset_iff.mpr hx
  exact sphere_in_banach_space_is_unicoherent E hinf S {x} Subset.rfl hsub
    (union_eq_left.mpr hsub) isClosed_sphere (isConnected_sphere hrank 0 zero_le_one)
    isClosed_singleton isConnected_singleton
