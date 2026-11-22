/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBody

@[expose] public section

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

/-! Non-vacuity checks for the sandwich of convex sets. -/

/-- The characteristic vector of the stable set `{0, 2}` of the path `0 - 1 - 2` lies in the
theta body and in QSTAB. -/
example : charVec ({0, 2} : Finset (Fin 3)) ∈
    th (SimpleGraph.fromRel fun i j : Fin 3 => i.val + 1 = j.val) := by
  apply charVec_mem_th
  intro u hu v hv huv
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all [SimpleGraph.fromRel_adj]

/-- The all-`1/2` vector on a triangle is not in QSTAB, hence not in the theta body. -/
example : (fun _ : Fin 3 => (1 / 2 : ℝ)) ∉ th (⊤ : SimpleGraph (Fin 3)) := by
  intro h
  have h' := (th_subset_qstab _ h).2 Finset.univ (by simp)
  norm_num at h'

example : (0 : Fin 4 → ℝ) ∈ th (⊥ : SimpleGraph (Fin 4)) := by
  apply stab_subset_th
  apply subset_convexHull
  exact ⟨∅, by simp, by ext v; simp [charVec]⟩
