/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.Reachability

@[expose] public section

namespace MathlibExtTest.Complexity.Reachability

open MathlibExt.Complexity.Reachability

/-- The directed path `0 → 1 → 2`, with vertex `3` isolated. -/
def pathAdj (u v : Fin 4) : Bool := (u = 0 && v = 1) || (u = 1 && v = 2)

/-- The start vertex is reachable in zero steps. -/
example : reachFrom pathAdj 0 0 = {0} := by decide

/-- One step reaches exactly the out-neighbour of the start. -/
example : reachFrom pathAdj 0 1 = {0, 1} := by decide

/-- Two steps reach the end of the path. -/
example : reachFrom pathAdj 0 2 = {0, 1, 2} := by decide

/-- The end of the path is two steps away, so it is not in iterate `1`. -/
example : (2 : Fin 4) ∉ reachFrom pathAdj 0 1 := by decide

/-- Edges are followed only forwards: from `1` the start `0` is never reached. -/
example : reachFrom pathAdj 1 3 = {1, 2} := by decide

/-- Every iterate from `0` stays inside `{0, 1, 2}`. -/
theorem reachFrom_pathAdj_subset (k : ℕ) : reachFrom pathAdj 0 k ⊆ {0, 1, 2} := by
  induction k with
  | zero => decide
  | succ k ih =>
      intro t ht
      rcases (mem_reachFrom_succ pathAdj 0 t k).mp ht with ht | ⟨u, hu, hadj⟩
      · exact ih ht
      · have hu' : u = 0 ∨ u = 1 ∨ u = 2 := by simpa using ih hu
        clear ht hu ih
        simp only [Finset.mem_insert, Finset.mem_singleton]
        revert u t
        decide

/-- The public characterization gives a two-step path from `0` to `2`. -/
example : Relation.ReflTransGen (fun a b => pathAdj a b = true) 0 2 :=
  (exists_mem_reachFrom_iff pathAdj 0 2).mp ⟨2, by decide⟩

/-- The isolated vertex `3` is not reachable from `0`. -/
example : ¬ Relation.ReflTransGen (fun a b => pathAdj a b = true) 0 3 := by
  rw [← exists_mem_reachFrom_iff]
  rintro ⟨k, hk⟩
  have h := reachFrom_pathAdj_subset k hk
  simp at h

end MathlibExtTest.Complexity.Reachability

end
