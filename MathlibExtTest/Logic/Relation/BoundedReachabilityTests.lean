/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Relation.BoundedReachability

/-!
# Tests for bounded reachability

On `Fin 4` with the directed path `0 → 1 → 2` and vertex `3` isolated, given by a Boolean
adjacency function: one- and two-step rounds, edge direction, agreement of the final round with
`Relation.transGenFin`, and both directions of `Relation.exists_mem_reachWithinFin_iff`, including
an unreachable vertex.
-/

@[expose] public section

namespace Relation.BoundedReachabilityTests

/-- The directed path `0 → 1 → 2` on `Fin 4`, with vertex `3` isolated. -/
def pathAdj (u v : Fin 4) : Bool := (u = 0 && v = 1) || (u = 1 && v = 2)

/-- The edge relation of `pathAdj`. -/
abbrev path (u v : Fin 4) : Prop := pathAdj u v = true

/-- The start vertex is reachable in zero steps. -/
example : reachWithinFin path 0 0 = {0} := by decide

/-- One step reaches exactly the out-neighbour of the start. -/
example : reachWithinFin path 0 1 = {0, 1} := by decide

/-- Two steps reach the end of the path. -/
example : reachWithinFin path 0 2 = {0, 1, 2} := by decide

/-- The end of the path is two steps away, so it is not in round `1`. -/
example : (2 : Fin 4) ∉ reachWithinFin path 0 1 := by decide

/-- Edges are followed only forwards: from `1` the start `0` is never reached. -/
example : reachWithinFin path 1 3 = {1, 2} := by decide

/-- After three rounds the start together with its transitive closure is reached. -/
example : reachWithinFin path 0 3 = insert 0 (transGenFin path 0) := by decide

/-- Every round from `0` stays inside `{0, 1, 2}`. -/
theorem reachWithinFin_path_subset (k : ℕ) : reachWithinFin path 0 k ⊆ {0, 1, 2} := by
  induction k with
  | zero => decide
  | succ k ih =>
      intro t ht
      rcases mem_reachWithinFin_succ.mp ht with ht | ⟨u, hu, hadj⟩
      · exact ih ht
      · have hu' : u = 0 ∨ u = 1 ∨ u = 2 := by simpa using ih hu
        clear ht hu ih
        simp only [Finset.mem_insert, Finset.mem_singleton]
        revert u t
        decide

/-- The characterization gives a two-step path from `0` to `2`. -/
example : ReflTransGen path 0 2 := exists_mem_reachWithinFin_iff.mp ⟨2, by decide⟩

/-- The isolated vertex `3` is not reachable from `0`. -/
example : ¬ ReflTransGen path 0 3 := by
  rw [← exists_mem_reachWithinFin_iff]
  rintro ⟨k, hk⟩
  have h := reachWithinFin_path_subset k hk
  simp at h

end Relation.BoundedReachabilityTests

end
