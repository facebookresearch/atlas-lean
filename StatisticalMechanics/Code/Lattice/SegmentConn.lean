/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Mathlib
import Code.Lattice.HypercubicLattice

open Set

namespace StatMech

namespace Lattice

variable {d : ℕ}



theorem adj_update_succ (x : Site d) (j : Fin d) (a : ℤ) :
    (hypercubicLattice d).Adj (Function.update x j a) (Function.update x j (a + 1)) := by
  rw [hypercubicLattice_adj]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Function.update_of_ne hij]
  · intro h; exact absurd (Finset.mem_univ j) h








theorem segment_connectedWithin (S : Set (Site d)) (j : Fin d) (x : Site d) (n : ℕ)
    (hmem : ∀ t ≤ n, Function.update x j (x j + (t : ℤ)) ∈ S) :
    ((hypercubicLattice d).induce S).Reachable
      ⟨Function.update x j (x j + (0 : ℤ)), hmem 0 (Nat.zero_le n)⟩
      ⟨Function.update x j (x j + (n : ℤ)), hmem n le_rfl⟩ := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    have hm : ∀ t ≤ m, Function.update x j (x j + (t : ℤ)) ∈ S := fun t ht =>
      hmem t (ht.trans (Nat.le_succ m))
    have step : ((hypercubicLattice d).induce S).Adj
        ⟨Function.update x j (x j + (m : ℤ)), hm m le_rfl⟩
        ⟨Function.update x j (x j + ((m : ℤ) + 1)), by
          have := hmem (m + 1) le_rfl
          have he : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
          rwa [he] at this⟩ := by
      have hadj := adj_update_succ x j (x j + (m : ℤ))
      simpa [SimpleGraph.induce_adj, add_assoc] using hadj
    have hrec := (ih hm).trans (SimpleGraph.Adj.reachable step)
    
    convert hrec using 4

end Lattice

end StatMech
