/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph SimpleGraph.Walk

namespace StatMech.Lattice

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u a b : V}




theorem walk_split_dist (p : G.Walk u u) (ha : a ∈ p.support) (hb : b ∈ p.support) :
    2 * G.dist a b ≤ p.length := by
  
  set q : G.Walk a a := p.rotate a ha with hq
  
  have hbq : b ∈ q.support := by
    rw [hq, mem_support_rotate_iff]; exact hb
  have hlen : q.length = p.length := by rw [hq, length_rotate]
  
  have hsplit : (q.takeUntil b hbq).length + (q.dropUntil b hbq).length = q.length := by
    have := congrArg Walk.length (q.take_spec hbq)
    rwa [length_append] at this
  
  have h1 : G.dist a b ≤ (q.takeUntil b hbq).length := dist_le _
  
  have h2 : G.dist a b ≤ (q.dropUntil b hbq).length := by
    rw [dist_comm]; exact dist_le _
  
  calc 2 * G.dist a b
      = G.dist a b + G.dist a b := two_mul _
    _ ≤ (q.takeUntil b hbq).length + (q.dropUntil b hbq).length :=
        Nat.add_le_add h1 h2
    _ = q.length := hsplit
    _ = p.length := hlen



theorem IsCycle.length_ge_two_mul_dist {p : G.Walk u u} (_hc : p.IsCycle)
    (ha : a ∈ p.support) (hb : b ∈ p.support) :
    2 * G.dist a b ≤ p.length :=
  walk_split_dist p ha hb

end StatMech.Lattice
