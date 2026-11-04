/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Closed walks are at least twice as long as any distance they span

A closed walk through two vertices `a` and `b` splits into a walk from `a` to `b` and a walk back,
each at least as long as the graph distance `G.dist a b`. Hence the closed walk has length at
least `2 * G.dist a b`; in particular this holds for cycles.

## Main results

* `StatMech.Lattice.walk_split_dist`: a closed walk through `a` and `b` has length at least
  `2 * G.dist a b`.

See also `StatMech.Lattice.closedWalk_length_ge_two_l1dist`, the same bound for closed walks in
subgraphs of `ℤ²` with the `ℓ¹` distance in place of the graph distance.
-/

@[expose] public section

open SimpleGraph SimpleGraph.Walk

namespace StatMech.Lattice

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u a b : V}

omit [DecidableEq V] in
/-- A closed walk visiting `a` and `b` has length at least `2 * G.dist a b`: rotating it to start
at `a` and splitting at `b` gives two walks between `a` and `b`. -/
theorem walk_split_dist (p : G.Walk u u) (ha : a ∈ p.support) (hb : b ∈ p.support) :
    2 * G.dist a b ≤ p.length := by
  classical
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

end StatMech.Lattice
