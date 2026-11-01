/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Concatenating paths

A generic fact about `SimpleGraph.Walk`: two paths that meet only at their common
endpoint concatenate to a path. This was previously proved in the Buneman
four-point-condition development; it is generic graph theory, so it lives here.
-/

@[expose] public section

namespace SimpleGraph.Walk

/-- Two paths that meet only at their common endpoint `m` concatenate to a path. -/
theorem isPath_append_of_isPath {V : Type*} {G : SimpleGraph V} {u m v : V}
    {p : G.Walk u m} {q : G.Walk m v} (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ a ∈ p.support, a ∈ q.support → a = m) : (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append]
  apply List.nodup_append.mpr
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro a ha b hb hab
  subst b
  have ham := hi a ha (List.mem_of_mem_tail hb)
  subst a
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hb

end SimpleGraph.Walk
