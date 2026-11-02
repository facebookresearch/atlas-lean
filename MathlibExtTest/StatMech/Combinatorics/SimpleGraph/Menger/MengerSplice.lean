/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Menger.MengerSplice
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Menger.MengerSplice`

* `mgs_append_isPath` for two one-edge paths `0 — 1 — 2` in the path graph on `Fin 3`.
* `mgs_spliced_isPath` for a one-path family with junction set `{1}`.
-/

@[expose] public section

open StatMech.Combinatorics

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Menger.MengerSplice

theorem adj01 : (SimpleGraph.pathGraph 3).Adj 0 1 := by
  simp [SimpleGraph.pathGraph_adj]

theorem adj12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by
  simp [SimpleGraph.pathGraph_adj]

/-- The edge `0 — 1`. -/
def p : (SimpleGraph.pathGraph 3).Walk 0 1 := .cons adj01 .nil

/-- The edge `1 — 2`. -/
def q : (SimpleGraph.pathGraph 3).Walk 1 2 := .cons adj12 .nil

theorem p_isPath : p.IsPath := by simp [p]

theorem q_isPath : q.IsPath := by simp [q]

theorem meet (x : Fin 3) (hp : x ∈ p.support) (hq : x ∈ q.support) : x = 1 := by
  simp only [p, q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with h | h <;> simp_all

example : (p.append q).IsPath := mgs_append_isPath p_isPath q_isPath meet

example : (mgs_spliced (ι := Unit) (fun _ => p) (fun _ => q) ()).IsPath :=
  mgs_spliced_isPath (S := {1}) (fun _ => p) (fun _ => q) (fun _ => p_isPath)
    (fun _ => q_isPath) (fun _ _ x hp hq => meet x hp hq)
    (fun _ _ _ hx => hx) ()

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Menger.MengerSplice
