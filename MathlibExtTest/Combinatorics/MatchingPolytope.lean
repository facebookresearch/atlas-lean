/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MatchingPolytope
import Mathlib.Tactic.NormNum

/-!
# Tests for the matching polytope

The empty matching gives the zero vector on every graph. On a triangle, putting weight one half
on every edge saturates the degree constraints and violates the odd-set inequality.
-/

open Finset MathlibExt.Combinatorics.MatchingPolytopeWanted

namespace MathlibExtTest.Combinatorics.MatchingPolytope

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 : G.edgeSet → ℝ) ∈ matchingPolytope G := by
  rw [matchingPolytope_eq]
  simp

private abbrev triangle := (⊤ : SimpleGraph (Fin 3))

example (v : Fin 3) :
    ∑ _e ∈ univ.filter (fun e : triangle.edgeSet => v ∈ e.val), (1 / 2 : ℝ) = 1 := by
  have hc : ∀ v : Fin 3, (univ.filter (fun e : triangle.edgeSet => v ∈ e.val)).card = 2 := by
    decide
  norm_num [hc]

example : (fun _ : triangle.edgeSet => (1 / 2 : ℝ)) ∉ matchingPolytope triangle := by
  rw [matchingPolytope_eq]
  intro hx
  have h := hx.2.2 univ (by decide)
  have hc : Fintype.card triangle.edgeSet = 3 := by decide
  have hs : univ.filter (fun e : triangle.edgeSet => e.val ∈ (univ : Finset (Fin 3)).sym2) =
      univ := by simp
  rw [hs, sum_const, card_univ, hc] at h
  norm_num at h

end MathlibExtTest.Combinatorics.MatchingPolytope
