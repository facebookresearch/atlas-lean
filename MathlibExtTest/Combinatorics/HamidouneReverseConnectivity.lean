/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HamidouneReverseConnectivity
import Mathlib.Tactic.FinCases

open MathlibExt.Combinatorics.HamidouneReverseConnectivityAIMCombinatoricsProblem191Wanted

-- The direct path and the path through 1 share both endpoints.
example : HasInternallyDisjointPaths (⟨(· < ·)⟩ : Digraph ℕ) 2 0 2 := by
  let paths (i : Fin 2) : List ℕ := if i = 0 then [0, 2] else [0, 1, 2]
  refine ⟨paths, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [paths, IsDirectedPath]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [paths, internalVertices]

-- A chain with a repeated endpoint fails the path predicate, even when every arc exists.
example : ¬ IsDirectedPath (⊤ : Digraph Bool) [false, true, false] := by
  simp [IsDirectedPath]

-- Specialize the refutation to the first admissible degree.
example : ¬ (∀ (V : Type) [Finite V] [Nonempty V] (D : Digraph V),
    (∀ v : V, ¬ D.Adj v v) → (∀ v : V, 3 ≤ {w | D.Adj v w}.ncard) →
    (∀ v : V, 3 ≤ {u | D.Adj u v}.ncard) →
    ∃ x y : V, D.Adj x y ∧ HasInternallyDisjointPaths D 3 y x) :=
  fun h ↦ hamidouneSomeRAtLeastThree_refuted ⟨3, le_rfl, h⟩
