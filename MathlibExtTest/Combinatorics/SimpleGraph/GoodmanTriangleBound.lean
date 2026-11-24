/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound
import Mathlib.Tactic.NormNum

/-!
# Tests for Goodman's triangle bound

The bound is instantiated on concrete graphs: it is tight for `K₄` (`6 · (24 - 16) = 48 =
3 · 4 · 4`), and the four-cycle shows that the *induced-density* form
`T / C(n, 3) ≥ ρ (2 ρ - 1)` with `ρ = m / C(n, 2)` fails for finite graphs (it only holds in the
limit), which is why the finite statements use `n ^ 2` and `n ^ 3` normalisations.
-/

open Finset MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound

namespace MathlibExtTest.Combinatorics.SimpleGraph.GoodmanTriangleBound

/-- The four-cycle `0 - 1 - 2 - 3 - 0`, as the complete bipartite graph between even and odd
vertices of `Fin 4`. -/
def fourCycle : SimpleGraph (Fin 4) where
  Adj i j := (i.val + j.val) % 2 = 1
  symm := ⟨fun i j h => by simpa [Nat.add_comm] using h⟩
  loopless := ⟨fun i h => by omega⟩

instance : DecidableRel fourCycle.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val + j.val) % 2 = 1))

example : #fourCycle.edgeFinset = 4 := by decide

example : #(fourCycle.cliqueFinset 3) = 0 := by decide

/-- Goodman's bound on the four-cycle: `4 · (16 - 16) = 0 ≤ 0`. -/
example : (#fourCycle.edgeFinset : ℤ) * (4 * #fourCycle.edgeFinset - Fintype.card (Fin 4) ^ 2) ≤
    3 * Fintype.card (Fin 4) * #(fourCycle.cliqueFinset 3) :=
  goodman fourCycle

/-- The naive finite induced-density form fails on the four-cycle: `ρ = 4 / 6`, so
`ρ (2 ρ - 1) = 2 / 9 > 0 = T / C(4, 3)`. -/
example :
    ¬ ((((#fourCycle.edgeFinset : ℕ) : ℚ) / (Nat.choose 4 2)) *
        (2 * (((#fourCycle.edgeFinset : ℕ) : ℚ) / (Nat.choose 4 2)) - 1) ≤
      ((#(fourCycle.cliqueFinset 3) : ℕ) : ℚ) / (Nat.choose 4 3)) := by
  have h1 : #fourCycle.edgeFinset = 4 := by decide
  have h2 : #(fourCycle.cliqueFinset 3) = 0 := by decide
  rw [h1, h2]
  norm_num [Nat.choose]

/-- Mantel's bound on the four-cycle is attained: `4 · 4 = 16 = 4 ^ 2`. -/
example : 4 * #fourCycle.edgeFinset ≤ Fintype.card (Fin 4) ^ 2 :=
  four_mul_card_edgeFinset_le_sq_of_cliqueFree_three fourCycle
    (fourCycle.cliqueFinset_eq_empty_iff.mp (card_eq_zero.mp (by decide)))

/-- Ordered triangles of `K₄`: `6 · 4 = 24`. -/
example : #(orderedTriangles (⊤ : SimpleGraph (Fin 4))) = 24 := by decide

example : #(orderedTriangles (⊤ : SimpleGraph (Fin 4))) =
    6 * #((⊤ : SimpleGraph (Fin 4)).cliqueFinset 3) :=
  card_orderedTriangles_eq_six_mul _

/-- Goodman's bound is tight for `K₄`: both sides equal `48`. -/
example : (#(⊤ : SimpleGraph (Fin 4)).edgeFinset : ℤ) *
      (4 * #(⊤ : SimpleGraph (Fin 4)).edgeFinset - Fintype.card (Fin 4) ^ 2) = 48 ∧
    (3 * Fintype.card (Fin 4) * #((⊤ : SimpleGraph (Fin 4)).cliqueFinset 3) : ℤ) = 48 := by
  have he : #(⊤ : SimpleGraph (Fin 4)).edgeFinset = 6 := by decide
  have ht : #((⊤ : SimpleGraph (Fin 4)).cliqueFinset 3) = 4 := by decide
  rw [he, ht]
  simp

end MathlibExtTest.Combinatorics.SimpleGraph.GoodmanTriangleBound
