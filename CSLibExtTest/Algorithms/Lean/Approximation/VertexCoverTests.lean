/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.VertexCover
public meta import CSLibExt.Algorithms.Lean.Approximation.VertexCover
public meta import Mathlib.Data.Finset.Sort

/-!
# Vertex cover 2-approximation tests

Executed fixtures check the returned cover and the one-unit-per-edge cost on paths, stars, a
triangle, repeated and reversed edges, and the empty list. The path on four vertices is the tight
case: the scan returns all four vertices while `{1, 2}` covers it. Concrete graphs instantiate the
public theorems with decided hypotheses.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def check (label : String) (edges : List (Nat × Nat)) (expected : List Nat)
    (cost : Nat) : IO Unit := do
  let result := approxVertexCover edges
  let got := result.ret.sort (· ≤ ·)
  unless got == expected && result.time == cost do
    throw (IO.userError s!"{label}: got {got} with cost {result.time}")
  IO.println s!"{label}: {got}, cost {result.time}"

#eval check "no edges" [] [] 0
#eval check "single edge" [(3, 7)] [3, 7] 1
#eval check "path 0-1-2-3 (tight)" [(0, 1), (1, 2), (2, 3)] [0, 1, 2, 3] 3
#eval check "path, middle edge first" [(1, 2), (0, 1), (2, 3)] [1, 2] 3
#eval check "star centred at 0" [(0, 1), (0, 2), (0, 3)] [0, 1] 3
#eval check "triangle" [(0, 1), (1, 2), (2, 0)] [0, 1] 3
#eval check "repeated and reversed edges" [(0, 1), (1, 0), (0, 1), (2, 3)] [0, 1, 2, 3] 4
#eval check "two disjoint edges" [(0, 1), (2, 3)] [0, 1, 2, 3] 2

private def path4 : List (Fin 4 × Fin 4) := [(0, 1), (1, 2), (2, 3)]

/-- The path `0 - 1 - 2 - 3` as a Mathlib simple graph. -/
private def path4Graph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun a b => (a, b) ∈ path4

private instance : DecidableRel path4Graph.Adj := fun a b => by
  unfold path4Graph SimpleGraph.fromRel; infer_instance

private theorem path4_sound : ∀ e ∈ path4, path4Graph.Adj e.1 e.2 := by decide

private theorem path4_complete :
    ∀ ⦃u v⦄, path4Graph.Adj u v → (u, v) ∈ path4 ∨ (v, u) ∈ path4 := by decide

example : (approxVertexCover path4).ret = Finset.univ := by decide

/-- The tight instance: `{1, 2}` is a cover of half the size of the returned one. -/
example : path4Graph.IsVertexCover ({1, 2} : Set (Fin 4)) := by
  intro u v h
  revert u v
  decide

example : path4Graph.IsVertexCover ↑(approxVertexCover path4).ret ∧
    ((approxVertexCover path4).ret.card : ℕ∞) ≤ 2 * path4Graph.vertexCoverNum :=
  approxVertexCover_two_approximation path4Graph path4 path4_sound path4_complete

example : ((approxVertexCover path4).ret.card : ℕ∞) ≤ 2 * ({1, 2} : Set (Fin 4)).encard :=
  card_approxVertexCover_le_two_mul path4Graph path4 path4_sound _
    (by intro u v h; revert u v; decide)

example : ∃ A : List (Fin 4 × Fin 4), A.Sublist path4 ∧ A.Pairwise VertexDisjoint ∧
    (∀ e ∈ path4, ∃ f ∈ A, e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2) ∧
    (∀ x, x ∈ (approxVertexCover path4).ret ↔ ∃ e ∈ A, x = e.1 ∨ x = e.2) ∧
    (approxVertexCover path4).ret.card = 2 * A.length :=
  approxVertexCover_matching path4Graph path4 path4_sound

example : (approxVertexCover path4).time = 3 := by simp [path4]

universe u

example {V : Type u} [DecidableEq V] (edges : List (V × V)) :
    (approxVertexCover edges).time = edges.length := approxVertexCover_time edges

#print axioms approxVertexCover
#print axioms approxVertexCover_time
#print axioms approxVertexCover_covers
#print axioms approxVertexCover_isVertexCover
#print axioms card_approxVertexCover_le_two_mul
#print axioms approxVertexCover_two_approximation
#print axioms approxVertexCover_matching

end Cslib.Algorithms.Lean.TimeM
