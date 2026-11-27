/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.EdmondsKarpDistances
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Non-vacuity tests for the Edmonds–Karp distance-monotonicity lemmas. -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EdmondsKarpDistancesTests

open EdmondsKarp Relation

/-- The successor relation on `ℕ`: the chain `[0, 1, 2]` is a shortest chain from `0` to `2`. -/
private def succRel (a b : ℕ) : Prop := b = a + 1

/-- A relation adding the reverses of the steps of `[0, 1, 2]`. -/
private def withReverse (a b : ℕ) : Prop := b = a + 1 ∨ (a = b + 1 ∧ a ≤ 2)

private theorem chain012 : [0, 1, 2].IsChainFromTo succRel 0 2 :=
  ⟨by simp [succRel], by simp, rfl, rfl⟩

private theorem succRel_min (k : ℕ) (h : RelatesInSteps succRel 0 2 k) : 2 ≤ k := by
  have := h.apply_le_apply_add id (fun a b hab => by simp [succRel] at hab; simp [hab])
  simpa using this

private theorem withReverse_cases (a b : ℕ) (h : withReverse a b) :
    succRel a b ∨ (b, a) ∈ pathEdges [0, 1, 2] := by
  rcases h with h | ⟨rfl, h⟩
  · exact Or.inl h
  · right
    have hb : b ≤ 1 := by omega
    interval_cases b <;> simp [pathEdges]

/-- A detour `0 → 1 → 0 → 1` of length `3` through a reversed step is replaced by a direct walk
of length at most `3`; the reversed step really is used. -/
example : RelatesWithinSteps succRel 0 1 3 := by
  have e01 : withReverse 0 1 := Or.inl rfl
  have e10 : withReverse 1 0 := Or.inr ⟨rfl, by norm_num⟩
  have hw : RelatesInSteps withReverse 0 1 3 :=
    RelatesInSteps.tail _ _ _ _ (RelatesInSteps.tail _ _ _ _ (RelatesInSteps.single e01) e10) e01
  exact relatesWithinSteps_source_of_shortest chain012 rfl succRel_min withReverse_cases hw

example : RelatesWithinSteps succRel 1 2 3 := by
  have e12 : withReverse 1 2 := Or.inl rfl
  have e21 : withReverse 2 1 := Or.inr ⟨rfl, by norm_num⟩
  have hw : RelatesInSteps withReverse 1 2 3 :=
    RelatesInSteps.tail _ _ _ _ (RelatesInSteps.tail _ _ _ _ (RelatesInSteps.single e12) e21) e12
  exact relatesWithinSteps_sink_of_shortest chain012 rfl succRel_min withReverse_cases hw

private def onePathCapacity : Fin 3 → Fin 3 → ℕ
  | 0, 1 => 3
  | 1, 2 => 3
  | _, _ => 0

/-- Saturating the path `0 → 1 → 2` creates the reverse residual arc `1 → 0`, which was not a
residual arc before: the second alternative of Proposition 2 occurs. -/
example :
    (residualGraph onePathCapacity (augment (zeroFlow 3) [0, 1, 2] 3)).Edge 1 0 ∧
      ¬ (residualGraph onePathCapacity (zeroFlow 3)).Edge 1 0 ∧
      ((0 : Fin 3), (1 : Fin 3)) ∈ pathEdges [(0 : Fin 3), 1, 2] := by
  refine ⟨?_, ?_, by simp [pathEdges]⟩
  · rw [residualGraph_edge_iff]
    decide
  · rw [residualGraph_edge_iff]
    decide

example (u v : Fin 3)
    (h : (residualGraph onePathCapacity (augment (zeroFlow 3) [0, 1, 2] 3)).Edge u v) :
    (residualGraph onePathCapacity (zeroFlow 3)).Edge u v ∨ (v, u) ∈ pathEdges [0, 1, 2] :=
  residualGraph_edge_augment _ _ _ (amount := 3) (by norm_num) h

/-- The step lemmas apply to the algorithm's own `step`. -/
example {u : Fin 3} {k : ℕ}
    (hw : (residualGraph onePathCapacity (step onePathCapacity 0 2 (zeroFlow 3))).Walk k 0 u) :
    RelatesWithinSteps (residualGraph onePathCapacity (zeroFlow 3)).Edge 0 u k :=
  walk_step_source _ _ _ _ hw

end Cslib.Algorithms.Lean.EdmondsKarpDistancesTests
