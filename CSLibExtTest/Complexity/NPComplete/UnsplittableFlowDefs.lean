/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UnsplittableFlowDefs

namespace MetaMathlibExt.Complexity.NPComplete.UnsplittableFlow

open MetaMathlibExt.BitstringEncoding

/-- The path `0 - 1 - 2` with unit capacities, source `0`, sinks `1` and `2` of demand `1`
each, and the bound `K`. -/
private abbrev line (K : ℕ) : UnsplittableFlowInstance :=
  (3, [(0, 1, 1), (1, 2, 1)], 0, [(1, 1), (2, 1)], K)

/-- The instance is well formed for every positive bound. -/
example : WellFormed (line 1) := by unfold WellFormed; decide

private theorem line_two_wellFormed : WellFormed (line 2) := by unfold WellFormed; decide

private theorem adj01 (K : ℕ) : (Graph (line K) : SimpleGraph (Fin 3)).Adj 0 1 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

private theorem adj12 (K : ℕ) : (Graph (line K) : SimpleGraph (Fin 3)).Adj 1 2 := by
  simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The path `0, 1`. -/
private def path01 (K : ℕ) : (Graph (line K) : SimpleGraph (Fin 3)).Path 0 1 :=
  ⟨.cons (adj01 K) .nil, by simp⟩

/-- The path `0, 1, 2`. -/
private def path012 (K : ℕ) : (Graph (line K) : SimpleGraph (Fin 3)).Path 0 2 :=
  ⟨.cons (adj01 K) (.cons (adj12 K) .nil), by simp [SimpleGraph.Walk.cons_isPath_iff]⟩

/-- With the bound `2`, routing sink `1` along `0, 1` and sink `2` along `0, 1, 2` loads the
edge `{0, 1}` with `2 ≤ 2 · 1` and the edge `{1, 2}` with `1 ≤ 2 · 1`. -/
private theorem line_two_feasible : UnsplittableFlowFeasible (line 2) := by
  intro hs ht
  refine ⟨fun k => match k with
    | 0 => path01 2
    | 1 => path012 2, ?_⟩
  decide +revert

/-- `1` is the only neighbour of `0`. -/
private theorem adj_zero (K : ℕ) :
    ∀ v : Fin 3, (Graph (line K) : SimpleGraph (Fin 3)).Adj 0 v → v = 1 := by
  intro v
  fin_cases v <;> simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- Every walk from `0` to another vertex uses the edge `{0, 1}`. -/
private theorem walk_from_zero_uses (K : ℕ) {t : Fin 3} (ht : t ≠ 0)
    (p : (Graph (line K) : SimpleGraph (Fin 3)).Walk 0 t) :
    s((0 : ℕ), (1 : ℕ)) ∈ p.edges.map (Sym2.map Fin.val) := by
  cases p with
  | nil => exact absurd rfl ht
  | cons h q =>
    obtain rfl := adj_zero K _ h
    simp

/-- With the bound `1` the instance is infeasible: both sinks must be reached through the
edge `{0, 1}`, which then carries demand `2 > 1 · 1`. Only the bound differs from the
feasible instance. -/
private theorem line_one_infeasible : ¬ UnsplittableFlowFeasible (line 1) := by
  intro h
  obtain ⟨paths, hcap⟩ := h (by decide) (fun k => by fin_cases k <;> decide)
  have h0 := walk_from_zero_uses 1 (by decide) (paths 0).1
  have h1 := walk_from_zero_uses 1 (by decide) (paths 1).1
  have hle := hcap (0, 1, 1) (by simp)
  rw [Finset.filter_true_of_mem (fun k _ => by fin_cases k; exacts [h0, h1])] at hle
  revert hle
  decide

/-- The source `5` is not one of the three vertices; otherwise this is `line 1`. -/
private abbrev badSource : UnsplittableFlowInstance :=
  (3, [(0, 1, 1), (1, 2, 1)], 5, [(1, 1), (2, 1)], 1)

/-- The sink `7` is not one of the three vertices; otherwise this is `line 1`. -/
private abbrev badSink : UnsplittableFlowInstance :=
  (3, [(0, 1, 1), (1, 2, 1)], 0, [(1, 1), (7, 1)], 1)

/-- `UnsplittableFlowFeasible` only constrains instances whose source and sinks are
vertices, so it holds for `badSource`, although the same instance with source `0` is
infeasible. -/
private theorem badSource_feasible : UnsplittableFlowFeasible badSource :=
  fun hs => absurd hs (by decide)

/-- It also holds for `badSink`. -/
private theorem badSink_feasible : UnsplittableFlowFeasible badSink :=
  fun _ ht => absurd (ht 1) (by decide)

private theorem badSource_malformed : ¬ WellFormed badSource := by unfold WellFormed; decide

private theorem badSink_malformed : ¬ WellFormed badSink := by unfold WellFormed; decide

/-- The decision problem accepts the encoding of `line 2`. -/
example : unsplittableFlowDec (bitEncode (line 2)) = true := by
  simp [unsplittableFlowDec, line_two_wellFormed, line_two_feasible]

/-- It rejects the encoding of the well-formed but infeasible `line 1`. -/
example : unsplittableFlowDec (bitEncode (line 1)) = false := by
  simp [unsplittableFlowDec, line_one_infeasible]

/-- It rejects `badSource` and `badSink`, on which `UnsplittableFlowFeasible` holds: the
decision problem, unlike the feasibility predicate alone, requires the source and the sinks
to be vertices. -/
example :
    UnsplittableFlowFeasible badSource ∧ unsplittableFlowDec (bitEncode badSource) = false ∧
      UnsplittableFlowFeasible badSink ∧ unsplittableFlowDec (bitEncode badSink) = false := by
  refine ⟨badSource_feasible, ?_, badSink_feasible, ?_⟩ <;>
    simp [unsplittableFlowDec, badSource_malformed, badSink_malformed]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : unsplittableFlowDec [true] = false := by
  have h : bitDecode (α := UnsplittableFlowInstance) [true] = none := rfl
  simp [unsplittableFlowDec, h]

end MetaMathlibExt.Complexity.NPComplete.UnsplittableFlow
