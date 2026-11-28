/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.LubyMISRounds
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for Luby's maximal independent set algorithm

* With no vertex, the algorithm stops at once with the empty set.
* On the edgeless graph on three vertices one round selects every vertex.
* On the path `0 - 1 - 2 - 3 - 4` with priorities `1, 0, 2, 3, 4`, the first round selects only
  `1` and leaves `{3, 4}`; the second round selects `3` and stops with `{1, 3}`, which
  `lubyRun_maximal` certifies as a maximal independent set. On the triangle one round selects
  exactly one vertex.
* Rounds after the algorithm has stopped change nothing, and after `n` rounds no vertex remains,
  whatever the priorities (here all equal, so only the tie-breaking by index separates them).
* On the edgeless graph the probability that a vertex remains after one round is `0`; on any
  graph on three vertices it is at most `1 / 3` after `3 * ⌈log₂ 3⌉ + 1 = 7` rounds (`c = 1`).
* The key estimate and the expectation bound instantiate with the discrete measurable structure
  on the permutations.
-/

@[expose] public section

namespace Cslib.Distributed.LubyMISRoundsTests

open Cslib.Distributed.LubyMIS MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- With no vertex, no round is needed: nothing remains and the independent set is empty. -/
example (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj] : lubyRun G [] = (∅, ∅) := by
  simp [lubyRun]

/-- On the edgeless graph one round selects every vertex. -/
example : lubyRun (⊥ : SimpleGraph (Fin 3)) [![2, 0, 1]] = (Finset.univ, ∅) := by
  decide

/-- Priorities on the path `0 - 1 - 2 - 3 - 4`. -/
def prio5 : Fin 5 → ℕ := ![1, 0, 2, 3, 4]

/-- The first round on the path selects only `1`, so `0`, `1` and `2` are removed. -/
example : lubyRound (SimpleGraph.pathGraph 5) (∅, Finset.univ) prio5 = ({1}, {3, 4}) := by
  decide

/-- Two rounds on the path stop with the independent set `{1, 3}`. -/
theorem lubyRun_path5 : lubyRun (SimpleGraph.pathGraph 5) [prio5, prio5] = ({1, 3}, ∅) := by
  decide

/-- The computed set is a maximal independent set of the path. -/
example : Maximal (SimpleGraph.pathGraph 5).IsIndepSet
    (({1, 3} : Finset (Fin 5)) : Set (Fin 5)) := by
  have h := ((lubyRun_maximal (SimpleGraph.pathGraph 5) [prio5, prio5]).1
    (by rw [lubyRun_path5])).1
  rwa [lubyRun_path5] at h

/-- Rounds after the algorithm has stopped change nothing. -/
example : lubyRun (SimpleGraph.pathGraph 5) ([prio5, prio5] ++ [![0, 0, 0, 0, 0]]) =
    ({1, 3}, ∅) := by
  rw [((lubyRun_maximal (SimpleGraph.pathGraph 5) [prio5, prio5]).1
    (by rw [lubyRun_path5])).2, lubyRun_path5]

/-- On the triangle one round selects exactly the vertex of least priority. -/
example : lubyRun (⊤ : SimpleGraph (Fin 3)) [![2, 0, 1]] = ({1}, ∅) := by
  decide

/-- With all priorities equal, ties are broken by index, and after `n` rounds (here three, on the
path `0 - 1 - 2`) no vertex remains. -/
example : (lubyRun (SimpleGraph.pathGraph 3) [0, 0, 0]).2 = ∅ :=
  (lubyRun_maximal (SimpleGraph.pathGraph 3) [0, 0, 0]).2 (by simp)

/-- The run above stops with `{0, 2}`. -/
example : lubyRun (SimpleGraph.pathGraph 3) [0, 0, 0] = ({0, 2}, ∅) := by
  decide

section Probability

/-- The discrete measurable structure on the permutations of three vertices. -/
local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤

local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) := ⟨fun _ => trivial⟩

/-- On the edgeless graph some vertex remains after one round with probability `0`. -/
example : Measure.pi (fun _ : Fin (0 + 1) => uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
    {ω | (lubyRun (⊥ : SimpleGraph (Fin 3)) (List.ofFn fun t w => (ω t w : ℕ))).2.Nonempty} =
      0 := by
  refine le_antisymm ((prob_lubyRun_nonempty_le ⊥ 0).trans ?_) zero_le
  simp

/-- On any graph on three vertices, some vertex remains after `7` rounds with probability at most
`1 / 3`. -/
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    Measure.pi (fun _ : Fin ((1 + 2) * Nat.clog 2 3 + 1) =>
        uniformOn (Set.univ : Set (Equiv.Perm (Fin 3))))
      {ω | (lubyRun G (List.ofFn fun t w => (ω t w : ℕ))).2.Nonempty} ≤ (3 : ℝ≥0∞)⁻¹ := by
  simpa using prob_lubyRun_nonempty_le_inv_pow G 1

/-- `⌈log₂ 3⌉ = 2`, so the bound above is for `7` rounds. -/
example : (1 + 2) * Nat.clog 2 3 + 1 = 7 := by
  decide

/-- The key estimate on the path `0 - 1 - 2` for the edge `01`: the vertex `0` has the smallest
value among `N(0) ∪ N(1) = {0, 1, 2}` with probability at least `1 / (1 + 2)`. -/
example : ((1 + 2 : ℕ) : ℝ≥0∞)⁻¹ ≤ uniformOn Set.univ {σ : Equiv.Perm (Fin 3) |
    ∀ w ∈ (SimpleGraph.pathGraph 3).neighborFinset 0 ∩ Finset.univ ∪
      (SimpleGraph.pathGraph 3).neighborFinset 1 ∩ Finset.univ, w ≠ 0 → σ 0 < σ w} := by
  have h := inv_le_uniformOn_smallest (SimpleGraph.pathGraph 3) (R := Finset.univ)
    (Finset.mem_univ 0) (by decide : (SimpleGraph.pathGraph 3).Adj 0 1)
  have h0 : ((SimpleGraph.pathGraph 3).neighborFinset 0 ∩ Finset.univ).card = 1 := by decide
  have h1 : ((SimpleGraph.pathGraph 3).neighborFinset 1 ∩ Finset.univ).card = 2 := by decide
  rwa [h0, h1] at h

/-- On the triangle a round removes, in expectation, at least half of its three edges. -/
example : ((remainingEdges (⊤ : SimpleGraph (Fin 3)) Finset.univ).card : ℝ) / 2 ≤
    ∫ σ : Equiv.Perm (Fin 3), ((remainingEdges ⊤ Finset.univ \
      remainingEdges ⊤ (lubyRemaining ⊤ (fun w => (σ w : ℕ)) Finset.univ)).card : ℝ)
      ∂uniformOn Set.univ :=
  expected_removed_edges_ge ⊤ Finset.univ

end Probability

end Cslib.Distributed.LubyMISRoundsTests
