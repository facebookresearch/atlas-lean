/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.ConsistentCut
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for consistent cuts

The execution of `VectorClockTests`: `p0` has an internal event and then sends
a message, `p1` has an internal event and then receives that message, and `p0`
has another internal event. The vector timestamps are
`(1, 0), (2, 0), (0, 1), (2, 2), (3, 0)`, and the initial events are `0` and `2`.

* `{0, 2}`, the initial events, is the least cut; it is consistent, with global
  time `(1, 1)`.
* `{0, 2, 3}` is a cut but not a consistent one: it contains the receipt `3`
  but not the send `1`, and the vector-time criterion fails, as
  `C(3)(0) = 2 > 1 = C(0)(0)`.
* `{0, 1, 2, 3}` is a consistent cut, with global time `(2, 2)`, the diagonal
  of its last events' timestamps.
* `{0, 1}` is not a cut, as it misses the initial event `2` of `p1`, and neither
  is `{0, 2, 4}`, which skips the event `1` of `p0`.
-/

@[expose] public section

namespace Cslib.Distributed.ConsistentCut.Tests

open LamportClock (Event WellFormed HappensBefore)
open VectorClock

/-- The example execution. -/
def tr : List (Event (Fin 2)) :=
  [⟨0, none⟩, ⟨0, none⟩, ⟨1, none⟩, ⟨1, some 1⟩, ⟨0, none⟩]

/-- The events at the listed positions. -/
def evs (l : List ℕ) : Set (Fin tr.length) := {a | (a : ℕ) ∈ l}

theorem wellFormed_tr : WellFormed tr := by
  intro j ej i hj hr
  rcases j with _ | _ | _ | _ | _ | j <;> simp only [tr] at hj <;>
    first
    | (simp at hj; done)
    | (obtain rfl := Option.some.inj hj; simp at hr; done)
    | (obtain rfl := Option.some.inj hj; simp at hr; omega)

example : (timestamps tr).map (fun v => [v 0, v 1]) =
    [[1, 0], [2, 0], [0, 1], [2, 2], [3, 0]] := by decide

/-- The initial events form a cut. -/
theorem isCut_initial : IsCut tr (evs [0, 2]) := by
  simp only [IsCut, evs, Set.mem_ofPred_eq]
  decide

/-- A set missing the initial event of `p1` is not a cut. -/
example : ¬ IsCut tr (evs [0, 1]) := by
  simp only [IsCut, evs, Set.mem_ofPred_eq]
  decide

/-- A set that skips an earlier event of a process is not a cut. -/
example : ¬ IsCut tr (evs [0, 2, 4]) := by
  simp only [IsCut, evs, Set.mem_ofPred_eq]
  decide

theorem isCut_023 : IsCut tr (evs [0, 2, 3]) := by
  simp only [IsCut, evs, Set.mem_ofPred_eq]
  decide

theorem isCut_0123 : IsCut tr (evs [0, 1, 2, 3]) := by
  simp only [IsCut, evs, Set.mem_ofPred_eq]
  decide

/-- The cut `{0, 2, 3}` contains the receipt `3` but not the send `1`. -/
example : ¬ IsConsistentCut tr (evs [0, 2, 3]) := by
  rw [isConsistentCut_iff_recv wellFormed_tr isCut_023]
  intro h
  have := h ⟨1, by decide⟩ ⟨3, by decide⟩ (by simp [evs]) rfl
  simp [evs] at this

/-- The vector-time criterion detects the same inconsistency. -/
example : ¬ IsConsistentCut tr (evs [0, 2, 3]) := by
  rw [isConsistentCut_iff_le (c := (![0, 3] : Fin 2 → Fin 5)) isCut_023
    (by simp only [evs, Set.mem_ofPred_eq]; decide)]
  intro h
  exact absurd (h 0 1) (by decide)

theorem isConsistentCut_0123 : IsConsistentCut tr (evs [0, 1, 2, 3]) := by
  rw [isConsistentCut_iff_le (c := (![1, 3] : Fin 2 → Fin 5)) isCut_0123
    (by simp only [evs, Set.mem_ofPred_eq]; decide)]
  decide

/-- The supremum form of the criterion: for `{0, 1, 2, 3}` the supremum of the
last events' timestamps `(2, 0)` and `(2, 2)` is their diagonal `(2, 2)`, and for
`{0, 2, 3}` the supremum `(2, 2)` of `(1, 0)` and `(2, 2)` is not the diagonal
`(1, 2)`. -/
example : IsConsistentCut tr (evs [0, 1, 2, 3]) ∧ ¬ IsConsistentCut tr (evs [0, 2, 3]) := by
  rw [(isConsistentCut_iff_vectorTime (c := (![1, 3] : Fin 2 → Fin 5)) isCut_0123
      (by simp only [evs, Set.mem_ofPred_eq]; decide)).2,
    (isConsistentCut_iff_vectorTime (c := (![0, 3] : Fin 2 → Fin 5)) isCut_023
      (by simp only [evs, Set.mem_ofPred_eq]; decide)).2]
  decide

theorem isConsistentCut_initial : IsConsistentCut tr (evs [0, 2]) := by
  rw [isConsistentCut_iff_le (c := (![0, 2] : Fin 2 → Fin 5)) isCut_initial
    (by simp only [evs, Set.mem_ofPred_eq]; decide)]
  decide

/-- The global time of the consistent cut `{0, 1, 2, 3}` is `(2, 2)`, the diagonal
of the timestamps `(2, 0)` and `(2, 2)` of its last events. -/
example : globalTime tr (evs [0, 1, 2, 3]) = ![2, 2] := by
  rw [globalTime_eq_sup (c := (![1, 3] : Fin 2 → Fin 5))
    (by simp only [evs, Set.mem_ofPred_eq]; decide)]
  decide

/-- The global time of the inconsistent cut `{0, 2, 3}` is `(2, 2)`, not the
diagonal `(1, 2)`. -/
example : globalTime tr (evs [0, 2, 3]) = ![2, 2] := by
  rw [globalTime_eq_sup (c := (![0, 3] : Fin 2 → Fin 5))
    (by simp only [evs, Set.mem_ofPred_eq]; decide)]
  decide

example : ![1, 1] ∈ globalTime tr '' {C | IsConsistentCut tr C} := by
  refine ⟨(evs [0, 2]), isConsistentCut_initial, ?_⟩
  rw [globalTime_eq_sup (c := (![0, 2] : Fin 2 → Fin 5))
    (by simp only [evs, Set.mem_ofPred_eq]; decide)]
  decide

/-- The consistent cuts `{0, 2}` and `{0, 1, 2, 3}` are ordered by inclusion,
and so are their global times. -/
example : globalTime tr (evs [0, 2]) ≤ globalTime tr (evs [0, 1, 2, 3]) :=
  (subset_iff_globalTime_le isConsistentCut_initial.2 isConsistentCut_0123.2).1
    (fun a ha => by simp only [evs, Set.mem_ofPred_eq] at ha ⊢; revert a; decide)

/-- In the empty execution the empty set is a consistent cut, with global time
`0`. -/
example : IsConsistentCut ([] : List (Event (Fin 2))) ∅ ∧
    globalTime ([] : List (Event (Fin 2))) ∅ = 0 :=
  ⟨⟨⟨fun a => a.elim0, fun a => a.elim0⟩, fun a => a.elim0⟩, by simp [globalTime]; rfl⟩

/-- The main theorem applies to the example execution. -/
example : IsSublattice (globalTime tr '' {C | IsConsistentCut tr C}) :=
  (consistentCuts_lattice wellFormed_tr).2.2.2.2.1

end Cslib.Distributed.ConsistentCut.Tests
