/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card

/-!
# Cache coherence at epoch boundaries

For one location, `Epoch.SWMR` restricts who can access it, while `Epoch.DataValue` checks that
its logical start value comes from the most recent completed read–write epoch. An explicit initial
value is used until there has been such an epoch. `Epoch.MatchesStart` separately checks the
values available to readers, so agreement is not built into the representation.
`Epoch.CoherentHistory` applies all three checks at every position in a finite history,
using only the epochs strictly before that position for the start-value check.

`TokenAllocation.swmr_of_validBudget` proves the permission invariant for one allocation and
its budget, including unassigned tokens. The budget is positive and at least the number of
cores, though this proof only needs positivity and conservation. `epoch_coherence` checks
only the current allocation. Its `past` is supplied by the caller: any entry with a writer
contributes its end value, without a check of that entry's SWMR or token budget. A coherent
trace with a fixed budget would require separate hypotheses on the supplied history. This
model does not specify how tokens or values move, or what happens within an epoch.

## Reference

* D. J. Sorin, M. D. Hill, and D. A. Wood, *A Primer on Memory Consistency and Cache Coherence*,
  2011, §§2.3–2.3.1.
-/

@[expose] public section

namespace CSLibExt.CacheCoherence

/-- A snapshot for one location in an epoch, with an end value if it was a read–write epoch.
The logical start value, per-core readable values, and write permissions can be inconsistent;
coherence is checked by separate predicates. -/
structure Epoch (n : ℕ) (Value : Type*) where
  /-- The logical value of the location at the start, even if nobody can read it. -/
  startValue : Value
  /-- The value available at the start to each core with read access, `none` otherwise. -/
  readValue : Fin n → Option Value
  /-- Whether a core has write access in this epoch. -/
  canWrite : Fin n → Bool
  /-- The location's end value when there is write access, whether or not it changed. -/
  endWriteValue : (∃ c, canWrite c = true) → Value

namespace Epoch

variable {n : ℕ} {Value : Type*}

/-- Either one core can both read and write and no other core can do either,
or there are no writers and any number of readers (possibly zero). -/
def SWMR (e : Epoch n Value) : Prop :=
  (∃ w, e.canWrite w = true ∧ (e.readValue w).isSome = true ∧
    ∀ c, c ≠ w → e.canWrite c = false ∧ e.readValue c = none) ∨
  (∀ c, e.canWrite c = false)

/-- The value carried into the next epoch after `past`, ordered earliest to latest.
Read-only epochs leave the carried value unchanged, including before the first write. -/
def carriedValue (initial : Value) (past : List (Epoch n Value)) : Value :=
  past.foldl (fun current e =>
    if h : ∃ c, e.canWrite c = true then e.endWriteValue h else current) initial

/-- The location starts with the end value of the last read–write epoch in the preceding
history, or the initial value if there is no such epoch. -/
def DataValue (e : Epoch n Value) (initial : Value) (past : List (Epoch n Value)) : Prop :=
  e.startValue = carriedValue initial past

/-- Every readable copy at the start of an epoch matches its logical start value. -/
def MatchesStart (e : Epoch n Value) : Prop :=
  ∀ ⦃c : Fin n⦄ ⦃v : Value⦄, e.readValue c = some v → v = e.startValue

/-- All cores with read access agree on the value available at the start of the epoch. -/
def ReadAgreement (e : Epoch n Value) : Prop :=
  ∀ ⦃a b : Fin n⦄ ⦃va vb : Value⦄,
    e.readValue a = some va → e.readValue b = some vb → va = vb

/-- Matching copies suffice for read agreement, independently of the permissions of writers. -/
theorem readAgreement_of_matchesStart {e : Epoch n Value} (h : e.MatchesStart) :
    e.ReadAgreement := by
  intro a b va vb ha hb
  exact (h ha).trans (h hb).symm

/-- With both value checks, any readable copy contains the value carried from the history. -/
theorem read_eq_carriedValue {e : Epoch n Value} {initial : Value} {past : List (Epoch n Value)}
    (hData : e.DataValue initial past) (hMatches : e.MatchesStart)
    {c : Fin n} {v : Value} (hRead : e.readValue c = some v) : v = carriedValue initial past :=
  (hMatches hRead).trans hData

/-- A finite history of snapshots for one location is coherent when every epoch satisfies
`SWMR`, starts with the value carried from exactly the epochs strictly before it, and has every
readable copy match that start value. The list is ordered earliest first: at index `i` the
preceding history is `history.take i`, excluding the current epoch and all later epochs.
Before any write this uses `initial`, even when no copy is readable. -/
def CoherentHistory (initial : Value) (history : List (Epoch n Value)) : Prop :=
  ∀ i : Fin history.length,
    let e := history[i]
    e.SWMR ∧ e.DataValue initial (history.take i.val) ∧ e.MatchesStart

/-- In a coherent history, a readable copy at any epoch contains the value carried from the
strictly preceding prefix. -/
theorem CoherentHistory.read_eq_carriedValue {initial : Value} {history : List (Epoch n Value)}
    (h : CoherentHistory initial history) (i : Fin history.length) {c : Fin n} {v : Value}
    (hRead : history[i].readValue c = some v) : v = carriedValue initial (history.take i.val) :=
  Epoch.read_eq_carriedValue (h i).2.1 (h i).2.2 hRead

end Epoch

/-- A location's token counts at an epoch boundary. Unassigned tokens grant no access. -/
structure TokenAllocation (n : ℕ) where
  /-- The number of tokens each core holds. -/
  held : Fin n → ℕ
  /-- The number of tokens held by no core. -/
  unassigned : ℕ

namespace TokenAllocation

variable {n : ℕ} {Value : Type*}

/-- The fixed budget is positive, at least the number of cores, and fully accounted for. -/
def ValidBudget (a : TokenAllocation n) (total : ℕ) : Prop :=
  0 < total ∧ n ≤ total ∧ (∑ c, a.held c) + a.unassigned = total

/-- Interpret a token allocation as permissions for an epoch. Holding a token makes the core's
copy readable; holding all tokens allows writing. Nothing here equates copies with `start`. -/
def epoch (a : TokenAllocation n) (total : ℕ) (start : Value) (copy : Fin n → Value)
    (finish : (∃ c, a.held c = total) → Value) : Epoch n Value where
  startValue := start
  readValue c := if 0 < a.held c then some (copy c) else none
  canWrite c := decide (a.held c = total)
  endWriteValue h := finish (by simpa only [decide_eq_true_eq] using h)

/-- A valid token budget enforces SWMR for arbitrary readable copies and end values. If one
core holds all tokens, any other core's holding must be zero. -/
theorem swmr_of_validBudget {a : TokenAllocation n} {total : ℕ} (h : a.ValidBudget total)
    (start : Value) (copy : Fin n → Value) (finish : (∃ c, a.held c = total) → Value) :
    (a.epoch total start copy finish).SWMR := by
  obtain ⟨hpos, -, hsum⟩ := h
  by_cases hw : ∃ c, a.held c = total
  · obtain ⟨w, hw⟩ := hw
    refine Or.inl ⟨w, by simp [epoch, hw], by simp [epoch, hw, hpos], ?_⟩
    intro c hcw
    have hpair : a.held c + a.held w ≤ ∑ i, a.held i := by
      calc
        _ = ∑ i ∈ ({c, w} : Finset (Fin n)), a.held i := (Finset.sum_pair hcw).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hz : a.held c = 0 := by omega
    simp [epoch, hz, Nat.ne_of_lt hpos]
  · exact Or.inr (fun c => by simpa [epoch] using fun hc => hw ⟨c, hc⟩)

/-- **Cache coherence at epoch boundaries.** A valid token budget rules out concurrent access
by any other core when a core can write. Separately, if the initial or last-written value is
carried forward and every readable copy matches the start value, then every reader sees that
carried value. The token permissions alone impose no equality on the copies. -/
theorem epoch_coherence {a : TokenAllocation n} {total : ℕ} (h : a.ValidBudget total)
    (start : Value) (copy : Fin n → Value) (finish : (∃ c, a.held c = total) → Value)
    (initial : Value) (past : List (Epoch n Value)) :
    let e := a.epoch total start copy finish
    e.SWMR ∧ (e.DataValue initial past → e.MatchesStart →
      e.ReadAgreement ∧ ∀ c v, e.readValue c = some v → v = Epoch.carriedValue initial past) := by
  exact ⟨swmr_of_validBudget h start copy finish, fun hData hMatches =>
    ⟨Epoch.readAgreement_of_matchesStart hMatches,
      fun _ _ hRead => Epoch.read_eq_carriedValue hData hMatches hRead⟩⟩

end TokenAllocation

end CSLibExt.CacheCoherence
