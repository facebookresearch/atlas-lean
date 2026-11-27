/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Distributed.UnicastRound
public import CSLibExt.Computability.Distributed.VectorClock
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-!
# Worst-case dimension of causal timestamps

For each `n ≥ 2` there is a finite unicast execution of `n` processes containing the standard
example of order dimension `n`: distinct events `A i`, `B i` whose only strict comparisons are
`A i → B j` for `i ≠ j`. In an exact product clock, each `B i` is strictly below `A i` in some
coordinate, and distinct indices require distinct such coordinates. This applies even if a clock is
allowed to assign equal timestamps to different events. In particular, a scalar clock can preserve
causality without characterizing it. The ordinary vector clock with one natural-number coordinate
per process attains the bound.

The comparison is the strict product order: coordinatewise `≤` and unequal vectors. This is
not a bound on bits, on local storage, or on the dimension needed for every individual protocol;
encoding a vector in a scalar and changing the comparison is not ruled out.

## References

B. Charron-Bost, *Concerning the size of logical clocks in distributed systems*, Information
Processing Letters 39 (1991), 11–16. See R. Schwarz and F. Mattern, *Detecting Causal
Relationships in Distributed Computations: In Search of the Holy Grail*, author manuscript,
§4.3, pp. 15–16, Definition 4.2, Theorems 4.4–4.5 and Corollary 4.6, for the dimension
result and its attribution. The unicast round below is an explicit witness.
-/

namespace Cslib.Distributed.CausalClockDimension

open LamportClock UnicastRound

universe u

/-- In the crown round, process `i` sends once to every process except itself and its cyclic
successor. Local order, not a message, relates its own two markers. -/
def crownLinks (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun q => i ≠ q ∧ finRotate n i ≠ q).map fun q => (i, q)

/-- The finite `n`-process execution obtained by sending all the crown messages in one unicast
round. For `n = 2` it has no messages and consists of two disjoint chains of two events each. -/
def crown (n : ℕ) : List (Event (Fin n)) := execution (crownLinks n)

/-- The two layers of the standard example as valid positions of the execution: the left
marker `A i` is initial on process `i`; the right marker `B i` is final on its cyclic successor. -/
def marker (n : ℕ) : Fin n ⊕ Fin n → Fin (crown n).length :=
  Sum.elim (first (crownLinks n)) (last (crownLinks n)) ∘ Sum.map id (finRotate n)

/-- The `2n` marked events of the crown execution are distinct positions. -/
theorem marker_injective (n : ℕ) : Function.Injective (marker n) :=
  (markers_injective _).comp
    (Sum.map_injective.mpr ⟨Function.injective_id, (finRotate n).injective⟩)

private theorem rotate_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  match n with
  | 0 | 1 => omega
  | m + 2 => simp

/-- On its marked events, happened-before in the crown on `n ≥ 2` processes is exactly the
standard example: `A i` precedes `B j` if and only if `i ≠ j`; neither layer has any internal
comparison, and no `B` precedes any `A`. -/
theorem marker_happensBefore_iff {n : ℕ} (hn : 2 ≤ n) (x y : Fin n ⊕ Fin n) :
    HappensBefore (crown n) (marker n x) (marker n y) ↔
      match x, y with
      | .inl i, .inr j => i ≠ j
      | _, _ => False := by
  cases x with
  | inl i => cases y with
    | inl j => exact iff_false_intro (not_first_before_first _ i j)
    | inr j =>
      change HappensBefore _ (first _ i) (last _ (finRotate n j)) ↔ i ≠ j
      rw [crown, first_before_last_iff]
      have mem (p q : Fin n) : (p, q) ∈ crownLinks n ↔ p ≠ q ∧ finRotate n p ≠ q := by
        simp [crownLinks]
      rw [mem]
      constructor
      · rintro (h | ⟨-, h⟩) rfl
        · exact rotate_ne hn i h.symm
        · exact h rfl
      · intro h
        by_cases e : i = finRotate n j
        · exact Or.inl e
        · exact Or.inr ⟨e, (finRotate n).injective.ne h⟩
  | inr i => cases y with
    | inl j => exact iff_false_intro (not_last_before_first _ _ _)
    | inr j => exact iff_false_intro (not_last_before_last _ _ _)

/-- Any timestamp assignment on the valid events of the explicit `n`-process crown, `n ≥ 2`,
that preserves and reflects strict happened-before in a product of `d` copies of a linear order
has `n ≤ d`. Timestamp injectivity is not an assumption. -/
theorem dimension_le {n d : ℕ} (hn : 2 ≤ n) {α : Type*} [LinearOrder α]
    (T : Fin (crown n).length → Fin d → α)
    (exactClock : ∀ a b : Fin (crown n).length,
      HappensBefore (crown n) a b ↔ T a < T b) : n ≤ d := by
  let A (i : Fin n) := T (marker n (.inl i))
  let B (i : Fin n) := T (marker n (.inr i))
  have cross (i j : Fin n) : A i < B j ↔ i ≠ j :=
    (exactClock _ _).symm.trans (marker_happensBefore_iff hn (.inl i) (.inr j))
  have unequal (i : Fin n) : A i ≠ B i := by
    intro h
    -- Equality would transfer the incoming edge from A j to an edge within the lower layer.
    let j := finRotate n i
    have hj := (cross j i).2 (rotate_ne hn i)
    rw [← h] at hj
    exact (marker_happensBefore_iff hn (.inl j) (.inl i)).1 ((exactClock _ _).2 hj)
  have reversed (i : Fin n) : ∃ k, B i k < A i k := by
    by_contra! hle
    exact (cross i i).1 (lt_of_le_of_ne hle (unequal i)) rfl
  choose k hk using reversed
  have inj : Function.Injective k := by
    intro i j e
    by_contra h
    have h₁ := (hk i).trans_le (((cross i j).2 h).le (k i))
    have h₂ := (hk j).trans_le (((cross j i).2 (Ne.symm h)).le (k j))
    rw [e] at h₁
    exact h₁.asymm h₂
  simpa using Fintype.card_le_of_injective k inj

/-- No scalar assignment into a linear order characterizes strict happened-before on the
`n`-process crown for `n ≥ 2`, even if incomparable events may receive equal scalars. -/
theorem no_scalar_clock {n : ℕ} (hn : 2 ≤ n) {α : Type*} [LinearOrder α] :
    ¬ ∃ T : Fin (crown n).length → α,
      ∀ a b : Fin (crown n).length, HappensBefore (crown n) a b ↔ T a < T b := by
  rintro ⟨T, hT⟩
  have h := dimension_le (d := 1) hn (fun a _ => T a) fun a b => (hT a b).trans (by
    constructor
    · intro h
      exact Pi.lt_def.mpr ⟨fun _ => h.le, 0, h⟩
    · rintro h
      obtain ⟨-, k, hk⟩ := Pi.lt_def.mp h
      exact hk)
  omega

/-- For every `n ≥ 2` there is a well-formed finite execution on `n` processes in which each
send is received at most once, the ordinary `n`-coordinate vector clock characterizes strict
happened-before, and every assignment into `d` linearly ordered coordinates characterizing it
on all valid events satisfies `n ≤ d`. The comparison in both cases is the strict product order. -/
theorem exists_optimal_unicast_execution {n : ℕ} (hn : 2 ≤ n) :
    ∃ tr : List (Event (Fin n)), WellFormed tr ∧ SingleDelivery tr ∧
      (∀ a b : Fin tr.length, HappensBefore tr a b ↔
        (VectorClock.timestamps tr).getD a 0 < (VectorClock.timestamps tr).getD b 0) ∧
      ∀ (d : ℕ) (α : Type u) [LinearOrder α] (T : Fin tr.length → Fin d → α),
        (∀ a b : Fin tr.length, HappensBefore tr a b ↔ T a < T b) → n ≤ d :=
  ⟨crown n, wellFormed _, singleDelivery _,
    fun a b => VectorClock.happensBefore_iff_lt a.isLt b.isLt, fun _ _ _ => dimension_le hn⟩

end Cslib.Distributed.CausalClockDimension
